//! Built-in operators: TLA+ core and native standard-module overrides
//! (tlc-semantics.md §4, §7).
//!
//! The operator families with their own helpers live in child modules:
//! `folds` (`FoldSet`, `FoldSeq`, `FoldLeft`/`FoldRight`, `MapThenFoldSet`),
//! `bags` (`BagOfAll`, `FoldBag`) and `permutations` (`Permutations`,
//! `SetToSeqs`).

mod bags;
mod folds;
mod permutations;

use std::sync::Arc;

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;
use tlx_value::{arith, ops, order, LazySet, Sym, Value};

use crate::env::{Env, OpVal};
use crate::error::{EResult, EvalError};
use crate::eval::{as_bool, Ctx};
use crate::interp::Interp;

/// The Java methods of TLC's overrides whose failures `java_override`
/// reports (`Method.toString`).
const IS_FINITE_SET: &str = "public static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value)";
const CARDINALITY: &str = "public static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value)";
const TO_STRING: &str = "public static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value)";

/// The result of a native that TLC implements by the Java method `sig`
/// (a `MethodValue`): an error the method runs into (TLC: a
/// `TLCRuntimeException` of the value classes, not an `EvalException` of
/// the module code such as an argument error) is wrapped in
/// EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE (`MethodValue.eval`). This is
/// observable by `AssertError`, which compares messages.
fn java_override<T>(sig: &str, r: tlx_value::Result<T>) -> EResult<T> {
    r.map_err(|e| match e.kind {
        tlx_value::ValueErrorKind::General | tlx_value::ValueErrorKind::Overflow => EvalError::new(format!(
            "Attempted to apply the operator overridden by the Java method\n{sig},\nbut it produced the following error:\n{}",
            e.message()
        )),
        _ => e.into(),
    })
}

fn int(v: &Value, op: &str) -> EResult<i64> {
    match v {
        Value::Int(i) => Ok(*i),
        _ => Err(EvalError::new(format!("The argument of {op} should be an integer, but instead it is: {v}"))),
    }
}

/// Strict binary built-ins of `Interp::builtin2` (the common operators,
/// evaluated without copying their arguments).
#[inline]
pub(crate) fn is_plain2(op: B) -> bool {
    matches!(
        op,
        B::Eq
            | B::Neq
            | B::In
            | B::NotIn
            | B::Plus
            | B::Minus
            | B::Mul
            | B::Mod
            | B::Div
            | B::Lt
            | B::Gt
            | B::Le
            | B::Ge
            | B::DotDot
            | B::Cup
            | B::Cap
            | B::SetMinus
            | B::SubsetEq
            | B::Concat
            | B::Append
    )
}

/// Strict binary built-ins with a boolean result (`compare2`).
#[inline]
pub(crate) fn is_compare2(op: B) -> bool {
    matches!(op, B::Eq | B::Neq | B::In | B::NotIn | B::Lt | B::Gt | B::Le | B::Ge | B::SubsetEq)
}

/// A strict binary built-in with a boolean result (`is_compare2`) applied
/// to its arguments (as `Interp::builtin2` applies it).
#[inline]
pub(crate) fn compare2(op: B, a: &Value, b: &Value) -> EResult<bool> {
    Ok(match op {
        B::Eq => order::eq_tlc(a, b)?,
        B::Neq => !order::eq_tlc(a, b)?,
        B::In => ops::member(a, b)?,
        B::NotIn => !ops::member(a, b)?,
        B::Lt | B::Gt | B::Le | B::Ge => {
            let name = match op {
                B::Lt => "<",
                B::Gt => ">",
                B::Le => "<=",
                _ => ">=",
            };
            let (x, y) = (int(a, name)?, int(b, name)?);
            match op {
                B::Lt => x < y,
                B::Gt => x > y,
                B::Le => x <= y,
                _ => x >= y,
            }
        }
        B::SubsetEq => ops::subseteq(a, b)?,
        _ => unreachable!("not a comparison: {op:?}"),
    })
}

/// Strict unary built-ins of `builtin1`.
#[inline]
pub(crate) fn is_plain1(op: B) -> bool {
    matches!(op, B::Len | B::Head | B::Tail | B::Domain | B::Neg | B::Union | B::Subset)
}

/// A strict unary built-in (`is_plain1`) applied to its argument (as
/// `Interp::builtin_values` applies it).
pub(crate) fn builtin1(op: B, a: &Value) -> EResult<Value> {
    Ok(match op {
        B::Len => Value::Int(ops::len(a)?),
        B::Head => ops::head(a)?,
        B::Tail => ops::tail(a)?,
        B::Domain => ops::domain(a)?,
        B::Neg => Value::Int(arith::neg(int(a, "-")?)?),
        B::Union => ops::big_union(a)?,
        B::Subset => ops::powerset(a)?,
        _ => unreachable!("not a plain unary built-in: {op:?}"),
    })
}

impl Interp {
    pub(crate) fn builtin(self: &Arc<Self>, op: B, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        if let Some((m, n)) = op.java_only_name() {
            return Err(EvalError::at(tlx_sema::builtins::unsupported_error(m, n), span));
        }
        if let Some(d) = self.builtin_override(op) {
            return self.apply_overridden(d, args, env, cx, span);
        }
        match op {
            B::Prime => {
                if cx.init || cx.s1.is_none() {
                    return Err(EvalError::at("primed expression evaluated in a non-action context", span));
                }
                self.eval(&args[0], env, &cx.primed())
            }
            B::Unchanged => Ok(Value::Bool(self.unchanged(&args[0], env, cx)?)),
            B::Enabled => Ok(Value::Bool(self.enabled(&args[0], env, cx)?)),
            B::Compose => Ok(Value::Bool(self.composition_holds(&args[0], &args[1], env, cx, span)?)),
            B::Not => Ok(Value::Bool(!self.eval_bool(&args[0], env, cx)?)),
            B::Implies => Ok(Value::Bool(!self.eval_bool(&args[0], env, cx)? || self.eval_bool(&args[1], env, cx)?)),
            B::SelectSeq => self.select_seq(&args[0], &args[1], env, cx, span),
            B::CausalOrder => self.causal_order(args, env, cx, span),
            // SequencesExt.java returns the index in the *original* sequence
            // (the TLA+ definition indexes the subsequence; TLC wins).
            B::SelectInSubSeq => self.select_in_sub_seq(&args[0], &args[1], &args[2], &args[3], env, cx, span),
            B::SelectLastInSubSeq => self.select_last_in_sub_seq(&args[0], &args[1], &args[2], &args[3], env, cx, span),
            B::MapThenFoldSet => self.map_then_fold_set(args, env, cx, span),
            B::SortSeq => self.sort_seq(&args[0], &args[1], env, cx, span),
            B::BagOfAll => self.bag_of_all(&args[0], &args[1], env, cx, span),
            B::FoldBag => self.fold_bag(args, env, cx, span),
            B::FoldSet => self.fold_set(args, env, cx, span),
            B::FoldFunction => self.fold_function(args, env, cx, span),
            B::FoldFunctionOnSet => self.fold_function_on_set(args, env, cx, span),
            B::FoldSeq => self.fold_seq(args, env, cx, span),
            B::FoldLeft => self.fold_left(args, env, cx, span),
            B::FoldRight => self.fold_right(args, env, cx, span),
            B::FoldLeftDomain => self.fold_left_domain(args, env, cx, span),
            B::FoldRightDomain => self.fold_right_domain(args, env, cx, span),
            B::TLCGet => {
                let k = self.eval(&args[0], env, cx)?;
                self.tlc_get(&k, cx, span)
            }
            B::TLCSet => {
                let k = self.eval(&args[0], env, cx)?;
                let v = self.eval(&args[1], env, cx)?;
                self.tlc_set(&k, v, span)
            }
            B::Trace => self.trace(cx, span),
            B::AssertError => self.assert_error(&args[0], &args[1], env, cx, span),
            B::TLCCache => self.tlc_cache(&args[0], &args[1], env, cx),
            // TLC normalizes a set enumeration `{a, b}` when it is first
            // used, here inside the Java method (whose wrapper an error of
            // the normalization then gets, e.g. comparing `Nat` with
            // `Nat \cup {0}`).
            B::Cardinality | B::IsFiniteSet | B::ToString if matches!(&*args[0].kind, ExprKind::SetEnum(_)) => {
                let ExprKind::SetEnum(es) = &*args[0].kind else { unreachable!() };
                let vs = es.iter().map(|x| self.eval(x, env, cx)).collect::<EResult<Vec<_>>>()?;
                let sig = match op {
                    B::Cardinality => CARDINALITY,
                    B::IsFiniteSet => IS_FINITE_SET,
                    _ => TO_STRING,
                };
                let set = java_override(sig, Value::set_from(vs))?;
                self.builtin_values(op, &[set], cx, span)
            }
            B::Always | B::Eventually | B::LeadsTo | B::WhilePlus => {
                Err(EvalError::at(format!("`{}` cannot be evaluated by the explicit-state checker", op.name()), span))
            }
            // Strict built-ins: the arguments of the common arities are
            // kept on the stack; those of the common operators are not
            // copied (`eval_cow`).
            _ => match args {
                [x, y] if is_plain2(op) => {
                    let x = self.eval_cow(x, env, cx)?;
                    let y = self.eval_cow(y, env, cx)?;
                    self.builtin2(op, &x, &y).map_err(|e| e.with_span(span))
                }
                [x] if is_plain1(op) => {
                    let x = self.eval_cow(x, env, cx)?;
                    builtin1(op, &x).map_err(|e| e.with_span(span))
                }
                [] => self.builtin_values(op, &[], cx, span),
                [x] => self.builtin_values(op, &[self.eval(x, env, cx)?], cx, span),
                [x, y] => {
                    let x = self.eval(x, env, cx)?;
                    self.builtin_values(op, &[x, self.eval(y, env, cx)?], cx, span)
                }
                [x, y, z] => {
                    let x = self.eval(x, env, cx)?;
                    let y = self.eval(y, env, cx)?;
                    self.builtin_values(op, &[x, y, self.eval(z, env, cx)?], cx, span)
                }
                _ => {
                    let vs = args.iter().map(|a| self.eval(a, env, cx)).collect::<EResult<Vec<_>>>()?;
                    self.builtin_values(op, &vs, cx, span)
                }
            },
        }
    }

    /// A strict binary built-in (`is_plain2`) applied to its arguments (as
    /// `builtin_values` applies it).
    pub(crate) fn builtin2(&self, op: B, a: &Value, b: &Value) -> EResult<Value> {
        Ok(match op {
            B::Eq | B::Neq | B::In | B::NotIn | B::Lt | B::Gt | B::Le | B::Ge | B::SubsetEq => Value::Bool(compare2(op, a, b)?),
            B::Plus => Value::Int(arith::add(int(a, "+")?, int(b, "+")?)?),
            B::Minus => Value::Int(arith::sub(int(a, "-")?, int(b, "-")?)?),
            B::Mul => Value::Int(arith::mul(int(a, "*")?, int(b, "*")?)?),
            B::Div => {
                let (x, y) = (int(a, "\\div")?, int(b, "\\div")?);
                Value::Int(if self.div_floor { arith::div_floor(x, y)? } else { arith::div_naturals(x, y)? })
            }
            B::Mod => Value::Int(arith::modulo(int(a, "%")?, int(b, "%")?)?),
            B::DotDot => ops::interval(int(a, "..")?, int(b, "..")?),
            B::Cup => ops::union(a, b)?,
            B::Cap => ops::intersect(a, b)?,
            B::SetMinus => ops::difference(a, b)?,
            B::Concat => ops::concat(a, b)?,
            B::Append => ops::append(a, b.clone())?,
            _ => unreachable!("not a plain binary built-in: {op:?}"),
        })
    }

    /// Apply a strict built-in to evaluated arguments (for the compiler's
    /// IR interpreter); respects cfg overrides of standard-module operators.
    pub fn builtin_on_values(self: &Arc<Self>, op: B, args: Vec<Value>, cx: &Ctx) -> EResult<Value> {
        self.builtin_values(op, &args, cx, Span::default())
    }

    /// Strict built-ins on evaluated arguments.
    pub(crate) fn builtin_values(self: &Arc<Self>, op: B, a: &[Value], cx: &Ctx, span: Span) -> EResult<Value> {
        if let Some((m, n)) = op.java_only_name() {
            return Err(EvalError::at(tlx_sema::builtins::unsupported_error(m, n), span));
        }
        if let Some(d) = self.builtin_override(op) {
            if let Some(v) = self.def_value.get(&d) {
                return Ok(v.clone());
            }
            return self.apply_opval_values(&OpVal::Ref(OpRef::Def(self.redirect_def(d))), a.to_vec(), cx, span);
        }
        let r: EResult<Value> = (|| {
            Ok(match op {
                B::Eq
                | B::Neq
                | B::In
                | B::NotIn
                | B::Plus
                | B::Minus
                | B::Mul
                | B::Mod
                | B::Div
                | B::Lt
                | B::Gt
                | B::Le
                | B::Ge
                | B::DotDot
                | B::Cup
                | B::Cap
                | B::SetMinus
                | B::SubsetEq
                | B::Concat
                | B::Append => self.builtin2(op, &a[0], &a[1])?,
                B::Len | B::Head | B::Tail | B::Domain | B::Neg | B::Union | B::Subset => builtin1(op, &a[0])?,
                B::Not => Value::Bool(!as_bool(&a[0], span)?),
                B::Implies => Value::Bool(!as_bool(&a[0], span)? || as_bool(&a[1], span)?),
                B::Equiv => Value::Bool(as_bool(&a[0], span)? == as_bool(&a[1], span)?),
                B::Times => ops::product(a.to_vec())?,
                B::Boolean => Value::set_from(vec![Value::FALSE, Value::TRUE])?,
                B::StringSet => Value::LazySet(Arc::new(LazySet::StringSet)),
                B::Nat => Value::LazySet(Arc::new(LazySet::Nat)),
                B::Int => Value::LazySet(Arc::new(LazySet::Int)),
                B::Pow => Value::Int(arith::pow(int(&a[0], "^")?, int(&a[1], "^")?)?),
                B::Seq => ops::seq_set(&a[0])?,
                B::SubSeq => ops::subseq(&a[0], int(&a[1], "SubSeq")?, int(&a[2], "SubSeq")?)?,
                B::AllSubSeqs => crate::natives::all_sub_seqs(&a[0])?,
                B::ReplaceAllSubSeqs => crate::natives::replace_all_sub_seqs(&a[0], &a[1], &a[2])?,
                B::ToJson => crate::natives::json::to_json(&a[0])?,
                B::ToJsonArray => crate::natives::json::to_json_array(&a[0])?,
                B::ToJsonObject => crate::natives::json::to_json_object(&a[0])?,
                B::ChiSquare => crate::natives::stats::chi_square(&a[0], &a[1], &a[2])?,
                B::IsFiniteSet => Value::Bool(java_override(IS_FINITE_SET, ops::is_finite_set(&a[0]))?),
                // (A set that is not `Enumerable` is refused by the method
                // itself, with an error that is not wrapped.)
                B::KSubset => ops::ksubset(&a[0], &a[1])?,
                B::Cardinality => Value::Int(match &a[0] {
                    Value::LazySet(l)
                        if matches!(**l, LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any) =>
                    {
                        ops::cardinality(&a[0])?
                    }
                    _ => java_override(CARDINALITY, ops::cardinality(&a[0]))?,
                }),
                B::ColonGt => ops::single_fcn(a[0].clone(), a[1].clone())?,
                B::AtAt => ops::fcn_merge(&a[0], &a[1])?,
                // TLC prints with `toStringUnchecked` (see `printable`).
                B::Print => {
                    let (x, y) = (tlx_value::fmt::printable(&a[0])?, tlx_value::fmt::printable(&a[1])?);
                    if !self.print_suppressed() {
                        self.print_line(&format!("{x}  {y}"));
                    }
                    a[1].clone()
                }
                B::PrintT => {
                    let x = tlx_value::fmt::printable(&a[0])?;
                    if !self.print_suppressed() {
                        self.print_line(&x.to_string());
                    }
                    Value::TRUE
                }
                B::Assert => {
                    if !as_bool(&a[0], span)? {
                        // (TLC shows the value: a string quoted, a tuple not.)
                        let msg = a[1].to_string();
                        let e = EvalError::of_kind(
                            tlx_runtime::ErrorKind::AssertFailed,
                            format!("The first argument of Assert evaluated to FALSE; the second argument was:\n{msg}"),
                        );
                        return Err(e.with_span(span));
                    }
                    Value::TRUE
                }
                B::JavaTime => Value::Int(
                    (std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0) & 0x7fff_ffff)
                        as i64,
                ),
                B::Permutations => {
                    let elems = ops::enumerate_normalized(&a[0])?;
                    let mut perms = Vec::new();
                    permutations::for_each_permutation(&elems, |cur| {
                        perms.push(permutations::function_permutation(&elems, cur)?);
                        Ok(())
                    })?;
                    Value::set_from(perms)?
                }
                // SequencesExt.java: the elements of `S` in TLC's normalized
                // (sorted) order, as a sequence. (The TLA+ definition, a CHOOSE
                // over an injective function, enumerates the whole function set.)
                B::SetToSeq => Value::tuple(ops::enumerate_normalized(&a[0])?),
                // SequencesExt.java `SetToSeqs`: every permutation of `S`'s
                // elements *as a sequence* (also `<<>>` when `S` is empty).
                // (Not `Permutations`, which maps elements to elements.)
                B::SetToSeqs => {
                    let elems = ops::enumerate_normalized(&a[0])?;
                    let mut seqs = Vec::new();
                    permutations::for_each_permutation(&elems, |cur| {
                        seqs.push(Value::tuple(cur.to_vec()));
                        Ok(())
                    })?;
                    Value::set_from(seqs)?
                }
                B::RandomElement => self.random_element(&a[0], cx)?,
                // Randomization (TLC's Java overrides): random choices
                // instead of enumerating SUBSET S.
                B::RandomSubset => {
                    let k = int(&a[0], "RandomSubset")?;
                    if k < 0 {
                        return Err(EvalError::new(format!(
                            "The first argument of RandomSubset should be a nonnegative integer, but instead it is {k}"
                        )));
                    }
                    if !ops::is_finite_set(&a[1])? {
                        return Err(EvalError::new(format!(
                            "The second argument of RandomSubset should be a finite set, but instead it is:\n{}",
                            a[1]
                        )));
                    }
                    self.random_subset(k, &a[1], cx)?
                }
                B::RandomSetOfSubsets => {
                    // k random subsets of S, each element in with probability n / |S|.
                    let (k, n) = (int(&a[0], "RandomSetOfSubsets")?, int(&a[1], "RandomSetOfSubsets")?);
                    let size = ops::cardinality(&a[2])?;
                    if k < 0 || n < 0 || n > size || (size < 62 && k > (1i64 << size)) {
                        return Err(EvalError::new(
                            "RandomSetOfSubsets: invalid arguments (0 <= k <= 2^Cardinality(S) and 0 <= n <= Cardinality(S) are required)",
                        ));
                    }
                    self.random_set_of_subsets(k, n, &a[2], cx)?
                }
                B::ToString => Value::Str(Sym::new(&java_override(TO_STRING, tlx_value::fmt::printable(&a[0]))?.to_string())),
                B::IOEnv => crate::natives::io_env(),
                B::Atoi => crate::natives::atoi(&a[0])?,
                B::IsInjective => crate::natives::is_injective(&a[0])?,
                B::TLCModelValue => match &a[0] {
                    Value::Str(s) => Value::ModelValue(*s),
                    v => {
                        let msg = format!("The argument of ModelValue should be a string, but instead it is:\n{v}");
                        return Err(EvalError::of_kind(tlx_runtime::ErrorKind::ArgumentError, msg));
                    }
                },
                // (TLC: FP64.Hash of the fingerprint, an int.)
                B::TLCFP => Value::Int(i64::from(tlx_value::fingerprint::fingerprint(&a[0].normalize()?)? as u32 as i32)),
                B::CsvWrite => crate::natives::csv_write(&a[0], &a[1], &a[2], |path, bytes| {
                    self.with_file_write(path, crate::interp::effects::FileWrite::Append, bytes, "CSVWrite")
                })?,
                B::CsvRecords => crate::natives::csv_records(&a[0])?,
                B::CsvWriteRecord => crate::natives::csv_write_record(&a[0], &a[1], &a[2], &a[3], |path, bytes| {
                    self.with_file_write(path, crate::interp::effects::FileWrite::Append, bytes, "CSVWriteRecord")
                })?,
                B::CsvRead => crate::natives::csv_read(&a[0], &a[1], &a[2])?,
                B::JsonSerialize => crate::natives::json::json_serialize(&a[0], &a[1], |path, bytes| {
                    self.with_file_write(path, crate::interp::effects::FileWrite::Overwrite, bytes, "JsonSerialize")
                })?,
                B::NdJsonSerialize => crate::natives::json::nd_json_serialize(&a[0], &a[1], |path, bytes| {
                    self.with_file_write(path, crate::interp::effects::FileWrite::Overwrite, bytes, "ndJsonSerialize")
                })?,
                B::JsonDeserialize => crate::natives::json::json_deserialize(&a[0])?,
                B::NdJsonDeserialize => crate::natives::json::nd_json_deserialize(&a[0])?,
                B::IOExec => self.run_command(crate::natives::PreparedCommand::io_exec(&a[0])?)?,
                B::IOEnvExec => self.run_command(crate::natives::PreparedCommand::io_env_exec(&a[0], &a[1])?)?,
                B::IOExecTemplate => self.run_command(crate::natives::PreparedCommand::io_exec_template(&a[0], &a[1])?)?,
                B::IOEnvExecTemplate => self.run_command(crate::natives::PreparedCommand::io_env_exec_template(&a[0], &a[1], &a[2])?)?,
                B::GraphConnected => crate::natives::are_connected_in(&a[0], &a[1], &a[2], true)?,
                B::UGraphConnected => crate::natives::are_connected_in(&a[0], &a[1], &a[2], false)?,
                B::GraphStronglyConnected => crate::natives::is_strongly_connected(&a[0], true)?,
                B::UGraphStronglyConnected => crate::natives::is_strongly_connected(&a[0], false)?,
                B::UGraphComponents => crate::natives::connected_components(&a[0])?,
                B::GraphSimplePath => crate::natives::simple_path(&a[0], true)?,
                B::UGraphSimplePath => crate::natives::simple_path(&a[0], false)?,
                B::Gcd => Value::Int(tlx_value::arith::gcd(int(&a[0], "GCD")?, int(&a[1], "GCD")?)?),
                B::Choose => crate::natives::choose(&a[0], &a[1])?,
                B::SetMax | B::SetMin => {
                    // CHOOSE x \in S : \A y \in S : x >= y (resp. =<).
                    let elems = ops::enumerate_normalized(&a[0])?;
                    let mut best: Option<i64> = None;
                    for e in &elems {
                        let i = int(e, if op == B::SetMax { ">=" } else { "=<" })?;
                        best = Some(match best {
                            None => i,
                            Some(b) if op == B::SetMax => b.max(i),
                            Some(b) => b.min(i),
                        });
                    }
                    match best {
                        Some(b) => Value::Int(b),
                        None => return Err(EvalError::new(
                            "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.",
                        )),
                    }
                }
                B::TLCEval => a[0].clone(),
                B::TLCGetOrDefault => self.tlc_get_or_default(&a[0], &a[1], span)?,
                B::EmptyBag => Value::empty_fcn(),
                B::IsABag => crate::bags::is_a_bag(&a[0])?,
                B::BagCardinality => crate::bags::bag_cardinality(&a[0])?,
                B::BagIn => crate::bags::bag_in(&a[0], &a[1], false)?,
                B::CopiesIn => crate::bags::bag_in(&a[0], &a[1], true)?,
                B::BagCup => crate::bags::bag_cup(&a[0], &a[1])?,
                B::BagDiff => crate::bags::bag_diff(&a[0], &a[1])?,
                B::BagUnion => crate::bags::bag_union(&a[0])?,
                B::SqSubseteq => crate::bags::sq_subseteq(&a[0], &a[1])?,
                B::BagToSet => crate::bags::bag_to_set(&a[0])?,
                B::SetToBag => crate::bags::set_to_bag(&a[0])?,
                B::Any => Value::LazySet(Arc::new(LazySet::Any)),
                B::TLCGet
                | B::TLCSet
                | B::Prime
                | B::Unchanged
                | B::Enabled
                | B::SelectSeq
                | B::SelectInSubSeq
                | B::CausalOrder
                | B::SelectLastInSubSeq
                | B::SortSeq
                | B::MapThenFoldSet
                | B::BagOfAll
                | B::FoldBag
                | B::FoldSet
                | B::FoldFunction
                | B::FoldFunctionOnSet
                | B::FoldSeq
                | B::FoldLeft
                | B::FoldRight
                | B::FoldLeftDomain
                | B::FoldRightDomain
                | B::Always
                | B::Eventually
                | B::LeadsTo
                | B::WhilePlus
                | B::Compose
                | B::UnsupportedDotDiGraph
                | B::UnsupportedIoDeserialize
                | B::UnsupportedIoSerialize
                | B::UnsupportedDeserialize
                | B::UnsupportedSerialize
                | B::UnsupportedSvgElemToString
                | B::UnsupportedNodeOfRingNetwork
                | B::AssertError
                | B::TLCCache
                | B::Trace
                | B::UnsupportedCounterExample
                | B::UnsupportedToTrace
                | B::UnsupportedTLCEvalDefinition => return Err(EvalError::new(format!("`{}` cannot be applied to values", op.name()))),
            })
        })();
        r.map_err(|e| e.with_span(span))
    }

    /// `TLCExt!Trace` (TLCExt.java `getTrace`): the states from an initial
    /// state to the current one, as records of the variables. The search
    /// provides the path to the state it expands
    /// (`tlx_runtime::live::current_path`); the current state is a successor
    /// of it unless it is that state itself (the next-state relation or an
    /// action property is evaluated). Without a path (the initial states),
    /// only the current state. In simulation each record also has the
    /// action that produced the state (field `_action`, as
    /// `TLCGet("action")`).
    fn trace(&self, cx: &Ctx, span: Span) -> EResult<Value> {
        use tlx_runtime::live::{current_path, CurrentPath};
        let vars = &self.prog.vars;
        let unassigned = |missing: Vec<&str>| {
            EvalError::at(
                format!(
                    "In evaluating TLCExt!Trace, the state is not completely specified yet (variable{} {} undefined).",
                    if missing.len() > 1 { "s" } else { "" },
                    missing.join(", ")
                ),
                span,
            )
        };
        let cur: Vec<Value> = match (cx.init, cx.s0, cx.s1) {
            (true, _, Some(s1)) => {
                let missing: Vec<&str> = s1.iter().zip(vars).filter(|(v, _)| v.is_none()).map(|(_, d)| &*d.name).collect();
                if !missing.is_empty() {
                    return Err(unassigned(missing));
                }
                s1.iter().map(|v| v.clone().expect("assigned")).collect()
            }
            (false, Some(s0), _) => s0.to_vec(),
            _ => return Err(unassigned(vars.iter().map(|d| &*d.name).collect())),
        };
        let sim = self.is_simulation();
        let action = |a: Option<u32>| -> Value {
            let info = self.spec_info();
            match (info, a) {
                (Some(i), None) => i.init_action.clone(),
                (Some(i), Some(a)) if (a as usize) < i.actions.len() => i.actions[a as usize].clone(),
                _ => Value::record(Vec::new()),
            }
        };
        let record = |vals: &[Value], a: Option<u32>| -> Value {
            let mut fs: Vec<(Sym, Value)> = vars.iter().zip(vals).map(|(d, v)| (Sym::new(&d.name), v.clone())).collect();
            if sim {
                fs.push((Sym::new("_action"), action(a)));
            }
            Value::record(fs)
        };
        let mut out: Vec<Value> = Vec::new();
        let mut last: Option<std::sync::Arc<[Value]>> = None;
        match current_path() {
            None => {}
            Some(CurrentPath::Unavailable) => {
                return Err(EvalError::at("TLCExt!Trace: the path to the current state is not available", span));
            }
            Some(CurrentPath::Known(n)) => {
                for p in n.states() {
                    out.push(record(&p.values, p.action));
                    last = Some(p.values.clone());
                }
            }
        }
        if last.as_deref() != Some(&cur[..]) {
            // (In simulation, the action producing the state checked.)
            let a = match tlx_runtime::live::current_action() {
                Some(tlx_runtime::CurrentAction::Action(a)) => Some(a),
                _ => None,
            };
            out.push(record(&cur, a));
        }
        Ok(Value::tuple(out))
    }

    /// `SelectInSubSeq(s, from, to, Test)` (SequencesExt.java): the first
    /// index `i` in `from..to` with `Test(s[i])`, in the *original* sequence
    /// (the TLA+ definition would index the subsequence); 0 if none.
    #[allow(clippy::too_many_arguments)] // the argument set of the hot-path/dispatch signature; a bundling struct would only rename them
    fn select_in_sub_seq(
        self: &Arc<Self>,
        seq: &Expr,
        from: &Expr,
        to: &Expr,
        test: &Expr,
        env: &Env,
        cx: &Ctx,
        span: Span,
    ) -> EResult<Value> {
        self.sub_seq_search(seq, from, to, test, env, cx, span, false)
    }

    /// `SelectLastInSubSeq(s, from, to, Test)`: like `select_in_sub_seq`,
    /// scanning `to..from` (highest matching index), in the original sequence.
    #[allow(clippy::too_many_arguments)] // the argument set of the hot-path/dispatch signature; a bundling struct would only rename them
    fn select_last_in_sub_seq(
        self: &Arc<Self>,
        seq: &Expr,
        from: &Expr,
        to: &Expr,
        test: &Expr,
        env: &Env,
        cx: &Ctx,
        span: Span,
    ) -> EResult<Value> {
        self.sub_seq_search(seq, from, to, test, env, cx, span, true)
    }

    #[allow(clippy::too_many_arguments)]
    fn sub_seq_search(
        self: &Arc<Self>,
        seq: &Expr,
        from: &Expr,
        to: &Expr,
        test: &Expr,
        env: &Env,
        cx: &Ctx,
        span: Span,
        last: bool,
    ) -> EResult<Value> {
        let name = if last { "SelectLastInSubSeq" } else { "SelectInSubSeq" };
        let s = crate::eval::force_seq(self.eval(seq, env, cx)?)?;
        let Value::Tuple(elems) = &s else {
            return Err(EvalError::at(format!("The first argument of {name} should be a sequence, but instead it is:\n{s}"), span));
        };
        let from_v = self.eval(from, env, cx)?;
        let to_v = self.eval(to, env, cx)?;
        let test = self.native_op_val(test, env, "fourth", name, span)?;
        let (f, t) = match (&from_v, &to_v) {
            (Value::Int(f), Value::Int(t)) => (*f, *t),
            (Value::Int(_), _) => {
                return Err(EvalError::at(
                    format!("The third argument of {name} should be a natural number, but instead it is:\n{to_v}"),
                    span,
                ))
            }
            _ => {
                return Err(EvalError::at(
                    format!("The second argument of {name} should be a natural number, but instead it is:\n{from_v}"),
                    span,
                ))
            }
        };
        if f > t {
            return Ok(Value::Int(0));
        }
        let n = elems.len() as i64;
        if f < 1 || f > n {
            return Err(EvalError::at(format!("The second argument of {name} is out of bounds: from = {f}, Len(seq) = {n}"), span));
        }
        if t < 1 || t > n {
            return Err(EvalError::at(format!("The third argument of {name} is out of bounds: to = {t}, Len(seq) = {n}"), span));
        }
        let range: Box<dyn Iterator<Item = i64>> = if last { Box::new((f..=t).rev()) } else { Box::new(f..=t) };
        for i in range {
            let r = self.apply_opval_values(&test, vec![elems[(i - 1) as usize].clone()], cx, span)?;
            if as_bool(&r, span)? {
                return Ok(Value::Int(i));
            }
        }
        Ok(Value::Int(0))
    }

    /// `SelectSeq(s, Test)`.
    fn select_seq(self: &Arc<Self>, seq: &Expr, test: &Expr, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let s = crate::eval::force_seq(self.eval(seq, env, cx)?)?;
        let test = self.native_op_val(test, env, "second", "SelectSeq", span)?;
        let Value::Tuple(elems) = &s else {
            return Err(EvalError::at(format!("The first argument of SelectSeq should be a sequence, but instead it is: {s}"), span));
        };
        let mut out = Vec::new();
        for e in elems.iter() {
            let r = self.apply_opval_values(&test, vec![e.clone()], cx, span)?;
            if as_bool(&r, span)? {
                out.push(e.clone());
            }
        }
        Ok(Value::tuple(out))
    }

    /// `CausalOrder(log, clock(_), node(_), domain(_))` (VectorClocks.java
    /// `causalOrder`, after ShiViz): the log lines grouped by node, each
    /// node's lines sorted by its own clock entry; every line gets as
    /// parents the lines of other nodes its clock has seen (by their clock
    /// entry); then, until the log is used up, a pass over the nodes takes
    /// the first line of each node that has no parent left. TLC visits the
    /// nodes in the order of a Java `HashMap` of their ids, which depends on
    /// its fingerprint polynomial; tlx takes TLC's order under `-fp 0`
    /// (docs/compat.md D-25; ids other than integers, strings and booleans
    /// in the order they first appear).
    fn causal_order(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let log = crate::eval::force_seq(self.eval(&args[0], env, cx)?)?;
        let Value::Tuple(lines) = &log else {
            return Err(EvalError::at(format!("The first argument of CausalOrder should be a sequence, but instead it is: {log}"), span));
        };
        let clock = self.native_op_val(&args[1], env, "second", "CausalOrder", span)?;
        let node = self.native_op_val(&args[2], env, "third", "CausalOrder", span)?;
        let domain = self.native_op_val(&args[3], env, "fourth", "CausalOrder", span)?;
        struct Line {
            clock: Value,
            time: Value,
            hosts: Vec<Value>,
            parents: tlx_base::hash::FxSet<usize>,
            children: tlx_base::hash::FxSet<usize>,
        }
        // A1) Each node's lines, nodes in order of first appearance.
        let mut lines_of: Vec<(Value, Vec<usize>)> = Vec::new();
        let mut gs: Vec<Line> = Vec::with_capacity(lines.len());
        for l in lines.iter() {
            let id = self.apply_opval_values(&node, vec![l.clone()], cx, span)?;
            let vc = self.apply_opval_values(&clock, vec![l.clone()], cx, span)?;
            let time = ops::apply(&vc, &id)?;
            let dom = self.apply_opval_values(&domain, vec![vc.clone()], cx, span)?;
            let hosts = ops::enumerate_normalized(&dom)?;
            let g = gs.len();
            gs.push(Line { clock: vc, time, hosts, parents: Default::default(), children: Default::default() });
            match lines_of.iter_mut().find(|(n, _)| *n == id) {
                Some((_, ls)) => ls.push(g),
                None => lines_of.push((id, vec![g])),
            }
        }
        // A2) Each node's lines by its own clock entry (a stable sort;
        // TLC compares the entries as integers).
        let missing = |what: &str| EvalError::at(format!("CausalOrder: {what}"), span);
        let int = |v: &Value| match v {
            Value::Int(i) => Ok(*i),
            _ => Err(missing(&format!("the clock entry {v} is not an integer"))),
        };
        for l in &gs {
            int(&l.time)?;
        }
        for (_, ls) in &mut lines_of {
            ls.sort_by_key(|&g| int(&gs[g].time).unwrap_or(0));
        }
        // B) The parents of each line: for each node, the latest clock entry
        // of every other node seen so far along its lines.
        for (host, ls) in &lines_of {
            let mut global: Vec<i64> = vec![0; lines_of.len()];
            let me = lines_of.iter().position(|(n, _)| n == host).expect("a node");
            for &g in ls {
                global[me] = int(&gs[g].time)?;
                for other in gs[g].hosts.clone() {
                    let o = lines_of
                        .iter()
                        .position(|(n, _)| *n == other)
                        .ok_or_else(|| missing(&format!("the clock domain names {other}, which has no line in the log")))?;
                    let t = int(&ops::apply(&gs[g].clock, &other)?)?;
                    if global[o] < t {
                        global[o] = t;
                        let p = usize::try_from(t - 1).ok().and_then(|i| lines_of[o].1.get(i).copied());
                        let p = p.ok_or_else(|| missing(&format!("node {other} has no line {t}")))?;
                        gs[g].parents.insert(p);
                        gs[p].children.insert(g);
                    }
                }
            }
        }
        // C) Take the nodes' first lines without parents, pass after pass.
        let hashes: Option<Vec<i32>> = lines_of.iter().map(|(n, _)| crate::java_order::tlc_hash_code(n)).collect();
        let order = match hashes {
            Some(hs) => crate::java_order::hash_map_order(&hs),
            None => (0..lines_of.len()).collect(),
        };
        let mut next: Vec<usize> = vec![0; lines_of.len()];
        let mut sorted = Vec::with_capacity(lines.len());
        for _ in 0..lines.len() {
            for &h in &order {
                let ls = &lines_of[h].1;
                let Some(&g) = ls.get(next[h]) else { continue };
                if gs[g].parents.is_empty() {
                    next[h] += 1;
                    for c in std::mem::take(&mut gs[g].children) {
                        gs[c].parents.remove(&g);
                    }
                    sorted.push(lines[g].clone());
                }
            }
        }
        Ok(Value::tuple(sorted))
    }

    /// `SortSeq(s, Op)`: insertion sort with the user's comparator (stable,
    /// errors propagate).
    fn sort_seq(self: &Arc<Self>, seq: &Expr, lt: &Expr, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let s = crate::eval::force_seq(self.eval(seq, env, cx)?)?;
        let lt = self.native_op_val(lt, env, "second", "SortSeq", span)?;
        let Value::Tuple(elems) = &s else {
            return Err(EvalError::at(format!("The first argument of SortSeq should be a sequence, but instead it is: {s}"), span));
        };
        let mut v: Vec<Value> = elems.to_vec();
        for i in 1..v.len() {
            let mut j = i;
            while j > 0 {
                let r = self.apply_opval_values(&lt, vec![v[j].clone(), v[j - 1].clone()], cx, span)?;
                if !as_bool(&r, span)? {
                    break;
                }
                v.swap(j, j - 1);
                j -= 1;
            }
        }
        Ok(Value::tuple(v))
    }

    /// `TLCCache(expression, closure)` (TLCExt.java `tlcEval2`): a
    /// constant-level (SANY level) expression is evaluated once per value
    /// of the closure, at its first use, and that value is reused wherever
    /// the same expression is evaluated again with an equal closure (also
    /// when the expression's value would differ, e.g. because of TLCSet).
    /// Other expressions are just evaluated.
    fn tlc_cache(self: &Arc<Self>, expr: &Expr, closure: &Expr, env: &Env, cx: &Ctx) -> EResult<Value> {
        let constant =
            self.tlc_cache.lock().unwrap().entry(expr.span).or_insert_with(|| (self.prog.expr_level(expr) == 0).then(Vec::new)).is_some();
        if !constant {
            return self.eval(expr, env, cx);
        }
        let key = self.eval(closure, env, cx)?;
        let cached = |ip: &Self| -> EResult<Option<Value>> {
            for (k, v) in ip.tlc_cache.lock().unwrap()[&expr.span].iter().flatten() {
                if tlx_value::order::eq_tlc(k, &key)? {
                    return Ok(Some(v.clone()));
                }
            }
            Ok(None)
        };
        if let Some(v) = cached(self)? {
            return Ok(v);
        }
        let v = self.eval(expr, env, cx)?;
        // (Evaluated without the lock: another thread may have stored a
        // value meanwhile, which wins.)
        if let Some(old) = cached(self)? {
            return Ok(old);
        }
        if let Some(Some(vs)) = self.tlc_cache.lock().unwrap().get_mut(&expr.span) {
            vs.push((key, v.clone()));
        }
        Ok(v)
    }

    /// `AssertError(err, exp)` (TLCExt.java `assertError`): TRUE iff
    /// evaluating `exp` fails with the message `err`, which must be a string
    /// literal. TLC compares with its exception's message, which for some
    /// errors ends with the location of the failing expression; tlx keeps
    /// the location apart, so a message followed by it matches too.
    fn assert_error(self: &Arc<Self>, err: &Expr, exp: &Expr, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let ExprKind::Str(expected) = &*err.kind else {
            return Err(EvalError::at(
                "In computing AssertError, a non-string expression was used as the err of an AssertError(err, exp).",
                span,
            ));
        };
        let Err(e) = self.eval(exp, env, cx) else { return Ok(Value::FALSE) };
        let Some(rest) = expected.strip_prefix(e.message.as_str()) else { return Ok(Value::FALSE) };
        let located = || e.span.is_some_and(|sp| rest.strip_prefix('\n') == Some(self.prog.location(sp).as_str()));
        Ok(Value::Bool(rest.is_empty() || located()))
    }

    /// `TLCSet(k, v)`.
    fn tlc_set(&self, k: &Value, v: Value, span: Span) -> EResult<Value> {
        match k {
            Value::Int(i) if *i >= 0 => self.set_register(*i, v),
            Value::Str(s) if s.as_str() == "exit" => {
                if matches!(v, Value::Bool(true)) {
                    self.request_exit();
                }
            }
            Value::Str(s) if s.as_str() == "pause" => {}
            Value::Str(s) if s.as_str().starts_with(NAMED_REGISTER_PREFIX) => self.set_register(named_register(*s), v),
            _ => return Err(EvalError::at(format!("TLCSet: unsupported register {k}"), span)),
        }
        Ok(Value::TRUE)
    }

    /// `TLCGetOrDefault(k, d)` (TLCExt.java `tlcGetOrDefault`): the value of
    /// register `k` (an integer or a named register), else `d` (also for
    /// any other key).
    fn tlc_get_or_default(&self, k: &Value, d: &Value, span: Span) -> EResult<Value> {
        let r = match k {
            // (TLC: an array index out of bounds.)
            Value::Int(i) if *i < 0 => return Err(EvalError::at(format!("TLCGetOrDefault: invalid register {i}"), span)),
            Value::Int(i) => self.get_register(*i),
            Value::Str(s) if s.as_str().starts_with(NAMED_REGISTER_PREFIX) => self.get_register(named_register(*s)),
            _ => None,
        };
        Ok(r.unwrap_or_else(|| d.clone()))
    }

    /// The step from `cx`'s current state to its next state is an
    /// `A \cdot B` step: a B step from one of the intermediate states (see
    /// `enumerate::composition_mids`).
    fn composition_holds(self: &Arc<Self>, a: &Expr, b: &Expr, env: &Env, cx: &Ctx, span: Span) -> EResult<bool> {
        let (Some(s0), Some(s1), false) = (cx.s0, cx.s1, cx.init) else {
            return Err(EvalError::at("action composition evaluated in a non-action context", span));
        };
        for mid in crate::enumerate::composition_mids(self, s0, cx.level, a, env)? {
            if self.eval_bool(b, env, &Ctx::action(&mid, s1, cx.level))? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// `TLCGet(k)` (tlc2/module/TLCGetSet.java).
    fn tlc_get(self: &Arc<Self>, k: &Value, cx: &Ctx, span: Span) -> EResult<Value> {
        let rec = |fs: Vec<(&str, Value)>| Value::record(fs.into_iter().map(|(n, v)| (Sym::new(n), v)).collect());
        match k {
            Value::Int(i) if *i >= 0 => self
                .get_register(*i)
                .ok_or_else(|| EvalError::at(format!("TLCGet({i}) was called but no value was set by TLCSet({i}, ...)."), span)),
            Value::Str(s) if s.as_str().starts_with(NAMED_REGISTER_PREFIX) => self
                .get_register(named_register(*s))
                .ok_or_else(|| EvalError::at(format!("TLCGet({k}) was called but no value was set by TLCSet({k}, ...)."), span)),
            Value::Str(s) => match s.as_str() {
                // Primed: the level of the next state (TLC evaluates `e'`
                // over the next state, one level deeper).
                "level" => Ok(Value::Int(if cx.init {
                    0
                } else if cx.primed {
                    cx.level as i64 + 1
                } else {
                    cx.level as i64
                })),
                "config" => {
                    let (workers, deadlock) = self.run_config();
                    Ok(match self.sim_config() {
                        // (TLC's Simulator.createConfig.)
                        Some(sim) => rec(vec![
                            ("mode", Value::str(if sim.generate { "generate" } else { "simulate" })),
                            ("deadlock", Value::Bool(deadlock)),
                            ("worker", Value::Int(workers as i64)),
                            ("seed", Value::str(&sim.seed.to_string())),
                            ("traces", Value::Int(sim.traces)),
                            ("depth", Value::Int(sim.depth)),
                            ("aril", Value::str("0")),
                            ("sched", Value::str("random")),
                            ("install", Value::str("")),
                        ]),
                        None => rec(vec![
                            ("mode", Value::str("bfs")),
                            ("deadlock", Value::Bool(deadlock)),
                            ("worker", Value::Int(workers as i64)),
                            ("seed", Value::str(&self.seed().to_string())),
                            ("fingerprint", Value::str("0")),
                            ("install", Value::str("")),
                        ]),
                    })
                }
                // The TLC revision whose behavior tlx follows (specs test
                // `TLCGet("revision").timestamp` for TLC features).
                "revision" => Ok(rec(vec![
                    ("count", Value::Int(0)),
                    ("timestamp", Value::Int(1790958956)),
                    ("date", Value::str("2026-10-02T16:35:56.5Z")),
                    ("tag", Value::str("tlx")),
                    ("calver", Value::str(env!("CARGO_PKG_VERSION"))),
                ])),
                // Java system properties TLC is run with: tlx implements
                // action composition (TLC's -Dtlc2.tool.impl.Tool.cdot=true).
                "-Dtlc2.tool.impl.Tool.cdot" => Ok(Value::str("true")),
                // (Before the model exists, TLC has no statistics.)
                "stats" | "distinct" | "generated" | "queue" | "diameter"
                    if self.before_model.load(std::sync::atomic::Ordering::Relaxed) =>
                {
                    Err(EvalError::at(format!("TLCGet({}) was undefined.", s.as_str()), span))
                }
                "stats" | "distinct" | "generated" | "queue" | "diameter" | "duration" => {
                    // During the search (and TLC's liveness search after
                    // it, see tlx_runtime::liveness): live ones; after the
                    // search or in simulation: the recorded statistics.
                    let live = || {
                        let l = tlx_runtime::live::current()?;
                        let s = crate::RunStats {
                            distinct: l.distinct,
                            generated: l.generated,
                            queue: l.queue,
                            diameter: l.diameter,
                            duration_secs: l.duration_secs,
                            initial: l.initial,
                            ..Default::default()
                        };
                        Some(Self::stats_record(&s))
                    };
                    // (Before the search, as TLC: nothing found yet.)
                    let before = || Self::stats_record(&crate::RunStats { diameter: 1, ..Default::default() });
                    let stats = live().or_else(|| self.final_stats()).unwrap_or_else(before);
                    if s.as_str() == "stats" {
                        if let Some(sim) = self.final_sim_stats() {
                            return Ok(sim);
                        }
                        return Ok(stats);
                    }
                    if let (true, Some(d)) = (s.as_str() == "duration", self.sim_duration()) {
                        return Ok(Value::Int(d as i64));
                    }
                    Ok(tlx_value::ops::field(&stats, Sym::new(s.as_str()))?)
                }
                // TLC knows the action of a state only in simulation.
                "action" => {
                    let info = self.spec_info();
                    let current = if self.is_simulation() { tlx_runtime::live::current_action() } else { None };
                    Ok(match (info, current) {
                        (Some(i), Some(tlx_runtime::CurrentAction::Init)) => i.init_action.clone(),
                        (Some(i), Some(tlx_runtime::CurrentAction::Action(a))) if (a as usize) < i.actions.len() => {
                            i.actions[a as usize].clone()
                        }
                        _ => rec(vec![
                            ("name", Value::str("UnnamedAction")),
                            ("location", crate::model::location_record(&tlx_sema::source::SourceRange::builtins())),
                        ]),
                    })
                }
                "spec" => match self.spec_info() {
                    Some(i) => Ok(i.spec.clone()),
                    None => Err(EvalError::at("TLCGet(\"spec\") is only available during model checking", span)),
                },
                // TLC: [i \in I |-> [w \in 1..workers |-> TLCGet(i) of worker w]]
                // (AbstractChecker.getAllValues / getAllNamedRegisterValues).
                "all" | "all:named" => {
                    let named = s.as_str() == "all:named";
                    let mut pairs = Vec::new();
                    for (k, per_worker) in self.all_registers(named) {
                        let key = if named {
                            // SAFETY: `k` is `named_register` of a `Sym` this
                            // process interned (registers are guarded by a mutex).
                            Value::Str(unsafe { Sym::from_id((-1 - k) as u32) })
                        } else {
                            Value::Int(k)
                        };
                        let vals = per_worker.into_iter().collect::<Option<Vec<_>>>().ok_or_else(|| {
                            EvalError::at(format!("TLCGet(\"{}\"): register {key} was not set by every worker", s.as_str()), span)
                        })?;
                        pairs.push((key, Value::tuple(vals)));
                    }
                    Ok(Value::fcn_rcd_from_pairs(pairs)?)
                }
                other => Err(EvalError::at(format!("TLCGet(\"{other}\") is not supported yet"), span)),
            },
            _ => Err(EvalError::at(
                format!("The argument of TLCGet should be a nonnegative integer or a string, but instead it is: {k}"),
                span,
            )),
        }
    }
}

/// String keys of TLCGet / TLCSet with this prefix name per-worker
/// registers (TLCGetSet.java `NAMED_REGISTER_PREFIX`).
const NAMED_REGISTER_PREFIX: &str = "s:";

/// The register of a named register `s`: kept with the integer registers,
/// under a negative key (`Sym` ids survive a checkpoint's restore).
pub(crate) fn named_register(s: Sym) -> i64 {
    -1 - s.id() as i64
}
