//! Reporting, diagnostics and coverage labels of the interpreted model.
//!
//! States, source locations, coverage labels, trace action labels and
//! evaluation errors are formatted here the way TLC prints them; the
//! `_POSSIBLE` predicates and the POSTCONDITIONs are evaluated here too.
//! Extracted from `mod.rs` (CODE-03: construction, execution, persistence
//! and reporting live at separate responsibility boundaries).

use super::*;

/// A state as TLC shows it: one `/\ name = value` line per variable; a
/// single variable has no bullet unless `bullet_single` (the ALIAS form).
pub(crate) fn fmt_state<N: std::fmt::Display, V: std::fmt::Display>(
    fields: impl IntoIterator<Item = (N, V)>,
    bullet_single: bool,
) -> String {
    let fields: Vec<(N, V)> = fields.into_iter().collect();
    if let (false, [(n, v)]) = (bullet_single, &fields[..]) {
        return format!("{n} = {v}");
    }
    fields.iter().map(|(n, v)| format!("/\\ {n} = {v}")).collect::<Vec<_>>().join("\n")
}

/// How a state is shown in a counterexample or a `-dump`: TLC's `-view`
/// and `-difftrace` command-line options (docs/configuration.md).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StateRenderOpts {
    /// `-view`: show a state through the `.cfg` `VIEW`, unless an `ALIAS`
    /// is configured (TLC evaluates the ALIAS first).
    pub use_view: bool,
    /// `-difftrace`: show only the fields of a state whose value differs
    /// from the preceding state's; a state without a predecessor (State 1,
    /// an initial-state violation) is shown in full.
    pub difftrace: bool,
}

/// The fields of a state as TLC prints them; with `diff`, the fields whose
/// value equals the predecessor's (same position and name) are left out.
/// `bullet_single`: a lone field keeps the `/\ ` prefix (the ALIAS and a
/// tuple `-view` do; a raw one-variable state does not, and a diffed raw
/// state of a model with more variables keeps it for every changed line).
fn render_fields(fields: &[(String, Value)], prev: Option<&[(String, Value)]>, diff: bool, bullet_single: bool) -> String {
    let kept: Vec<(&str, &Value)> = if diff {
        fields
            .iter()
            .enumerate()
            .filter(|(i, (n, v))| prev.and_then(|p| p.get(*i)).is_none_or(|(pn, pv)| pn != n || !tlx_value::order::certainly_equal(v, pv)))
            .map(|(_, (n, v))| (n.as_str(), v))
            .collect()
    } else {
        fields.iter().map(|(n, v)| (n.as_str(), v)).collect()
    };
    // (TLC checks the model's variable count, not the number of changed
    // fields, for the bullet of a raw state.)
    fmt_state(kept, bullet_single || fields.len() != 1)
}

/// TLC's location record (`beginLine`, ..., `module`) of `l`.
pub fn location_record(l: &Location) -> Value {
    use tlx_sema::source::Field;
    Value::record(
        l.fields()
            .into_iter()
            .map(|(n, f)| {
                (
                    Sym::new(n),
                    match f {
                        Field::Int(i) => Value::Int(i),
                        Field::Str(m) => Value::str(m),
                    },
                )
            })
            .collect(),
    )
}

/// An action instance as TLC describes it in a counterexample (`Action`:
/// name, location, and the parameters of its definition with their values).
pub struct ActionInfo {
    pub name: String,
    pub location: Location,
    pub params: Vec<(String, Value)>,
}

impl InterpModel {
    // --- errors ---

    /// The name of the module containing `sp` (its file stem).
    /// TLC's source location: "line l, col c to line l2, col c2 of module M".
    pub fn location(&self, sp: Span) -> String {
        let l = self.location_parts(sp);
        l.to_string()
    }

    /// The parts of `location(sp)`.
    pub fn location_parts(&self, sp: Span) -> Location {
        self.range(sp, EndTrim::BlankAndComments)
    }

    /// The location of `sp` with its end taken by `trim` (the module is the
    /// file's name).
    pub fn range(&self, sp: Span, trim: EndTrim) -> Location {
        Location::of(self.ip.prog.file(sp.file), sp, trim, self.module_name(sp))
    }

    /// TLC's label of the initial state of a simulated behavior: the
    /// initial predicate's operator and location.
    pub fn init_label(&self) -> String {
        match &*self.init.kind {
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let def = &self.ip.prog.defs[d.idx()];
                let span = match &def.kind {
                    DefKind::Op(body) => body.span,
                    _ => def.span,
                };
                format!("{} {}", def.name, self.location(span))
            }
            _ => format!("Init {}", self.location(self.init.span)),
        }
    }

    /// The coverage label of the action expression at `pred` (expanded
    /// from definition `def`, `name`, applied from definition `from`), as
    /// TLC prints it (tlc2.tool.coverage.ActionWrapper.printLocation):
    /// `<Name declaration>` (see `declaration`) when `pred` is the
    /// definition's body; followed by `(bl bc el ec)`, the location of
    /// `pred`, when it is a part of it (a disjunct); `<Action location>`
    /// for an expression that is not from a definition. Also the location
    /// of `pred`, which identifies the coverage entry (TLC: the action's
    /// predicate node, so the instances of an action with different
    /// parameters share one) and orders the entries.
    fn coverage_label(&self, name: &str, def: Option<DefId>, from: Option<DefId>, pred: Span) -> (String, Location) {
        let at = self.location_parts(pred);
        let Some(d) = def else { return (format!("<Action {}>", self.location(pred)), at) };
        let decl = self.declaration(d, from);
        let decl_text = decl.to_string();
        // (The body of a definition seen from outside its instance is the
        // substitution node, at the INSTANCE statement.)
        let body = match (&self.ip.prog.defs[d.idx()].kind, self.crosses_instance(d, from)) {
            (_, Some(inst)) => Some(self.location_parts(inst)),
            (DefKind::Op(body), None) => Some(self.location_parts(body.span)),
            _ => None,
        };
        let label = match body {
            Some(b) if (b.begin, b.end, &b.module) == (at.begin, at.end, &at.module) => format!("<{name} {decl_text}>"),
            _ => format!("<{name} {decl_text} ({} {} {} {})>", at.begin.0, at.begin.1, at.end.0, at.end.1),
        };
        (label, at)
    }

    /// The INSTANCE statement of the context of definition `d`, if it is
    /// applied from outside that instance (from definition `from`, or the
    /// configuration).
    fn crosses_instance(&self, d: DefId, from: Option<DefId>) -> Option<Span> {
        let (ctx, at) = self.ip.prog.def_instance(d)?;
        let outer = from.and_then(|f| self.ip.prog.def_instance(f)).map(|(c, _)| c);
        (outer != Some(ctx)).then_some(at)
    }

    /// TLC's declaration of definition `d` applied from `from`: the head of
    /// the definition (`Op(p, q)`, before `==`), or the INSTANCE statement
    /// of a definition applied from outside its instance.
    fn declaration(&self, d: DefId, from: Option<DefId>) -> Location {
        if let Some(inst) = self.crosses_instance(d, from) {
            // (The name of a named instance, `I` of `I == INSTANCE M`.)
            return self.location_parts(self.ip.prog.def_instance_name_span(d).unwrap_or(inst));
        }
        let sp = self.ip.prog.defs[d.idx()].span;
        let src = &self.ip.prog.file(sp.file).src;
        let start = (sp.start as usize).min(src.len());
        let text = &src[start..(sp.end as usize).clamp(start, src.len())];
        // (A LOCAL definition's span starts at the keyword.)
        let skip =
            text.strip_prefix("LOCAL").filter(|r| r.starts_with(char::is_whitespace)).map_or(0, |r| text.len() - r.trim_start().len());
        let head = text[skip..].find("==").or_else(|| text[skip..].find('≜')).map_or(text.len(), |i| skip + i);
        let mut l = self.location_parts(Span { start: (start + skip) as u32, end: (start + head) as u32, ..sp });
        if skip > 0 {
            l.begin = self.ip.prog.file(sp.file).lines().line_col(start + skip);
        }
        l
    }

    /// TLC's coverage label and identifying location (see
    /// `coverage_label`) of action `i`.
    pub fn action_coverage(&self, i: usize) -> (String, Location) {
        // (Actions are never split inside an instance: a definition from
        // one is seen from outside it.)
        let a = &self.actions[i];
        self.coverage_label(&a.name, a.def, None, a.span())
    }

    /// TLC's coverage labels of the initial predicate (see
    /// `coverage_label`): one per conjunct of the behavior spec that is a
    /// state predicate (TLC's initial actions, in order).
    pub fn init_coverage(&self) -> Vec<String> {
        match &*self.init.kind {
            // (`behavior` conjoins the parts of the SPECIFICATION.)
            ExprKind::And(es) => {
                es.iter().enumerate().map(|(k, e)| self.init_part_coverage(e, self.init_within.get(k).copied().flatten())).collect()
            }
            _ => vec![self.init_part_coverage(&self.init, self.init_within.first().copied().flatten())],
        }
    }

    /// `within`: the INSTANCE statement the conjunct `e` of the
    /// SPECIFICATION is under (TLC sees it under the substitutions, located
    /// there).
    fn init_part_coverage(&self, e: &Expr, within: Option<Span>) -> String {
        if let ExprKind::Apply { op: OpRef::Def(d), args } = &*e.kind {
            let d = self.ip.redirect_def(*d);
            let def = &self.ip.prog.defs[d.idx()];
            if let (true, DefKind::Op(body)) = (args.is_empty(), &def.kind) {
                // (Under the substitutions, the definition is seen from
                // inside its instance.)
                if let Some(at) = within {
                    return self.coverage_label(&def.name, Some(d), Some(d), at).0;
                }
                // (Seen from outside its instance, the body is the
                // substitution node, at the INSTANCE.)
                let pred = self.crosses_instance(d, None).unwrap_or(body.span);
                return self.coverage_label(&self.ip.prog.def_qualified_name(d), Some(d), None, pred).0;
            }
        }
        self.coverage_label("Action", None, None, within.unwrap_or(e.span)).0
    }

    /// TLC's label of action `i` in traces: its name and the location of
    /// its definition's body (or of the action expression).
    pub fn action_label(&self, i: usize) -> String {
        let info = self.action_info(i);
        let mut name = info.name;
        if !info.params.is_empty() {
            name = format!("{name}({})", info.params.iter().map(|(_, v)| v.to_string()).collect::<Vec<_>>().join(","));
        }
        format!("{name} {}", self.location(self.actions[i].span()))
    }

    /// Action `i` as TLC describes it (its `Action`): the name, the
    /// location of its definition's body (or of the action expression), and
    /// the definition's parameters with their values (none if one has no
    /// value).
    pub fn action_info(&self, i: usize) -> ActionInfo {
        let a = &self.actions[i];
        let mut params = Vec::new();
        if let Some(d) = a.def {
            let args: Option<Vec<(String, Value)>> = self.ip.prog.defs[d.idx()]
                .params
                .iter()
                .map(|p| {
                    let v = match a.env.lookup(*p)? {
                        crate::env::Binding::Val(v) => v.clone(),
                        b @ (crate::env::Binding::Thunk(_) | crate::env::Binding::Name(..)) => {
                            let (e, env) = b.by_name(&self.ip.prog).unwrap();
                            self.ip.eval(e, env, &Ctx::NONE).ok()?
                        }
                        _ => return None,
                    };
                    Some((self.ip.prog.locals[p.idx()].name.to_string(), v))
                })
                .collect();
            params = args.unwrap_or_default();
        }
        ActionInfo { name: a.name.to_string(), location: self.location_parts(a.span()), params }
    }

    /// The variables of state `vals` with their values, in the order TLC
    /// shows them.
    pub fn state_fields<'v>(&self, vals: &'v [Value]) -> Vec<(&str, &'v Value)> {
        self.var_order(vals.len()).iter().map(|&i| (&*self.ip.prog.vars[i].name, &vals[i])).collect()
    }

    /// "Spec defined at line .. of module M" for the SPECIFICATION.
    pub fn specification_location(&self) -> Option<String> {
        let name = self.ip.cfg.specification.as_ref()?;
        let d = self.ip.root_def(name)?;
        Some(format!("{name} defined at {}", self.location(self.ip.prog.defs[d.idx()].span)))
    }

    /// Check the `_POSSIBLE` predicates, then the POSTCONDITIONs in order
    /// (after `Interp::set_final_stats`; TLC's Tool.checkPostConditions):
    /// the message for the first that fails.
    pub fn check_postcondition(&self) -> Result<Option<String>, ModelError> {
        use std::sync::atomic::Ordering;
        // (TLC has the value of a constant-level definition instead, and
        // checks that before evaluating any: Spec.getPostConditionSpecs.)
        if let Some((n, _)) = self.postconditions.iter().find(|(_, d)| spec::tlc_has_value(&self.ip, *d)) {
            return Err(ModelError::new(format!("The post condition {n} cannot be a constant.")));
        }
        for p in self.possible.iter() {
            if !p.witnessed.load(Ordering::Relaxed) {
                let label = self.def_label(&p.name, p.def);
                return Ok(Some(format!(
                    "The _POSSIBLE predicate {label} was never witnessed.\n\
                     Others may be unwitnessed too; only witnessed predicates appear with a\n\
                     non-zero count in the record printed above.\n\
                     See https://explain.tlapl.us/possible-conditions for additional details."
                )));
            }
        }
        for (i, (_, d)) in self.postconditions.iter().enumerate() {
            self.post_at.store(i, Ordering::Relaxed);
            let def = &self.ip.prog.defs[d.idx()];
            let e = Expr::new(ExprKind::Apply { op: OpRef::Def(*d), args: Vec::new() }, def.span);
            if !self.ip.eval_bool(&e, &Env::default(), &Ctx::NONE).map_err(|e| self.error(e))? {
                return Ok(self.postcondition_label().map(|l| format!("Postcondition {l} is false.")));
            }
        }
        Ok(None)
    }

    /// The POSTCONDITION checked last as TLC names it in its messages:
    /// `Post at line .. of module M` (the location of its definition's body).
    pub fn postcondition_label(&self) -> Option<String> {
        let (name, d) = self.postconditions.get(self.post_at.load(std::sync::atomic::Ordering::Relaxed))?;
        Some(self.def_label(name, *d))
    }

    /// `Name at line .. of module M` (the location of the body of `d`).
    fn def_label(&self, name: &str, d: DefId) -> String {
        let def = &self.ip.prog.defs[d.idx()];
        let span = match &def.kind {
            DefKind::Op(body) => body.span,
            _ => def.span,
        };
        format!("{name} at {}", self.location(span))
    }

    /// Whether there are state-level (`action` false) or action-level
    /// `_POSSIBLE` predicates: the states (steps) in the model must then be
    /// passed to `witness`.
    pub fn possible_pending(&self, action: bool) -> bool {
        self.possible.iter().any(|p| p.action == action)
    }

    /// Evaluate the `_POSSIBLE` predicates on state `s` (`t`: None) or step
    /// `s -> t`. Called for the states and steps that satisfy the
    /// CONSTRAINTs (ACTION_CONSTRAINTs), as TLC evaluates them last. As
    /// TLC's `_Possible!_Track`, each evaluation counts in the worker's
    /// named register `"s:_possible"` (a record: name -> number of times
    /// true), which `TLCGet("all:named")` shows.
    pub fn witness(&self, s: &State, t: Option<&State>) -> Result<(), ModelError> {
        use std::sync::atomic::Ordering;
        let t1: Vec<Option<Value>>;
        let cx = match t {
            Some(t) => {
                t1 = t.vals.iter().cloned().map(Some).collect();
                Ctx::action(&s.vals, &t1, s.level)
            }
            None => Ctx::state(&s.vals, s.level),
        };
        for p in self.possible.iter().filter(|p| p.action == t.is_some()) {
            let e = Expr::new(ExprKind::Apply { op: OpRef::Def(p.def), args: Vec::new() }, Span::default());
            let holds = self.ip.eval_bool(&e, &Env::default(), &cx).map_err(|e| self.error(e))?;
            if holds {
                p.witnessed.store(true, Ordering::Relaxed);
            }
            self.count_possible(&p.name, holds);
        }
        Ok(())
    }

    /// `_Possible!_Track`'s update of the register `"s:_possible"`.
    fn count_possible(&self, name: &str, holds: bool) {
        let key = crate::builtins::named_register(Sym::new("s:_possible"));
        let mut fields: Vec<(Sym, Value)> = match self.ip.get_register(key) {
            Some(Value::Record(fs)) => fs.to_vec(),
            _ => Vec::new(),
        };
        let name = Sym::new(name);
        match fields.iter_mut().find(|(k, _)| *k == name) {
            Some((_, Value::Int(n))) if holds => *n += 1,
            Some(_) => {}
            None => fields.push((name, Value::Int(i64::from(holds)))),
        }
        self.ip.set_register(key, Value::record(fields));
    }

    /// Recovering from a checkpoint: the `_POSSIBLE` predicates the
    /// checkpointed search witnessed, by their counts in its registers
    /// (`main`, then each worker's of `snaps`), as the states it expanded
    /// are not evaluated again.
    pub(super) fn restore_witnessed(&self, main: &[u8], snaps: &[Vec<u8>]) -> Result<(), String> {
        use std::sync::atomic::Ordering;
        let key = crate::builtins::named_register(Sym::new("s:_possible"));
        for b in std::iter::once(main).chain(snaps.iter().map(Vec::as_slice)).filter(|b| !b.is_empty()) {
            let Some(Value::Record(fs)) = crate::interp::read_registers(b)?.remove(&key) else { continue };
            for p in self.possible.iter() {
                if fs.iter().any(|(k, n)| k.as_str() == p.name && matches!(n, Value::Int(n) if *n > 0)) {
                    p.witnessed.store(true, Ordering::Relaxed);
                }
            }
        }
        Ok(())
    }

    /// State `s` (number `level` of a trace, followed by `next` if any) as
    /// TLC prints it in a counterexample: through the ALIAS if there is
    /// one, else through `-view`'s VIEW, else its variables; with
    /// `difftrace`, only the fields that differ from `prev` (State 1 has
    /// no predecessor and is shown in full).
    pub fn render_trace_state(
        &self,
        s: &[Value],
        level: u32,
        prev: Option<(&[Value], u32)>,
        next: Option<&[Value]>,
        opts: StateRenderOpts,
    ) -> String {
        self.render_state(s, level, prev, next, opts, true)
    }

    /// State `s` of a `-dump`: TLC's dumps ignore the ALIAS (they apply
    /// only `-view` and `-difftrace`).
    pub fn render_dump_state(&self, s: &[Value], level: u32, prev: Option<(&[Value], u32)>, opts: StateRenderOpts) -> String {
        self.render_state(s, level, prev, None, opts, false)
    }

    /// `render_trace_state`, with `alias` deciding whether the ALIAS is
    /// applied.
    fn render_state(
        &self,
        s: &[Value],
        level: u32,
        prev: Option<(&[Value], u32)>,
        next: Option<&[Value]>,
        opts: StateRenderOpts,
        alias: bool,
    ) -> String {
        let diff = opts.difftrace && prev.is_some();
        if alias {
            if let Some(fields) = self.alias_fields(s, next, level) {
                // The predecessor's version of the ALIAS state, whose primed
                // variables read the state that follows it: this one.
                let prev_fields = if diff {
                    prev.and_then(|(pv, pl)| tlx_runtime::live::with_predecessor_path(|| self.alias_fields(pv, Some(s), pl)))
                } else {
                    None
                };
                return render_fields(&fields, prev_fields.as_deref(), diff, true);
            }
        }
        if opts.use_view {
            if let Some(text) = self.render_view(s, level, prev, diff) {
                return text;
            }
        }
        let fields = self.state_fields(s);
        // A raw state of a single-variable model has no bullet; one of a
        // model with more variables keeps it for every line (as TLC).
        let prev_fields = prev.map(|(pv, _)| self.state_fields(pv));
        let raw = fields.iter().map(|(n, v)| (n.to_string(), (*v).clone())).collect::<Vec<_>>();
        let prev_owned = prev_fields.map(|p| p.iter().map(|(n, v)| (n.to_string(), (*v).clone())).collect::<Vec<_>>());
        render_fields(&raw, prev_owned.as_deref(), diff, false)
    }

    /// The fields of the ALIAS state of `s` (`next`: the state after it,
    /// whose values fill primed variables; the state itself when there is
    /// none): None without ALIAS or if it cannot be evaluated (then the
    /// state is shown as usual).
    fn alias_fields(&self, s: &[Value], next: Option<&[Value]>, level: u32) -> Option<Vec<(String, Value)>> {
        let alias = self.alias.as_ref()?;
        // In the last state, primed variables are read from the state itself.
        let t: Vec<Option<Value>> = next.unwrap_or(s).iter().cloned().map(Some).collect();
        let cx = Ctx::action(s, &t, level);
        let env = Env::default();
        match self.alias_record(alias) {
            Some(fs) => fs.iter().map(|(n, e)| Some((n.to_string(), self.ip.eval(e, &env, &cx).ok()?))).collect::<Option<_>>(),
            None => match self.ip.eval(alias, &env, &cx).ok().map(|v| v.fcn_canonical().unwrap_or(v))? {
                Value::Record(r) => Some(r.iter().map(|(n, v)| (n.as_str().to_string(), v.clone())).collect()),
                _ => None,
            },
        }
    }

    /// The value of the `-view` VIEW on `s` (`level`), if it is configured
    /// and evaluates.
    fn eval_view(&self, view: &Expr, s: &[Value], level: u32) -> Option<Value> {
        self.ip.eval(view, &Env::default(), &Ctx::state(s, level)).ok()
    }

    /// `s` shown through `-view`'s VIEW: a tuple VIEW whose components are
    /// the state variables is shown as `/\ variable = value` lines in
    /// declaration order (TLC's `OpApplNode.toString(IValue)`); any other
    /// value as itself. None without a VIEW or if it cannot be evaluated
    /// (then the state is shown as usual).
    fn render_view(&self, s: &[Value], level: u32, prev: Option<(&[Value], u32)>, diff: bool) -> Option<String> {
        // (`-optimize` installs a synthetic state projection in `view`; it
        // is not a user VIEW and must not be shown: concrete states stay
        // concrete in counterexamples, docs/configuration.md.)
        if self.state_projection {
            return None;
        }
        let view = self.view.as_ref()?;
        let v = self.eval_view(view, s, level)?;
        if let Some(fields) = self.view_fields(view, &v) {
            let mut text = None;
            if diff {
                if let Some((pv, pl)) = prev {
                    if let Some(pval) = tlx_runtime::live::with_predecessor_path(|| self.eval_view(view, pv, pl)) {
                        if let Some(prev_fields) = self.view_fields(view, &pval) {
                            text = Some(render_fields(&fields, Some(&prev_fields), true, true));
                        }
                    }
                }
            }
            return Some(text.unwrap_or_else(|| render_fields(&fields, None, false, true)));
        }
        // (TLC prints a non-tuple VIEW value as the value itself; with
        // `-difftrace` it is shown when it changed.)
        if diff {
            if let Some((pv, pl)) = prev {
                if tlx_runtime::live::with_predecessor_path(|| self.eval_view(view, pv, pl))
                    .is_some_and(|pval| tlx_value::order::certainly_equal(&pval, &v))
                {
                    return Some(String::new());
                }
            }
        }
        Some(v.to_string())
    }

    /// The fields a tuple `-view` VIEW displays for value `v`: the state
    /// variables its definition references, in declaration order, paired
    /// with the tuple's components. None when the VIEW is not a tuple or
    /// application, when `v` is not a tuple, or when the counts differ.
    fn view_fields(&self, view: &Expr, v: &Value) -> Option<Vec<(String, Value)>> {
        let vars = self.view_field_vars(view)?;
        let Value::Tuple(elems) = v else { return None };
        (elems.len() == vars.len())
            .then(|| vars.iter().zip(elems.iter()).map(|(&i, v)| (self.ip.prog.vars[i].name.to_string(), v.clone())).collect())
    }

    /// The state variables of the body of the `-view` VIEW (through
    /// zero-arity definitions, which TLC's free-parameter collection also
    /// follows), in declaration order. None when the body is not a tuple or
    /// an application (then there is no field layout to print).
    fn view_field_vars(&self, view: &Expr) -> Option<Vec<usize>> {
        let body = self.view_body(view)?;
        if !matches!(&*body.kind, ExprKind::Tuple(_) | ExprKind::Apply { .. }) {
            return None;
        }
        let mut vars = std::collections::BTreeSet::new();
        self.view_vars(body, &mut vars, &mut std::collections::HashSet::new());
        (!vars.is_empty()).then(|| vars.into_iter().collect())
    }

    /// The body of the `-view` VIEW (the reference the configuration
    /// resolved to the definition).
    fn view_body(&self, view: &Expr) -> Option<&Expr> {
        let ExprKind::Apply { op: OpRef::Def(d), args } = &*view.kind else { return None };
        if !args.is_empty() {
            return None;
        }
        match &self.ip.prog.defs[self.ip.redirect_def(*d).idx()].kind {
            DefKind::Op(body) => Some(body),
            _ => None,
        }
    }

    /// The state variables `e` references: its variable references and
    /// those of the zero-arity definitions it applies (TLC's `allParams`;
    /// the arguments of an application are its free variables, its
    /// definition's parameters are not).
    fn view_vars(&self, e: &Expr, vars: &mut std::collections::BTreeSet<usize>, seen: &mut std::collections::HashSet<usize>) {
        match &*e.kind {
            ExprKind::Var(v) => {
                vars.insert(v.idx());
            }
            // (A variable of an instantiated module: its unprimed reference
            // reads its substitution.)
            ExprKind::InstVar { subst, .. } => self.view_vars(subst, vars, seen),
            ExprKind::Apply { op: OpRef::Def(d), args } => {
                // (TLC's `allParams` adds the applied definition's free
                // parameters whatever its arity: the arguments are the
                // caller's free variables, and the definition's own free
                // variables stay free after substitution; its formal
                // parameters are `Local`s and are not state variables.)
                for a in args {
                    self.view_vars(a, vars, seen);
                }
                self.view_def_vars(*d, vars, seen);
            }
            ExprKind::OpArg(OpRef::Def(d)) => self.view_def_vars(*d, vars, seen),
            _ => tlx_sema::visit::children(e, &mut |c| self.view_vars(c, vars, seen)),
        }
    }

    /// The state variables of definition `d`: its body (following the
    /// bounds and body of a function definition). `seen` breaks recursion.
    fn view_def_vars(&self, d: DefId, vars: &mut std::collections::BTreeSet<usize>, seen: &mut std::collections::HashSet<usize>) {
        let d = self.ip.redirect_def(d);
        if !seen.insert(d.idx()) {
            return;
        }
        match &self.ip.prog.defs[d.idx()].kind {
            DefKind::Op(body) => self.view_vars(body, vars, seen),
            DefKind::Fn { bounds, body } => {
                for b in bounds {
                    self.view_vars(&b.set, vars, seen);
                }
                self.view_vars(body, vars, seen);
            }
            DefKind::Pending => {}
        }
    }

    /// The fields of an ALIAS defined as a record constructor.
    fn alias_record(&self, alias: &Expr) -> Option<Vec<(Arc<str>, Expr)>> {
        let ExprKind::Apply { op: OpRef::Def(d), args } = &*alias.kind else { return None };
        if !args.is_empty() {
            return None;
        }
        let (_, body) = self.ip.plain_op_body(*d)?;
        match &*body.kind {
            ExprKind::Record(fs) => Some(fs.clone()),
            _ => None,
        }
    }

    fn module_name(&self, sp: Span) -> String {
        module_name(&self.ip, sp)
    }

    /// Format an evaluation error with its source location.
    pub fn error(&self, e: EvalError) -> ModelError {
        match e.span {
            // (TLC's errors of a specific kind do not show a location.)
            Some(sp) if matches!(e.kind, tlx_runtime::ErrorKind::General | tlx_runtime::ErrorKind::FunctionDomain) => {
                ModelError::of_kind(e.kind, format!("{}\n{}", e.message, tlx_sema::source::begin_text(sp, &self.module_name(sp))))
            }
            _ => ModelError::of_kind(e.kind, e.into_message()),
        }
    }
}
