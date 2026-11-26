//! Binding the `.cfg` file to a resolved program: CONSTANT values,
//! `Def = value` / `Def <- Other` overrides, and TLC's interning order.

use std::collections::HashMap;

use tlx_front::ast::FileId;
use tlx_front::cfg::{CfgValue, Config, ConstBinding};
use tlx_sema::hir::*;
use tlx_sema::Program;
use tlx_value::{Sym, Value};

use super::ConstVal;
use crate::error::{EResult, EvalError};

/// Convert a cfg literal to a value.
pub fn cfg_value(v: &CfgValue) -> EResult<Value> {
    Ok(match v {
        CfgValue::Int(i) => Value::Int(*i),
        CfgValue::Str(s) => Value::Str(Sym::new(s)),
        CfgValue::Bool(b) => Value::Bool(*b),
        CfgValue::ModelValue(m) => Value::ModelValue(Sym::new(m)),
        CfgValue::Set(es) => {
            // TLC builds configuration sets in a growing `ValueVec`, so
            // `-maxSetSize` applies to the raw cfg entries before deduplication
            // (unlike TLA+ source set literals, which preallocate their length).
            tlx_value::limits::check_set_size(es.len())?;
            Value::set_from(es.iter().map(cfg_value).collect::<EResult<_>>()?)?
        }
        CfgValue::Tuple(es) => Value::tuple(es.iter().map(cfg_value).collect::<EResult<_>>()?),
    })
}

/// All definition names a cfg refers to.
pub fn cfg_names(cfg: &Config) -> Vec<String> {
    let singles = [&cfg.init, &cfg.next, &cfg.specification];
    let lists = [&cfg.invariants, &cfg.properties, &cfg.constraints, &cfg.action_constraints];
    let tail = [&cfg.symmetry, &cfg.view, &cfg.alias];
    let names = singles.into_iter().flatten().chain(lists.into_iter().flatten()).chain(tail.into_iter().flatten());
    names.chain(&cfg.postconditions).chain(&cfg.possible).cloned().collect()
}

/// Intern the model values and strings of the cfg in order of appearance,
/// as TLC does before parsing the spec (tlc-semantics.md §1.3).
pub(super) fn intern_cfg(cfg: &Config) {
    fn walk(v: &CfgValue) {
        match v {
            CfgValue::Str(s) | CfgValue::ModelValue(s) => {
                Sym::new(s);
            }
            CfgValue::Set(es) | CfgValue::Tuple(es) => es.iter().for_each(walk),
            _ => {}
        }
    }
    for b in &cfg.constants {
        match b {
            ConstBinding::Value { value, .. } => walk(value),
            ConstBinding::OpValue { args, value, .. } => args.iter().chain([value]).for_each(walk),
            ConstBinding::Subst { .. } => {}
        }
    }
}

/// Intern source tokens in parse order, then string literals in dependency
/// order (standard modules first, root last), approximating TLC.
pub(super) fn intern_sources(prog: &mut Program) {
    let (parse, semantic) = prog.sany_file_orders();
    let texts: Vec<_> = prog.files.iter().map(|f| tlx_front::parse::token_texts(&f.src)).collect();
    // Files loaded otherwise (not reached from the root) come last.
    let rest = |order: &[FileId]| (0..texts.len() as u32).map(FileId).filter(|f| !order.contains(f)).collect::<Vec<_>>();
    for f in parse.iter().chain(&rest(&parse)) {
        for t in &texts[f.0 as usize].0 {
            Sym::new(t);
        }
    }
    for f in semantic.iter().chain(&rest(&semantic)) {
        for t in &texts[f.0 as usize].1 {
            Sym::new(t);
        }
    }
}

/// What the cfg binds: CONSTANT values and definition overrides.
pub(super) struct CfgBindings {
    pub consts: Vec<Option<ConstVal>>,
    /// `Def = value`.
    pub def_value: HashMap<DefId, Value>,
    /// `Def <- Other`.
    pub def_redirect: HashMap<DefId, DefId>,
}

/// Resolve the CONSTANT section of `cfg` against `prog`.
pub(super) fn bind_cfg(prog: &mut Program, cfg: &Config) -> EResult<CfgBindings> {
    let mut out = CfgBindings { consts: vec![None; prog.consts.len()], def_value: HashMap::new(), def_redirect: HashMap::new() };
    // Resolve everything the cfg refers to first: definitions inside module
    // instances only exist once resolved, and module-scoped overrides
    // (`F <- [M] G`) must find them.
    for n in cfg_names(cfg) {
        prog.lookup_root(&n);
    }
    // Values first: `C <- D` may name a constant D assigned a value.
    for b in &cfg.constants {
        match b {
            ConstBinding::Value { name, value, module } => bind_value(prog, &mut out, name, cfg_value(value)?, module.as_deref()),
            ConstBinding::OpValue { name, args, value } => bind_op_value(prog, &mut out, name, args, value)?,
            ConstBinding::Subst { .. } => {}
        }
    }
    for b in &cfg.constants {
        let ConstBinding::Subst { name, op, module } = b else { continue };
        if let (Some(RootSymbol::Const(c)), None) = (prog.lookup_root(op), module) {
            // `C <- D` for a constant D: C takes D's binding.
            match out.consts[c.idx()].clone() {
                Some(ConstVal::Value(v)) => bind_value(prog, &mut out, name, v, None),
                Some(ConstVal::Def(t) | ConstVal::Op(OpRef::Def(t))) => bind_subst(prog, &mut out, name, t, None)?,
                _ => return Err(EvalError::new(format!("cfg: the constant `{op}` substituted for `{name}` has no value"))),
            }
            continue;
        }
        let target = lookup_def(prog, op)?;
        bind_subst(prog, &mut out, name, target, module.as_deref())?;
    }
    bind_entries(prog, &mut out);
    Ok(out)
}

/// The entry definitions (`I!Op`, imports of an anonymous INSTANCE; see
/// `Program::entry_def`) that no override binds: an alias of the definition
/// they stand for if that is not overridden either, else (it is a different
/// node, docs/compat.md D-23) its original body.
fn bind_entries(prog: &mut Program, out: &mut CfgBindings) {
    let bound = |out: &CfgBindings, d: &DefId| out.def_value.contains_key(d) || out.def_redirect.contains_key(d);
    let entries: Vec<(DefId, DefId)> = prog.entry_defs().into_iter().filter(|(e, _)| !bound(out, e)).collect();
    let (alias, own): (Vec<_>, Vec<_>) = entries.into_iter().partition(|(_, d)| !bound(out, d));
    for (e, _) in own {
        prog.require(e);
    }
    for (e, d) in alias {
        out.def_redirect.insert(e, d);
    }
}

fn lookup_def(prog: &mut Program, name: &str) -> EResult<DefId> {
    match prog.lookup_root(name) {
        Some(RootSymbol::Def(d)) => Ok(d),
        _ => Err(EvalError::new(format!("cfg: `{name}` is not a definition of the spec"))),
    }
}

/// `name = v` or `name = [M] v`.
///
/// TLC (`SpecProcessor.processConfig`) looks the name up among the constants
/// and definitions of the root module (and its EXTENDS closure) and assigns
/// only what it finds there; an assignment that names something else — an
/// undeclared name, a variable, a definition that only exists inside an
/// INSTANCEd module, or a module-scoped form naming an unknown module or a
/// name that module does not define — is silently ignored.
fn bind_value(prog: &mut Program, out: &mut CfgBindings, name: &str, v: Value, module: Option<&str>) {
    match (module, prog.lookup_root(name)) {
        (None, Some(RootSymbol::Const(c))) => out.consts[c.idx()] = Some(ConstVal::Value(v)),
        (None, Some(RootSymbol::Def(d))) => {
            for d in prog.def_copies(d) {
                out.def_value.insert(d, v.clone());
            }
        }
        (None, _) => {}
        // `c = [M] v`: the definitions of that name in module M.
        (Some(m), _) => {
            let ds = prog.lookup_in_module(m, name);
            for d in prog.with_entries(ds) {
                out.def_value.insert(d, v.clone());
            }
        }
    }
}

/// `F(a1, ..., an) = v`: one entry of operator constant F's table (TLC's
/// SpecProcessor.makeConstantTable: all entries take the same number of
/// arguments). Other names are ignored, as by `bind_value`.
fn bind_op_value(prog: &mut Program, out: &mut CfgBindings, name: &str, args: &[CfgValue], v: &CfgValue) -> EResult<()> {
    let Some(RootSymbol::Const(c)) = prog.lookup_root(name) else { return Ok(()) };
    let args = args.iter().map(cfg_value).collect::<EResult<Vec<_>>>()?;
    let v = cfg_value(v)?;
    match &mut out.consts[c.idx()] {
        Some(ConstVal::Table(rows)) => {
            if rows.first().is_some_and(|(a, _)| a.len() != args.len()) {
                return Err(EvalError::new(format!(
                    "The operator {name} is given different numbers of arguments in the configuration file."
                )));
            }
            std::sync::Arc::make_mut(rows).push((args, v));
        }
        slot => *slot = Some(ConstVal::Table(std::sync::Arc::new(vec![(args, v)]))),
    }
    Ok(())
}

/// `name <- target` or `name <- [M] target`.
fn bind_subst(prog: &mut Program, out: &mut CfgBindings, name: &str, target: DefId, module: Option<&str>) -> EResult<()> {
    if let Some(m) = module {
        // `F <- [M] G`: override F as defined in module M (all instances,
        // also `I!F`: TLC overrides the body, which those nodes share).
        let ds = prog.lookup_in_module(m, name);
        if ds.is_empty() {
            return Err(EvalError::new(format!("cfg: module {m} has no definition `{name}`")));
        }
        for d in prog.with_entries(ds) {
            out.def_redirect.insert(d, target);
        }
        return Ok(());
    }
    match prog.lookup_root(name) {
        Some(RootSymbol::Const(c)) => {
            let cv = if prog.consts[c.idx()].arity == 0 { ConstVal::Def(target) } else { ConstVal::Op(OpRef::Def(target)) };
            out.consts[c.idx()] = Some(cv);
        }
        Some(RootSymbol::Def(d)) => {
            // Also inside every instance of the defining module (TLC
            // overrides the OpDefNode their bodies share), but not `I!F`
            // (docs/compat.md D-23).
            for d in prog.def_copies(d) {
                out.def_redirect.insert(d, target);
            }
        }
        _ => {
            let ds = prog.defs_named(name);
            if ds.is_empty() {
                return Err(EvalError::new(format!("cfg: unknown constant `{name}`")));
            }
            for d in ds {
                out.def_redirect.insert(d, target);
            }
        }
    }
    Ok(())
}
