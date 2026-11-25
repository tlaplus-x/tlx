//! C code generation from typed IR (design.md §6.7).
//!
//! Without mixed mode only fully typed, C-compatible actions/predicates are
//! generated; the others make the generated function return
//! `TLX_UNSUPPORTED`, and the host runs them through the IR executor /
//! interpreter. Any runtime problem in generated code (overflow, argument
//! outside a function's domain, value not fitting a layout) returns
//! `TLX_ERR`: the host then discards that call's buffered successors and
//! re-runs the (state, action) pair in the interpreter, which reproduces
//! TLC's exact behaviour.
//!
//! Mixed mode (docs/mixed-mode.md §4, `CGen::with_mixed`): an expression
//! C cannot compile becomes a *region* that the host evaluates through
//! `host->eval` (the IR executor on the call's states); the library's
//! regions are returned in its `RegionTable`. A region failing is a runtime
//! error like any other (`TLX_ERR`).
//!
//! Representation: Bool/Int are `int64_t`; encoded values are
//! `const uint64_t *` pointing into the states, static constants, or
//! function-scope buffers; boxed values (mixed mode) are `uint64_t` handles,
//! valid until the generated function returns (loops whose bodies make
//! handles release them after each iteration). Expressions use GCC/clang
//! statement expressions.
//!
//! Statements are generated in `stmt`, expressions in `expr`, region calls
//! in `region`.

mod expr;
mod region;
mod stmt;

use std::collections::HashMap;
use std::fmt::Write;
use std::sync::Arc;

use tlx_base::diag::{self, Topic};
use tlx_layout::Shape;

use crate::enc::mixed::RegionCtx;
use crate::ir::*;
use crate::native_plan::{Mixed, NativePlan, NativeSet, RegionBuilder};
use crate::types::Typing;

/// Return code of a generated function that is not implemented natively.
pub const UNSUPPORTED: i32 = tlx_native::native::UNSUPPORTED;

/// Helpers shared by generated code (TLC's 32-bit integer semantics,
/// bitsets, sorted-array sets).
const RUNTIME: &str = include_str!("runtime.h");

/// Why an IR construct has no C translation.
pub struct Unsupported(pub String);

type R<T> = Result<T, Unsupported>;

fn no<T>(msg: impl Into<String>) -> R<T> {
    Err(Unsupported(msg.into()))
}

/// A generated C translation unit, and the plan it implements (which the
/// JIT follows).
pub struct Library {
    pub src: String,
    pub plan: NativePlan,
}

/// Generates one C translation unit.
pub struct CGen<'a> {
    ty: &'a Typing,
    verified: &'a crate::verify::Program<'a>,
    /// File-scope constant arrays.
    statics: String,
    nstatic: usize,
    /// Deduplication tables for file-scope static arrays (rollback-safe via `*_keys`).
    static_u64_dedup: HashMap<Vec<u64>, String>,
    static_u64_keys: Vec<Vec<u64>>,
    static_arr_dedup: HashMap<(&'static str, Vec<String>, &'static str), String>,
    static_arr_keys: Vec<(&'static str, Vec<String>, &'static str)>,
    // Per-function state.
    /// Declarations of the function-scope buffers.
    bufs: String,
    nbuf: usize,
    /// Counter for fresh local names.
    ntmp: usize,
    temps: Vec<Ty>,
    /// Inside `ENABLED`: regions see the local scratch next state.
    in_enabled: bool,
    /// Redirect `Stmt::Emit` to `{ flag = 1; goto label; }` (inside `ENABLED` or `Stmt::Then::first`).
    emit_target: Option<(String, String)>,
    /// Which compiled functions (`Typing::funcs`) are native.
    fn_native: Vec<bool>,
    /// Generating the body of a compiled function.
    in_fn: bool,
    /// Mixed mode (None: off).
    mixed: Option<Mixed<'a>>,
    /// The regions of the library so far, and their call sites.
    regions: RegionBuilder,
    /// The current function may call regions (mixed mode, and a pure
    /// action or predicate).
    mixing: bool,
    /// The current function's name, its temps (shared by its regions) and
    /// the context of its regions.
    fn_name: Arc<str>,
    fn_temps: Arc<[Ty]>,
    rctx: RegionCtx,
    /// Next-state variables statically assigned at the current point (of
    /// the `ENABLED`'s next state inside one).
    assigned: Vec<bool>,
    /// Region calls making handles, emitted so far.
    handles: usize,
    /// Nodes eligible for `Mixed::force` seen so far.
    nforce: u64,
    /// Native functions calling regions so far.
    mixed_fns: usize,
    /// The temps bound in each enclosing statement loop body (its element
    /// and what is computed from it), innermost last (mixed mode).
    stmt_loops: Vec<std::collections::HashSet<Temp>>,
    /// The current function has a region in a statement loop body that
    /// depends on the loop's element (see `check_loop_regions`).
    loop_region: bool,
    /// The value store operations the code may call (`host->ref_op`).
    refops: Option<Arc<crate::exec::refops::RefOpTable>>,
}

/// C name of an IR temporary.
fn temp(t: Temp) -> String {
    format!("t{t}")
}

impl<'a> CGen<'a> {
    pub fn new(verified: &'a crate::verify::Program<'a>) -> CGen<'a> {
        CGen {
            ty: verified.typing(),
            verified,
            statics: String::new(),
            nstatic: 0,
            static_u64_dedup: HashMap::new(),
            static_u64_keys: Vec::new(),
            static_arr_dedup: HashMap::new(),
            static_arr_keys: Vec::new(),
            bufs: String::new(),
            nbuf: 0,
            ntmp: 0,
            temps: Vec::new(),
            in_enabled: false,
            emit_target: None,
            fn_native: Vec::new(),
            in_fn: false,
            mixed: None,
            regions: RegionBuilder::default(),
            mixing: false,
            fn_name: Arc::from(""),
            fn_temps: Arc::from([]),
            rctx: RegionCtx::Action,
            assigned: Vec::new(),
            handles: 0,
            nforce: 0,
            mixed_fns: 0,
            stmt_loops: Vec::new(),
            loop_region: false,
            refops: None,
        }
    }

    /// Generate calls of the value store operations of `table` (the
    /// table of the program, `RefOpTable::of`).
    pub fn with_refops(mut self, table: Option<Arc<crate::exec::refops::RefOpTable>>) -> CGen<'a> {
        self.refops = table;
        self
    }

    /// Generate in mixed mode: what C cannot compile in actions, Init and
    /// predicates becomes host regions.
    pub fn with_mixed(mut self, m: Mixed<'a>) -> CGen<'a> {
        self.mixed = Some(m);
        self
    }

    /// Generate the whole library: one function per action, invariant and
    /// action property (or a stub), plus the ABI entry points.
    pub fn library(&mut self, action_names: &[String], inv_names: &[String]) -> Library {
        let init = self.verified.init();
        let actions = self.verified.actions();
        let invariants = self.verified.predicates();
        let aprops = self.verified.transitions();
        let words = self.ty.layout.words;
        let s1 = format!("  uint64_t s1[{}];\n", words.max(1));
        let mut funcs = self.functions();
        let mut native = NativeSet::default();

        // (A function is mixed if it is native and made regions.)
        let r0 = self.regions.len();
        let body = init.ok_or(Unsupported("not lowered".into())).and_then(|f| self.action(f, RegionCtx::Init));
        // No current state (regions take one).
        let prologue = format!("{s1}  memset(s1, 0, sizeof s1);\n  const uint64_t *s0 = 0; (void)s0;\n");
        native.init =
            self.define(&mut funcs, "static int init_fn(const tlx_host *h, tlx_ctx *cx)", body, &prologue, "  return TLX_OK;\n", || {
                "Init".into()
            });
        native.mixed_init = native.init && self.regions.len() > r0;
        for (i, a) in actions.iter().enumerate() {
            let r0 = self.regions.len();
            let body = a.as_ref().ok_or(Unsupported("not lowered".into())).and_then(|f| self.action(f, RegionCtx::Action));
            let sig = format!("static int act_{i}(const tlx_host *h, tlx_ctx *cx, const uint64_t *s0)");
            let what = || format!("action {}", action_names.get(i).map_or("?", |s| s.as_str()));
            let ok = self.define(&mut funcs, &sig, body, &s1, "  return TLX_OK;\n", what);
            native.actions.push(ok);
            native.mixed_actions.push(ok && self.regions.len() > r0);
        }
        for (i, p) in invariants.iter().enumerate() {
            let r0 = self.regions.len();
            let body = self.pred(p, RegionCtx::StatePred);
            let sig = format!("static int inv_{i}(const tlx_host *h, tlx_ctx *cx, const uint64_t *s0)");
            let what = || format!("invariant {}", inv_names.get(i).map_or("?", |s| s.as_str()));
            // No next state (compiled functions and regions take one).
            let prologue = "  const uint64_t *s1 = 0; (void)s1;\n";
            let ok = self.define(&mut funcs, &sig, body, prologue, "", what);
            native.invariants.push(ok);
            native.mixed_invariants.push(ok && self.regions.len() > r0);
        }
        for (i, p) in aprops.iter().enumerate() {
            let r0 = self.regions.len();
            let body = self.pred(p, RegionCtx::TransPred);
            let sig = format!("static int aprop_{i}(const tlx_host *h, tlx_ctx *cx, const uint64_t *s0, const uint64_t *s1)");
            let ok = self.define(&mut funcs, &sig, body, "", "", || format!("action property {}", p.name));
            native.action_properties.push(ok);
            native.mixed_action_properties.push(ok && self.regions.len() > r0);
        }
        native.mixed = self.mixed_fns;
        let (regions, sites) = self.regions.finish(self.ty);

        let mut src = String::new();
        if !regions.is_empty() {
            // What the regions are is part of what the library means: in
            // the source, it is part of the build cache key. (Their
            // description itself can be hundreds of MB: its hashes.)
            writeln!(src, "/* host regions: {}, digest {} */", regions.len(), regions.digest()).unwrap();
        }
        if let Some(t) = &self.refops {
            // (Likewise the value store operations the code calls by id.)
            writeln!(src, "/* value store operations:\n{}*/", t.text()).unwrap();
        }
        src.push_str("#include <stdint.h>\n#include <string.h>\n#include \"tlx_abi.h\"\n");
        writeln!(src, "#define TLX_UNSUPPORTED ({UNSUPPORTED})\n").unwrap();
        src.push_str(RUNTIME);
        src.push_str(&self.statics);
        src.push_str(&funcs);
        let quote = |s: &String| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""));
        let names = |v: &[String]| {
            if v.is_empty() {
                "{0}".to_string()
            } else {
                format!("{{{}}}", v.iter().map(quote).collect::<Vec<_>>().join(", "))
            }
        };
        writeln!(src, "static const char *act_names[] = {};", names(action_names)).unwrap();
        writeln!(src, "static const char *inv_names[] = {};", names(inv_names)).unwrap();
        writeln!(src, "static const char *err_msgs[] = {{\"runtime error\"}};").unwrap();
        writeln!(
            src,
            "static const tlx_spec_info info = {{TLX_ABI_VERSION, {words}, {}, {}, act_names, inv_names, 1, err_msgs, {}, {}ULL, {}, {}ULL}};",
            action_names.len(),
            inv_names.len(),
            regions.len(),
            if regions.is_empty() { 0 } else { regions.hash() },
            self.refops.as_ref().map_or(0, |t| tlx_native::mixed::RefOps::len(&**t)),
            self.refops.as_ref().map_or(0, |t| tlx_native::mixed::RefOps::hash(&**t))
        )
        .unwrap();
        src.push_str("const tlx_spec_info *tlx_info(void) { return &info; }\n");
        src.push_str("int tlx_init(const tlx_host *h, tlx_ctx *cx) { return init_fn(h, cx); }\n");
        dispatch(&mut src, "int tlx_next(const tlx_host *h, tlx_ctx *cx, const uint64_t *s, uint32_t a)", "a", actions.len(), |i| {
            format!("act_{i}(h, cx, s)")
        });
        dispatch(
            &mut src,
            "int tlx_invariant(const tlx_host *h, tlx_ctx *cx, const uint64_t *s, uint32_t i)",
            "i",
            invariants.len(),
            |i| format!("inv_{i}(h, cx, s)"),
        );
        dispatch(
            &mut src,
            "int tlx_action_property(const tlx_host *h, tlx_ctx *cx, const uint64_t *s, const uint64_t *t, uint32_t i)",
            "i",
            aprops.len(),
            |i| format!("aprop_{i}(h, cx, s, t)"),
        );
        Library { src, plan: NativePlan { native, regions, sites } }
    }

    /// Define the C function `sig` with `body` between `prologue` and
    /// `epilogue`, or, if there is no body, as a stub returning
    /// `TLX_UNSUPPORTED`. Returns whether the function is native.
    fn define(
        &self,
        funcs: &mut String,
        sig: &str,
        body: R<String>,
        prologue: &str,
        epilogue: &str,
        what: impl FnOnce() -> String,
    ) -> bool {
        match body {
            Ok(b) => {
                writeln!(funcs, "{sig} {{\n{prologue}{b}{epilogue}}}\n").unwrap();
                true
            }
            Err(Unsupported(why)) => {
                diag::emit_with(Topic::Cgen, || format!("{} not native: {why}", what()));
                writeln!(funcs, "{sig} {{ return {UNSUPPORTED}; }}\n").unwrap();
                false
            }
        }
    }

    /// The compiled functions that can be native (prototypes, then
    /// definitions). A function calling a non-native one is not native;
    /// the round is the shared rejection fixpoint
    /// (`fast::rejection_fixpoint`), and this backend owns the probe
    /// (`self.function`), the mask and the diagnostics.
    fn functions(&mut self) -> String {
        let n = self.ty.funcs.len();
        self.fn_native = vec![true; n];
        let mut defs = vec![String::new(); n];
        // `self.function(i)` is probe and definition pass in one: a round
        // that rejects `i` has cleared `fn_native[i]` and named the reason,
        // and the next round re-probes the survivors (a call to a function
        // rejected now fails the call-site check in `expr`).
        crate::exec::fast::rejection_fixpoint(|| {
            let mut changed = false;
            #[allow(clippy::needless_range_loop)] // `i` is also the function index passed to `self.function(i)`
            for i in 0..n {
                if !self.fn_native[i] {
                    continue;
                }
                match self.function(i) {
                    Ok(d) => defs[i] = d,
                    Err(Unsupported(why)) => {
                        diag::emit(Topic::Cgen, format_args!("function {} not native: {why}", self.ty.funcs[i].name));
                        self.fn_native[i] = false;
                        changed = true;
                    }
                }
            }
            changed
        });
        let mut out = String::new();
        for i in (0..n).filter(|i| self.fn_native[*i]) {
            writeln!(out, "{};", self.fn_signature(i).unwrap_or_default()).unwrap();
        }
        for i in (0..n).filter(|i| self.fn_native[*i]) {
            out.push_str(&defs[i]);
        }
        out
    }

    /// C signature of compiled function `i`: the states, the call depth,
    /// the parameters and the result slot; returns TLX_OK or TLX_ERR.
    fn fn_signature(&self, i: usize) -> R<String> {
        let f = &self.ty.funcs[i];
        let mut parts = vec![
            "const uint64_t *s0".to_string(),
            "const uint64_t *s1".to_string(),
            "int depth".to_string(),
            "uint64_t *calls".to_string(),
        ];
        for p in &f.params {
            parts.push(format!("{} {}", self.c_ty(f.temps[*p as usize])?, temp(*p)));
        }
        parts.push(match f.ret {
            Ty::Bool | Ty::Int => "int64_t *out_".to_string(),
            Ty::Enc(_) => "uint64_t *out_".to_string(),
            Ty::Val => return no("boxed result"),
        });
        Ok(format!("static int fn_{i}({})", parts.join(", ")))
    }

    /// Definition of compiled function `i`.
    fn function(&mut self, i: usize) -> R<String> {
        let f = self.ty.funcs[i].clone();
        let sig = self.fn_signature(i)?;
        self.reset(&f.temps);
        self.in_fn = true;
        let body = self.expr(&f.body);
        self.in_fn = false;
        let body = body?;
        let set = match f.ret {
            Ty::Enc(sid) => format!("memcpy(out_, {body}, {} * 8)", self.words(sid)),
            _ => format!("*out_ = {body}"),
        };
        let budget = if f.budgeted {
            format!("  if (++*calls > {}) return TLX_ERR;\n", crate::exec::eval::MAX_BUDGETED_CALLS)
        } else {
            String::new()
        };
        Ok(format!(
            "{sig} {{
  if (depth > {}) return TLX_ERR;
{budget}{}  {set};
  return TLX_OK;
}}

",
            crate::exec::eval::MAX_CALL_DEPTH,
            self.bufs
        ))
    }

    fn reset(&mut self, temps: &[Ty]) {
        self.bufs.clear();
        self.nbuf = 0;
        self.ntmp = 0;
        self.temps = temps.to_vec();
        self.assigned = vec![false; self.ty.layout.vars.len()];
    }

    /// Start generating an action or predicate `name` with `temps` whose
    /// regions are called in context `ctx`; regions only if `mixing`.
    fn begin_fn(&mut self, name: &Arc<str>, temps: &[Ty], ctx: RegionCtx, mixing: bool) -> usize {
        self.reset(temps);
        self.mixing = mixing;
        self.loop_region = false;
        self.fn_name = name.clone();
        self.fn_temps = temps.into();
        self.rctx = ctx;
        self.regions.len()
    }

    /// Done generating the function begun by `begin_fn` (which returned
    /// `start`): its regions are dropped unless it is native.
    fn end_fn(&mut self, start: usize, native: bool) {
        if !native {
            self.regions.truncate(start);
        } else if self.regions.len() > start {
            self.mixed_fns += 1;
        }
        self.mixing = false;
    }

    /// Body of an action / Init function (emits into `s1`).
    fn action(&mut self, f: &ActionFn, ctx: RegionCtx) -> R<String> {
        let init = matches!(ctx, RegionCtx::Init);
        let mixing = self.mixed.as_ref().is_some_and(|m| if init { m.oracle.mixes_action(f) } else { m.oracle.mixes_next(f) });
        let start = self.begin_fn(&f.name, &f.temps, ctx, mixing);
        let mut body = String::new();
        let r = self.stmt(&f.body, 1, &mut body).and_then(|()| self.check_loop_regions());
        self.end_fn(start, r.is_ok());
        r?;
        Ok(format!("{}{}", self.bufs, body))
    }

    /// A statement loop whose body calls a region depending on the element
    /// calls the host once per element, each time converting what the
    /// region reads: such functions were measured slower than running them
    /// in the interpreter as a whole (TLCSailfish1, docs/mixed-mode.md
    /// §5.1). They are not mixed, unless `Mixed::loops` or `Mixed::force`.
    /// Init is never mixed so (unless forced): it runs once, so adaptive
    /// tiering cannot pick its faster path, and an Init enumerating many
    /// states is faster in the IR executor (SimTokenRing,
    /// CoffeeCan1000Beans 1.13-1.17x slower mixed).
    fn check_loop_regions(&self) -> R<()> {
        let init = matches!(self.rctx, RegionCtx::Init);
        if self.loop_region && self.mixed.as_ref().is_some_and(|m| (!m.loops || init) && m.force == 0) {
            return no("a region in a statement loop depends on the element");
        }
        Ok(())
    }

    /// Body of a predicate function (returns 1 or 0) over states `ctx`.
    fn pred(&mut self, p: &PredFn, ctx: RegionCtx) -> R<String> {
        if self.mixed.as_ref().is_some_and(|m| m.oracle.mixes_pred(p)) {
            let start = self.begin_fn(&p.name, &p.temps, ctx, true);
            let r = self.bool_expr(&p.body).and_then(|c| self.check_loop_regions().map(|()| c));
            self.end_fn(start, r.is_ok());
            match r {
                Ok(c) => return Ok(format!("{}  return ({c}) ? 1 : 0;\n", self.bufs)),
                Err(Unsupported(why)) => diag::emit(Topic::Cgen, format_args!("predicate {} not mixed: {why}", p.name)),
            }
        }
        self.reset(&p.temps);
        match self.bool_expr(&p.body) {
            Ok(c) => return Ok(format!("{}  return ({c}) ? 1 : 0;\n", self.bufs)),
            Err(Unsupported(why)) => diag::emit(Topic::Cgen, format_args!("predicate {} only partly native: {why}", p.name)),
        }
        // Decide what the native prefix of the predicate can decide; the
        // rest is left to the interpreter (TLX_UNSUPPORTED).
        let code = self.pred_prefix(&p.body)?;
        Ok(format!("{}{code}", self.bufs))
    }

    /// C statements deciding `e` from its leading natively compilable
    /// conjuncts / disjuncts (in TLC's evaluation order), returning 1 / 0,
    /// or TLX_UNSUPPORTED where the interpreter must take over.
    fn pred_prefix(&mut self, e: &Expr) -> R<String> {
        if let Ok(c) = self.bool_expr(e) {
            return Ok(format!("  return ({c}) ? 1 : 0;\n"));
        }
        let mut out = String::new();
        match &*e.kind {
            ExprKind::And(xs) | ExprKind::Or(xs) => {
                let and = matches!(&*e.kind, ExprKind::And(_));
                let mut decided = 0;
                for x in xs {
                    match self.bool_expr(x) {
                        Ok(c) if and => out.push_str(&format!("  if (!({c})) return 0;\n")),
                        Ok(c) => out.push_str(&format!("  if ({c}) return 1;\n")),
                        Err(_) => break,
                    }
                    decided += 1;
                }
                if decided == 0 {
                    return no("predicate without a native prefix");
                }
                out.push_str("  return TLX_UNSUPPORTED;\n");
            }
            ExprKind::Let { temp: t, value, body } => {
                let ct = self.c_ty(value.ty)?;
                let v = self.expr(value)?;
                out.push_str(&format!("  {{ {ct} {} = {v};\n", temp(*t)));
                out.push_str(&self.pred_prefix(body)?);
                out.push_str("  }\n");
            }
            _ => return no("predicate without a native prefix"),
        }
        Ok(out)
    }

    fn words(&self, sid: ShapeId) -> usize {
        self.ty.words(sid) as usize
    }

    fn find_sid(&self, s: &Shape) -> R<ShapeId> {
        self.ty.lookup(s).ok_or(Unsupported("unregistered shape".into()))
    }

    /// A fresh number for local names.
    fn fresh(&mut self) -> usize {
        self.ntmp += 1;
        self.ntmp - 1
    }

    /// A fresh function-scope buffer of `n` words.
    fn buf(&mut self, n: usize) -> String {
        let name = format!("b{}", self.nbuf);
        self.nbuf += 1;
        writeln!(self.bufs, "  uint64_t {name}[{}];", n.max(1)).unwrap();
        name
    }

    /// A fresh number for static array names.
    fn fresh_static(&mut self) -> usize {
        self.nstatic += 1;
        self.nstatic - 1
    }

    /// Define (or reuse an identical) static constant array (`empty` initializes an empty one).
    fn static_array(&mut self, prefix: &str, cty: &'static str, items: &[String], empty: &'static str) -> String {
        let key = (cty, items.to_vec(), empty);
        if let Some(existing) = self.static_arr_dedup.get(&key) {
            return existing.clone();
        }
        let name = format!("{prefix}{}", self.fresh_static());
        let init = if items.is_empty() { empty.to_string() } else { items.join(", ") };
        writeln!(self.statics, "static const {cty} {name}[{}] = {{{init}}};", items.len().max(1)).unwrap();
        self.static_arr_dedup.insert(key.clone(), name.clone());
        self.static_arr_keys.push(key);
        name
    }

    /// A static constant word array (deduplicated across the translation unit).
    fn static_words(&mut self, w: &[u64]) -> String {
        let key = w.to_vec();
        if let Some(existing) = self.static_u64_dedup.get(&key) {
            return existing.clone();
        }
        let name = format!("k{}", self.fresh_static());
        let init = if w.is_empty() { "0".to_string() } else { w.iter().map(|x| format!("{x}ULL")).collect::<Vec<_>>().join(", ") };
        writeln!(self.statics, "static const uint64_t {name}[{}] = {{{init}}};", w.len().max(1)).unwrap();
        self.static_u64_dedup.insert(key.clone(), name.clone());
        self.static_u64_keys.push(key);
        name
    }

    fn c_ty(&self, t: Ty) -> R<&'static str> {
        match t {
            Ty::Bool | Ty::Int => Ok("int64_t"),
            Ty::Enc(_) => Ok("const uint64_t *"),
            Ty::Val if self.mixing => Ok("uint64_t"),
            Ty::Val => no("boxed value"),
        }
    }
}

/// `sig { switch (sel) { case i: return call(i); ... } }` over `n` cases.
fn dispatch(src: &mut String, sig: &str, sel: &str, n: usize, call: impl Fn(usize) -> String) {
    writeln!(src, "{sig} {{\n  switch ({sel}) {{").unwrap();
    for i in 0..n {
        writeln!(src, "  case {i}: return {};", call(i)).unwrap();
    }
    src.push_str("  default: return TLX_UNSUPPORTED;\n  }\n}\n");
}
