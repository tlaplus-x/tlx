//! Compact text form of the IR for debugging dumps (`TLX_IR_DUMP`): one
//! node per line, indented, with its representation (`#n` = `Enc(n)`).

use std::fmt::Write;

use crate::ir::{Expr, ExprKind, FieldLoc, SlotLayout, Stmt, Ty};

fn ty(t: Ty) -> String {
    match t {
        Ty::Bool => "bool".into(),
        Ty::Int => "int".into(),
        Ty::Enc(s) => format!("#{s}"),
        Ty::Val => "val".into(),
    }
}

fn fmt_loc(loc: FieldLoc) -> String {
    match loc {
        FieldLoc::Words(w) => format!("@{w}"),
        FieldLoc::Bits(p) => format!("@{}:{}+{}", p.word, p.shift, p.bits),
    }
}

fn fmt_slot(slot: SlotLayout) -> String {
    match slot {
        SlotLayout::Words(w) => format!("w{w}"),
        SlotLayout::Bits(b) => format!("b{b}"),
    }
}

/// A short label of an expression node (without its children).
pub(crate) fn label(e: &Expr) -> String {
    use ExprKind::*;
    let s = match &*e.kind {
        Const(v) => format!("const {v}"),
        ConstWords(w) => format!("words {:?}", &w[..w.len().min(8)]),
        Var(v) => format!("var {v}"),
        NextVar(v) => format!("var' {v}"),
        Temp(t) => format!("t{t}"),
        Slice { loc, .. } => format!("slice {}", fmt_loc(*loc)),
        Index { slot, .. } => format!("index {}", fmt_slot(*slot)),
        ExceptAt { loc, .. } => format!("except {}", fmt_loc(*loc)),
        Pack { parts, .. } => format!("pack x{}", parts.len()),
        Exists { bind, .. } => format!("exists t{bind}"),
        Forall { bind, .. } => format!("forall t{bind}"),
        Choose { bind, .. } => format!("choose t{bind}"),
        Let { temp, .. } => format!("let t{temp}"),
        Filter { bind, .. } => format!("filter t{bind}"),
        MapSet { bind, .. } => format!("mapset t{bind}"),
        Call { func, .. } => format!("call f{func}"),
        Collect { bind, .. } => format!("collect t{bind}"),
        Fold { product, bind, .. } => format!("{} t{bind}", if *product { "product" } else { "sum" }),
        UnionFold { bind, .. } => format!("union t{bind}"),
        MapBuild { bind, .. } => format!("mapbuild t{bind}"),
        SeqFilter { bind, .. } => format!("seqfilter t{bind}"),
        IntBin(op, ..) => format!("{op:?}"),
        IntCmp(op, ..) => format!("{op:?}"),
        BitSetOp(op, ..) => format!("bit{op:?}"),
        SortedOp { op, .. } => format!("sorted{op:?}"),
        ValOp { op, .. } => format!("valop {}", op.name()),
        RefOp { op, .. } => format!("refop {op:?}"),
        ValField(_, f) => format!("field {f:?}"),
        Fail(m) => format!("fail {m:?}"),
        ConstElems { count, elem, .. } => format!("constelems #{elem} x{count}"),
        Interp { expr, .. } => {
            let d = format!("{:?}", expr.kind);
            format!("interp {} @{}:{}", cut(&d, 60), expr.span.line, expr.span.col)
        }
        k => format!("{k:?}").split([' ', '(', '{']).next().unwrap_or("?").to_string(),
    };
    format!("{s} : {}", ty(e.ty))
}

/// The largest prefix of `s` of at most `max` bytes that ends on a character
/// boundary: a debug text is arbitrary UTF-8, and a byte cut inside a
/// multibyte character panics instead of printing a diagnostic (CODE-17).
/// Every byte of ASCII text is a boundary, so ASCII dumps are unchanged.
pub(crate) fn cut(s: &str, max: usize) -> &str {
    let mut end = max.min(s.len());
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

pub fn expr(e: &Expr, depth: usize, out: &mut String) {
    writeln!(out, "{}{}", "  ".repeat(depth), label(e)).unwrap();
    if !matches!(&*e.kind, ExprKind::Interp { .. }) {
        e.for_each_child(&mut |c| expr(c, depth + 1, out));
    } else if let ExprKind::Interp { binds, .. } = &*e.kind {
        for (_, b) in binds {
            expr(b, depth + 1, out);
        }
    }
}

pub fn stmt(s: &Stmt, depth: usize, out: &mut String) {
    let pad = "  ".repeat(depth);
    let head = match s {
        Stmt::Stop => "stop".to_string(),
        Stmt::Emit => "emit".to_string(),
        Stmt::Compose { .. } => "compose".to_string(),
        Stmt::Branches(bs) => format!("branches {}", bs.len()),
        Stmt::Guard { .. } => "guard".to_string(),
        Stmt::If { .. } => "if".to_string(),
        Stmt::Then { .. } => "then".to_string(),
        Stmt::Let { temp, .. } => format!("let t{temp}"),
        Stmt::ForEach { bind, sorted, .. } => format!("foreach t{bind}{}", if *sorted { " sorted" } else { "" }),
        Stmt::Assign { var, .. } => format!("assign var' {var}"),
        Stmt::Error(m) => format!("error {m:?}"),
        Stmt::Repeat { id, bind, .. } => format!("repeat {id} t{bind}"),
        Stmt::Count(id) => format!("count {id}"),
    };
    writeln!(out, "{pad}{head}").unwrap();
    if let Some(e) = s.expr() {
        expr(e, depth + 2, out);
    }
    s.for_each_sub_stmt(&mut |b| stmt(b, depth + 1, out));
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tlx_eval::env::Env;
    use tlx_sema::hir;

    use super::*;

    /// An `Interp` node (the interpreter fallback) whose debug text is
    /// `Str("<content>")`: `7 + content.len()` bytes, of which the first five
    /// are the `Str("` prefix.
    fn interp_str(content: &str, line: u32, col: u32) -> Expr {
        let span = hir::Span { line, col, ..Default::default() };
        Expr {
            ty: Ty::Val,
            kind: Box::new(ExprKind::Interp {
                expr: hir::Expr::new(hir::ExprKind::Str(Arc::from(content)), span),
                binds: Vec::new(),
                deferred: Vec::new(),
                env: Env::default(),
            }),
        }
    }

    /// The debug text `label` truncates, computed the same way it is.
    fn debug_text(content: &str) -> String {
        format!("{:?}", hir::ExprKind::Str(Arc::from(content)))
    }

    /// Placements of a multibyte character so that a raw 60-byte cut would
    /// land inside it: `(ascii prefix length, character)`. Content starts at
    /// byte 5 of the debug text, so the character occupies
    /// `5 + ascii .. 5 + ascii + ch.len_utf8()`, which contains byte 60 for
    /// every case below.
    const MULTIBYTE: &[(usize, char)] = &[
        (54, 'é'),  // 2 bytes at 59..61
        (53, '中'), // 3 bytes at 58..61
        (54, '中'), // 3 bytes at 59..62
        (52, '😀'), // 4 bytes at 57..61
    ];

    /// The ASCII dump is byte for byte what it was before the boundary fix;
    /// only a cut inside a multibyte character changes (CODE-17). 70 digits
    /// debug as `Str("..."` = 77 bytes, so the 60-byte prefix keeps the five
    /// prefix bytes and 55 digits.
    #[test]
    fn interp_label_ascii_golden() {
        let l = label(&interp_str(&"0123456789".repeat(7), 7, 3));
        assert_eq!(l, "interp Str(\"0123456789012345678901234567890123456789012345678901234 @7:3 : val");
    }

    /// Every byte of ASCII text is a character boundary, so the fix must not
    /// move the cut for any pure-ASCII debug text.
    #[test]
    fn cut_keeps_an_ascii_byte_prefix() {
        for n in 0..200 {
            let s = "a".repeat(n);
            assert_eq!(cut(&s, 60), &s[..s.len().min(60)], "n={n}");
        }
        assert_eq!(cut("", 60), "");
        assert_eq!(cut("ascii", 60), "ascii");
    }

    /// A raw byte cut inside a multibyte character is what the old
    /// `&d[..d.len().min(60)]` panicked on; the fix backs off to the
    /// character's start.
    #[test]
    fn cut_backs_off_to_a_character_boundary() {
        for &(ascii, ch) in MULTIBYTE {
            let d = debug_text(&format!("{}{ch}", "a".repeat(ascii)));
            assert!(!d.is_char_boundary(60), "case ({ascii}, {ch:?}) does not straddle byte 60");
            assert_eq!(cut(&d, 60), &d[..5 + ascii], "case ({ascii}, {ch:?})");
        }
    }

    /// The cut is a prefix, stays within the limit and is as long as the
    /// limit allows.
    #[test]
    fn cut_is_the_longest_boundary_prefix() {
        let s = "aé中😀b".repeat(20);
        for n in 0..s.len() + 3 {
            let p = cut(&s, n);
            assert!(s.starts_with(p), "n={n}");
            assert!(p.len() <= n, "n={n}");
            assert!(s.is_char_boundary(p.len()), "n={n}");
            assert!(p.len() == s.len() || p.len() == n || !s.is_char_boundary(p.len() + 1), "n={n} is not maximal");
        }
    }

    /// The label of a multibyte fallback node keeps the whole text of the
    /// straddling case and the span suffix.
    #[test]
    fn interp_label_multibyte_is_exact() {
        for &(ascii, ch) in MULTIBYTE {
            let content = format!("{}{ch}", "a".repeat(ascii));
            let d = debug_text(&content);
            let l = label(&interp_str(&content, 7, 3));
            assert_eq!(l, format!("interp {} @7:3 : val", &d[..5 + ascii]), "case ({ascii}, {ch:?})");
        }
    }

    /// The dump of a multibyte fallback node: the label line, then its bound
    /// locals (`expr` does not walk the fallback's children, see below).
    #[test]
    fn expr_dump_of_a_multibyte_interp() {
        let content = format!("{}é", "a".repeat(54));
        let d = debug_text(&content);
        let mut e = interp_str(&content, 7, 3);
        if let ExprKind::Interp { binds, .. } = &mut *e.kind {
            binds.push((hir::LocalId(0), Expr { ty: Ty::Int, kind: Box::new(ExprKind::Temp(0)) }));
        }
        let mut out = String::new();
        expr(&e, 1, &mut out);
        assert_eq!(out, format!("  interp {} @7:3 : val\n    t0 : int\n", &d[..5 + 54]));
    }
}
