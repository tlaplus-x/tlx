use super::*;

impl Program {
    pub fn arena_expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id.idx()]
    }

    /// Number of expressions in the arena (an upper bound of `ExprId::index`).
    pub fn arena_len(&self) -> usize {
        self.exprs.len()
    }

    pub fn expr_id(&self, expr: &Expr) -> Option<ExprId> {
        let id = expr.arena_id?;
        let stored = self.exprs.get(id.idx())?;
        (Arc::ptr_eq(&stored.kind, &expr.kind) && stored.span == expr.span).then_some(id)
    }

    pub(super) fn index_exprs(&mut self) {
        let mut indexed = HashMap::new();
        for def in &mut self.defs {
            match &mut def.kind {
                DefKind::Op(body) => index(body, &mut self.exprs, &mut indexed),
                DefKind::Fn { bounds, body } => {
                    for bound in bounds {
                        index(&mut bound.set, &mut self.exprs, &mut indexed);
                    }
                    index(body, &mut self.exprs, &mut indexed);
                }
                DefKind::Pending => {}
            }
        }
        for assume in &mut self.assumes {
            index(assume, &mut self.exprs, &mut indexed);
        }
    }
}

fn index(expr: &mut Expr, arena: &mut Vec<Expr>, indexed: &mut HashMap<usize, (Arc<ExprKind>, Arc<ExprKind>)>) {
    let key = Arc::as_ptr(&expr.kind) as usize;
    if let Some((_, kind)) = indexed.get(&key) {
        expr.kind = kind.clone();
    } else {
        let original = expr.kind.clone();
        crate::visit::children_mut(expr, &mut |child| index(child, arena, indexed));
        indexed.insert(key, (original, expr.kind.clone()));
    }
    let id = u32::try_from(arena.len())
        .ok()
        .and_then(|len| len.checked_add(1))
        .and_then(std::num::NonZeroU32::new)
        .expect("HIR arena exhausted");
    expr.arena_id = Some(ExprId(id));
    arena.push(expr.clone());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexing_preserves_shared_kinds_and_individual_spans() {
        let first = Expr::new(ExprKind::Num(42), Span::default());
        let mut second = first.clone();
        second.span.line = 2;
        let mut root = Expr::new(ExprKind::Tuple(vec![first, second]), Span::default());
        let mut arena = Vec::new();
        index(&mut root, &mut arena, &mut HashMap::new());
        let ExprKind::Tuple(children) = &*root.kind else { panic!("tuple") };
        assert!(Arc::ptr_eq(&children[0].kind, &children[1].kind));
        for child in children {
            let stored = &arena[child.arena_id.unwrap().idx()];
            assert!(Arc::ptr_eq(&child.kind, &stored.kind));
            assert_eq!(child.span, stored.span);
        }
        assert_eq!(arena.len(), 3);
    }
}
