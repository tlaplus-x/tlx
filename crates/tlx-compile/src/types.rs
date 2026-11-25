//! Shape registry for typed lowering: `ShapeId` ↔ `Shape`, word sizes and
//! the layout of state variables.

use std::collections::HashMap;
use std::ops::Range;
use std::sync::{Arc, OnceLock};

use tlx_layout::layout::{words, MapDims};
use tlx_layout::{Layout, LayoutNode, Shape};

use tlx_value::plan::{Absent, Witness};

use crate::ir::{MapPutPlan, ShapeId, Ty};

#[derive(Clone, Debug)]
pub struct Typing {
    pub layout: Arc<Layout>,
    shapes: Vec<Shape>,
    words: Vec<u32>,
    /// Layout tree of each shape (built on first use).
    nodes: Vec<OnceLock<Arc<LayoutNode>>>,
    ids: HashMap<Shape, ShapeId>,
    /// Shape of each state variable.
    pub var_sid: Vec<ShapeId>,
    /// Shapes of materialized 0-ary state-level definitions.
    pub def_sid: HashMap<tlx_sema::hir::DefId, ShapeId>,
    /// Compiled functions (`ExprKind::Call`).
    pub funcs: Vec<crate::ir::FnDef>,
    /// Shapes with ids below this are those of the state variables and
    /// materialized definitions and their nested shapes (registered first):
    /// the shapes whose values the layout functions encode and transcode.
    layout_shapes: usize,
    /// The run's value store shape (`Shape::Ref`), if the layout has one.
    ref_sid: Option<ShapeId>,
    /// The verification of the layout and of `funcs` (`verify::verified`):
    /// every backend verifies each action, predicate and host region against
    /// it, so it is computed once; `funcs_changed` resets it.
    verified: OnceLock<Arc<crate::verify::Verified>>,
}

impl Typing {
    pub fn new(layout: Arc<Layout>) -> Typing {
        let mut t = Typing {
            layout: layout.clone(),
            shapes: Vec::new(),
            words: Vec::new(),
            nodes: Vec::new(),
            ids: HashMap::new(),
            var_sid: Vec::new(),
            def_sid: HashMap::new(),
            funcs: Vec::new(),
            layout_shapes: 0,
            ref_sid: None,
            verified: OnceLock::new(),
        };
        t.var_sid = layout.vars.iter().map(|s| t.id(s)).collect();
        // Register nested shapes too, so constant values can reuse the
        // state's atom universes and integer ranges.
        for s in layout.vars.iter() {
            t.register_nested(s);
        }
        t.layout_shapes = t.shapes.len();
        t.ref_sid = t.find_ref();
        t
    }

    /// The id of the `Shape::Ref` of the registered shapes: a run has one
    /// value store, so at most one such shape (`Shape` equality is the
    /// store's identity); panics on two.
    fn find_ref(&self) -> Option<ShapeId> {
        let mut refs = self.shapes.iter().enumerate().filter_map(|(i, s)| match s {
            Shape::Ref(st) => Some((i as ShapeId, st)),
            _ => None,
        });
        let (first, a) = refs.next()?;
        if let Some((_, b)) = refs.next() {
            panic!("value store handles of two stores in one run ({:?}, {:?})", a.0, b.0);
        }
        Some(first)
    }

    /// The id of the run's value store shape (`Shape::Ref`), if the layout
    /// (or a materialized definition) has one.
    pub fn ref_sid(&self) -> Option<ShapeId> {
        self.ref_sid
    }

    /// The run's value store, if the layout has one.
    pub fn ref_store(&self) -> Option<tlx_layout::store::StoreRef> {
        match self.shape(self.ref_sid?) {
            Shape::Ref(s) => Some(s.clone()),
            _ => None,
        }
    }

    /// The cached verification (see `verified`).
    pub(crate) fn verified_cache(&self) -> &OnceLock<Arc<crate::verify::Verified>> {
        &self.verified
    }

    /// `funcs` changed: the cached verification no longer applies.
    pub(crate) fn funcs_changed(&mut self) {
        self.verified = OnceLock::new();
    }

    /// With materialized definitions of the given shapes.
    pub fn with_defs(layout: Arc<Layout>, defs: &[(tlx_sema::hir::DefId, Shape)]) -> Typing {
        let mut t = Typing::new(layout);
        for (d, s) in defs {
            t.register_nested(s);
            let sid = t.id(s);
            t.def_sid.insert(*d, sid);
        }
        t.layout_shapes = t.shapes.len();
        t.ref_sid = t.find_ref();
        t
    }

    /// Whether shape `id` is (nested in) the shape of a state variable or
    /// materialized definition. Other shapes are those of intermediate
    /// values (e.g. the parameters of compiled functions), which the layout
    /// functions never encode.
    pub fn in_layout(&self, id: ShapeId) -> bool {
        (id as usize) < self.layout_shapes
    }

    fn register_nested(&mut self, s: &Shape) {
        self.id(s);
        s.for_each_child(|c| self.register_nested(c));
        if let Shape::Map { key, .. } = s {
            self.id(&map_domain_shape(key));
        }
    }

    /// The plan of an update of a map of type `ty` (`ExprKind::MapPut`):
    /// for an EXCEPT (`Absent::Unchanged`), the ranks whose keys the empty
    /// map's witness rejects on its missing-key branch (an empty map
    /// decodes as `<<>>`, see `MapPutPlan`).
    pub(crate) fn map_put_plan(&self, ty: Ty, absent: Absent) -> MapPutPlan {
        fn push(out: &mut Vec<Range<u64>>, range: Range<u64>) {
            if let Some(last) = out.last_mut().filter(|r| r.end == range.start) {
                last.end = range.end;
            } else if !range.is_empty() {
                out.push(range);
            }
        }
        fn collect(s: &Shape, base: u64, out: &mut Vec<Range<u64>>) {
            let admitted = Witness::Tuple.key_type();
            match s {
                Shape::Int { .. } => {}
                Shape::Atom(values) => {
                    for (i, v) in values.iter().enumerate() {
                        if !admitted.admits(v) {
                            let start = base + i as u64;
                            push(out, start..start + 1);
                        }
                    }
                }
                Shape::Union(arms) => {
                    let mut base = base;
                    for arm in arms.iter() {
                        collect(arm, base, out);
                        base += arm.cardinality().expect("finite map keys");
                    }
                }
                _ => push(out, base..base + s.cardinality().expect("finite map keys")),
            }
        }
        let mut out = Vec::new();
        if let (Absent::Unchanged, Ty::Enc(sid)) = (absent, ty) {
            if let Shape::Map { key, .. } = self.shape(sid) {
                collect(key, 0, &mut out);
            }
        }
        MapPutPlan { absent, reject_when_empty: out.into() }
    }

    pub fn id(&mut self, s: &Shape) -> ShapeId {
        if let Some(&id) = self.ids.get(s) {
            return id;
        }
        let id = self.shapes.len() as ShapeId;
        self.shapes.push(s.clone());
        self.words.push(u32::try_from(words(s)).unwrap_or(u32::MAX));
        self.nodes.push(OnceLock::new());
        self.ids.insert(s.clone(), id);
        id
    }

    /// Id of an already registered shape.
    pub fn lookup(&self, s: &Shape) -> Option<ShapeId> {
        self.ids.get(s).copied()
    }

    pub fn shape(&self, id: ShapeId) -> &Shape {
        &self.shapes[id as usize]
    }

    /// The layout tree of shape `id` (for encoding, decoding and ranking
    /// values of that shape).
    pub fn node(&self, id: ShapeId) -> &LayoutNode {
        self.nodes[id as usize].get_or_init(|| Arc::new(LayoutNode::new(&self.shapes[id as usize])))
    }

    pub fn num_shapes(&self) -> usize {
        self.shapes.len()
    }

    pub fn words(&self, id: ShapeId) -> u32 {
        self.words[id as usize]
    }

    pub fn var_ty(&self, v: usize) -> Ty {
        Ty::Enc(self.var_sid[v])
    }

    pub fn var_offset(&self, v: usize) -> usize {
        self.layout.offsets[v]
    }

    /// Word range of variable `v` in an encoded state.
    pub fn var_range(&self, v: usize) -> Range<usize> {
        let off = self.var_offset(v);
        off..off + self.words(self.var_sid[v]) as usize
    }
}

/// The encoding of map shape `s` (None: not a map shape).
pub fn map_dims(s: &Shape) -> Option<MapDims> {
    MapDims::of(s)
}

pub(crate) fn scalar_arm(arms: &[Shape], ty: Ty) -> Option<(usize, i64, i64)> {
    arms.iter().enumerate().find_map(|(index, arm)| match (ty, arm) {
        (Ty::Int, Shape::Int { lo, hi }) => Some((index, *lo, *hi)),
        (Ty::Bool, Shape::Bool) => Some((index, 0, 1)),
        _ => None,
    })
}

/// The shape of `DOMAIN m` for maps with keys of shape `key`: a bitset over
/// the key universe (the prefix of the map's encoding).
pub fn map_domain_shape(key: &Shape) -> Shape {
    let u = key.cardinality().expect("map key universe") as usize;
    Shape::Set { elem: Box::new(key.clone()), max_card: u }
}
