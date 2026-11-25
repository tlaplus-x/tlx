//! Binary serialization of shapes, layouts, the `Dyn` interner and the
//! `Ref` value store for checkpoint/recover (docs/scale.md §9.2,
//! docs/value-store.md §7), on top of `tlx_value::ser` (same streams, same
//! framing).
//!
//! A shape is a tag byte and its payload:
//!
//! | tag | shape | payload |
//! |---|---|---|
//! | 0 | `Never` | — |
//! | 1 | `Bool` | — |
//! | 2 | `Int` | ivar lo, ivar hi |
//! | 3 | `Atom` | uvar n, n values |
//! | 4 | `Set` | elem, uvar max_card |
//! | 5 | `Fcn` | uvar n, n domain values, range |
//! | 6 | `Map` | key, range |
//! | 7 | `Record` | uvar n, n × (symbol reference, shape) |
//! | 8 | `Tuple` | uvar n, n shapes |
//! | 9 | `Seq` | elem, uvar max_len |
//! | 10 | `Union` | uvar n, n arms |
//! | 11 | `Dyn` | — |
//!
//! A layout is its variable shapes (uvar n, n shapes); offsets and widths
//! are recomputed by `Layout::new`, so the rebuilt layout (and the C code
//! generated from it) is identical.
//!
//! The `Dyn` interner snapshot is uvar shard count, then per shard uvar n
//! and its n values in index order. Restoring it (after the string intern
//! table, before anything interns a `Dyn` value) gives every value its old
//! handle, so handles inside encoded states stay valid.

use std::sync::Arc;

use tlx_value::ser::{decode_arc, DecodeResult, Reader, Writer};

use crate::layout::Layout;
use crate::shape::{FcnWitness, Shape};

const S_NEVER: u8 = 0;
const S_BOOL: u8 = 1;
const S_INT: u8 = 2;
const S_ATOM: u8 = 3;
const S_SET: u8 = 4;
const S_FCN: u8 = 5;
const S_MAP: u8 = 6;
const S_RECORD: u8 = 7;
const S_TUPLE: u8 = 8;
const S_SEQ: u8 = 9;
const S_UNION: u8 = 10;
const S_DYN: u8 = 11;

const W_ENUM: u8 = 0;
const W_INTV: u8 = 1;
const W_DYN: u8 = 2;

fn write_witness(w: &mut Writer, witness: FcnWitness) {
    w.u8(match witness {
        FcnWitness::Enumerated => W_ENUM,
        FcnWitness::Interval => W_INTV,
        FcnWitness::Dynamic => W_DYN,
    });
}

fn read_witness(r: &mut Reader<'_>) -> DecodeResult<FcnWitness> {
    Ok(match r.u8()? {
        W_ENUM => FcnWitness::Enumerated,
        W_INTV => FcnWitness::Interval,
        W_DYN => FcnWitness::Dynamic,
        t => return r.error(format!("unknown function witness tag {t}")),
    })
}

const MAX_DEPTH: u32 = 1000;

pub fn write_shape(w: &mut Writer, s: &Shape) {
    match s {
        Shape::Never => w.u8(S_NEVER),
        Shape::Bool => w.u8(S_BOOL),
        Shape::Int { lo, hi } => {
            w.u8(S_INT);
            w.ivar(*lo);
            w.ivar(*hi);
        }
        Shape::Atom(vs) => {
            w.u8(S_ATOM);
            write_values(w, vs);
        }
        Shape::Set { elem, max_card } => {
            w.u8(S_SET);
            write_shape(w, elem);
            w.usize(*max_card);
        }
        Shape::Fcn { dom, range, witness, key_variants } => {
            w.u8(S_FCN);
            write_values(w, dom);
            write_shape(w, range);
            write_witness(w, *witness);
            w.usize(key_variants.len());
            for (pos, vs) in key_variants.iter() {
                w.usize(*pos);
                write_values(w, vs);
            }
        }
        Shape::Map { key, range, witness } => {
            w.u8(S_MAP);
            write_shape(w, key);
            write_shape(w, range);
            write_witness(w, *witness);
        }
        Shape::Record(fs) => {
            w.u8(S_RECORD);
            w.usize(fs.len());
            for (k, f) in fs.iter() {
                w.sym(*k);
                write_shape(w, f);
            }
        }
        Shape::Tuple(es) => {
            w.u8(S_TUPLE);
            write_shapes(w, es);
        }
        Shape::Seq { elem, max_len } => {
            w.u8(S_SEQ);
            write_shape(w, elem);
            w.usize(*max_len);
        }
        Shape::Union(arms) => {
            w.u8(S_UNION);
            write_shapes(w, arms);
        }
        Shape::Dyn => w.u8(S_DYN),
        // (`Speculation::shapes` keeps `Shape::Dyn` and maps to `Shape::Ref` via `store_mode`.)
        Shape::Ref(_) => panic!("value store shapes are not serialized directly"),
    }
}

fn write_shapes(w: &mut Writer, ss: &[Shape]) {
    w.usize(ss.len());
    for s in ss {
        write_shape(w, s);
    }
}

fn write_values(w: &mut Writer, vs: &[tlx_value::Value]) {
    w.usize(vs.len());
    for v in vs {
        // Shape values are atoms and finite domain elements: always normal.
        w.value(v).expect("shape values are normalized");
    }
}

pub fn read_shape(r: &mut Reader<'_>) -> DecodeResult<Shape> {
    read_shape_at(r, 0)
}

fn read_shape_at(r: &mut Reader<'_>, depth: u32) -> DecodeResult<Shape> {
    if depth >= MAX_DEPTH {
        return r.error("shape nested too deeply");
    }
    let d = depth + 1;
    let tag = r.u8()?;
    Ok(match tag {
        S_NEVER => Shape::Never,
        S_BOOL => Shape::Bool,
        S_INT => Shape::Int { lo: r.ivar()?, hi: r.ivar()? },
        S_ATOM => Shape::Atom(read_values(r)?),
        S_SET => Shape::Set { elem: Box::new(read_shape_at(r, d)?), max_card: r.usize()? },
        S_FCN => {
            let dom = read_values(r)?;
            let range = Box::new(read_shape_at(r, d)?);
            let witness = read_witness(r)?;
            let kv_n = r.count(2)?;
            let mut key_variants = Vec::with_capacity(kv_n);
            let mut prev_pos: Option<usize> = None;
            for _ in 0..kv_n {
                let pos = r.usize()?;
                if pos >= dom.len() || prev_pos.is_some_and(|p| pos <= p) {
                    return r.error(format!("invalid function key variant position {pos}"));
                }
                prev_pos = Some(pos);
                let vs = read_values(r)?;
                if vs.len() < 2 {
                    return r.error("function key variant must hold at least two keys");
                }
                if !vs[0].exact_eq(&dom[pos]) {
                    return r.error("function key variant first key must match domain representative");
                }
                for w in vs.windows(2) {
                    if w[0].exact_cmp(&w[1]) != std::cmp::Ordering::Less {
                        return r.error("function key variants must be strictly increasing in exact order");
                    }
                }
                for v in &vs[1..] {
                    if tlx_value::order::eq_tlc(&vs[0], v) != Ok(true) {
                        return r.error("function key variants must be TLA+-equal to domain representative");
                    }
                }
                key_variants.push((pos, vs));
            }
            Shape::Fcn { dom, range, witness, key_variants: Arc::from(key_variants) }
        }
        S_MAP => {
            let key = Box::new(read_shape_at(r, d)?);
            let range = Box::new(read_shape_at(r, d)?);
            let witness = read_witness(r)?;
            Shape::Map { key, range, witness }
        }
        S_RECORD => {
            let n = r.count(2)?;
            let mut fs = Vec::with_capacity(n);
            for _ in 0..n {
                let k = r.sym()?;
                fs.push((k, read_shape_at(r, d)?));
            }
            Shape::Record(Arc::from(fs))
        }
        S_TUPLE => Shape::Tuple(read_shapes(r, d)?),
        S_SEQ => Shape::Seq { elem: Box::new(read_shape_at(r, d)?), max_len: r.usize()? },
        S_UNION => Shape::Union(read_shapes(r, d)?),
        S_DYN => Shape::Dyn,
        _ => return r.error(format!("unknown shape tag {tag}")),
    })
}

fn read_shapes(r: &mut Reader<'_>, depth: u32) -> DecodeResult<Arc<[Shape]>> {
    Ok(Arc::from(read_shapes_vec(r, depth)?))
}

fn read_shapes_vec(r: &mut Reader<'_>, depth: u32) -> DecodeResult<Vec<Shape>> {
    let n = r.count(1)?;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(read_shape_at(r, depth)?);
    }
    Ok(out)
}

fn read_values(r: &mut Reader<'_>) -> DecodeResult<Arc<[tlx_value::Value]>> {
    let n = r.count(1)?;
    decode_arc(n, tlx_value::Value::FALSE, || r.value())
}

pub fn write_layout(w: &mut Writer, l: &Layout) {
    write_shapes(w, &l.vars);
}

pub fn read_layout(r: &mut Reader<'_>) -> DecodeResult<Layout> {
    Ok(Layout::new(read_shapes_vec(r, 0)?))
}

/// Write a `dynval::snapshot()`. Errors only for values that cannot be
/// normalized (never the case for values of states).
pub fn write_dyn_table(w: &mut Writer, snap: &[Vec<tlx_value::Value>]) -> tlx_value::Result<()> {
    w.usize(snap.len());
    for shard in snap {
        w.usize(shard.len());
        for v in shard {
            w.value(v)?;
        }
    }
    Ok(())
}

/// Read a snapshot written by `write_dyn_table` (install it with
/// `dynval::restore`).
pub fn read_dyn_table(r: &mut Reader<'_>) -> DecodeResult<Vec<Vec<tlx_value::Value>>> {
    let shards = r.count(1)?;
    let mut out = Vec::with_capacity(shards);
    for _ in 0..shards {
        let n = r.count(1)?;
        let mut vals = Vec::with_capacity(n);
        for _ in 0..n {
            vals.push(r.value()?);
        }
        out.push(vals);
    }
    Ok(out)
}

/// Write a `Store` snapshot (`model-store`, docs/value-store.md §7).
pub fn write_store(w: &mut Writer, store: &crate::store::Store) -> Result<(), String> {
    store.write_snapshot(w)
}

/// Read and validate a `Store` snapshot written by `write_store`, allocating a
/// fresh process-unique store id and enforcing `budget`.
pub fn read_store(r: &mut Reader<'_>, budget: usize) -> Result<Arc<crate::store::Store>, String> {
    crate::store::Store::read_snapshot(r, budget)
}
