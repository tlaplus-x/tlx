//! Global interner for values stored in `Dyn` slots: equal values get equal
//! handles (canonical within one run). Handle 0 is never used.
//!
//! Scalars are not stored in the table: a handle's low `TAG_BITS` tell its
//! kind, and strings and model values (by their `Sym` id, already
//! canonical), Booleans and integers (of at most 61 bits) are encoded in
//! the handle itself, the shared schema of `crate::scalar` (a spec whose
//! state holds a new string per state otherwise interned every one twice,
//! its text and its value, and kept both tables for the run). Tag 0 is a
//! table handle: the table's own format, not that schema.
//!
//! Equality is `Value`'s structural equality on canonical forms (an
//! `Interval` and the equal enumerated `Set` share a handle); `lookup`
//! returns the representation that was interned first.
//!
//! The table is split into shards by hash, each behind its own lock, so
//! that search workers interning and looking up values in parallel rarely
//! touch the same lock. A handle is `(index in shard + 1) << SHARD_BITS |
//! shard`.
//!
//! Values are hashed with Fx over their canonical word stream, finished by
//! `fmix64` (`hash`; SipHash took a large share of an intern). A
//! handle's number depends on the hash (its shard) and on the order of
//! interning, which with several workers varies from run to run: nothing
//! may order by handles (they are compared for equality and hashed into
//! state fingerprints; no count, verdict or trace length depends on the
//! values of fingerprints).

use std::collections::HashMap;
use std::hash::{BuildHasher, BuildHasherDefault};
use std::sync::{OnceLock, RwLock, RwLockReadGuard, RwLockWriteGuard};
use tlx_base::hash::{fmix64, FxBuildHasher, IdHasher};

use crate::scalar::{self, TAG_BITS};
use tlx_value::Value;

const SHARD_BITS: u32 = 6;
const SHARDS: usize = 1 << SHARD_BITS;

/// Indices (in `Shard::vals`) of the values with one hash.
enum Ids {
    One(u32),
    Many(Vec<u32>),
}

#[derive(Default)]
struct Shard {
    ids: HashMap<u64, Ids, BuildHasherDefault<IdHasher>>,
    vals: Vec<Value>,
    /// Index in `vals` of the first TLA+-equal value in this shard
    /// (`canon[i] <= i` and `vals[canon[i]] == vals[i]`).
    canon: Vec<u32>,
}

impl Shard {
    fn find_by(&self, hash: u64, v: &Value, eq: fn(&Value, &Value) -> bool) -> Option<u32> {
        match self.ids.get(&hash)? {
            Ids::One(i) => eq(&self.vals[*i as usize], v).then_some(*i),
            Ids::Many(is) => is.iter().copied().find(|i| eq(&self.vals[*i as usize], v)),
        }
    }

    fn insert(&mut self, hash: u64, v: &Value) -> u32 {
        let i = u32::try_from(self.vals.len()).expect("dynval: too many values");
        let canon = self.find_by(hash, v, PartialEq::eq).unwrap_or(i);
        self.vals.push(v.clone());
        self.canon.push(canon);
        match self.ids.get_mut(&hash) {
            None => {
                self.ids.insert(hash, Ids::One(i));
            }
            Some(Ids::Many(is)) => is.push(i),
            Some(ids @ Ids::One(_)) => {
                let Ids::One(j) = *ids else { unreachable!() };
                *ids = Ids::Many(vec![j, i]);
            }
        }
        i
    }
}

/// A shard on its own cache lines.
#[repr(align(128))]
#[derive(Default)]
struct Padded(RwLock<Shard>);

impl Padded {
    fn read(&self) -> RwLockReadGuard<'_, Shard> {
        self.0.read().unwrap_or_else(|e| e.into_inner())
    }
    fn write(&self) -> RwLockWriteGuard<'_, Shard> {
        self.0.write().unwrap_or_else(|e| e.into_inner())
    }
}

fn shards() -> &'static [Padded; SHARDS] {
    static S: OnceLock<[Padded; SHARDS]> = OnceLock::new();
    S.get_or_init(|| std::array::from_fn(|_| Padded::default()))
}

/// The tag of a table handle: this table's own composite format, distinct
/// from the immediate scalar schema of `crate::scalar`.
const TAG_TABLE: u64 = 0;

fn handle(shard: usize, i: u32) -> u64 {
    ((i as u64 + 1) << SHARD_BITS | shard as u64) << TAG_BITS | TAG_TABLE
}

/// The hash of `v` (equal values, equal hashes; deterministic).
fn hash(v: &Value) -> u64 {
    fmix64(FxBuildHasher::default().hash_one(v))
}

/// The shard of a hash: middle bits, since a shard's map takes its buckets
/// from the low bits and its control bytes from the top ones.
fn shard_of(hash: u64) -> usize {
    (hash >> 32) as usize & (SHARDS - 1)
}

fn intern_by(v: &Value, eq: fn(&Value, &Value) -> bool) -> u64 {
    if let Some(h) = scalar::immediate(v) {
        return h;
    }
    let hash = hash(v);
    let si = shard_of(hash);
    let shard = &shards()[si];
    if let Some(i) = shard.read().find_by(hash, v, eq) {
        return handle(si, i);
    }
    let mut t = shard.write();
    let i = match t.find_by(hash, v, eq) {
        Some(i) => i,
        None => t.insert(hash, v),
    };
    handle(si, i)
}

pub fn intern(v: &Value) -> u64 {
    intern_by(v, PartialEq::eq)
}

/// Intern `v` by exact representation (`Value::exact_eq`), preserving
/// construction witnesses (`Tuple` vs `Record` vs `Fcn(_, Enumerated)` vs
/// `Fcn(_, Interval)`, `Interval` vs `Set`) while `canonical(h)` maps all
/// TLA+-equal handles to one canonical handle.
pub fn intern_exact(v: &Value) -> u64 {
    intern_by(v, Value::exact_eq)
}

/// Canonical handle of the TLA+-equality class of `h`: equal values have
/// identical canonical handles (`canonical(intern_exact(a)) == intern(b)`
/// whenever `a == b`).
pub fn canonical(h: u64) -> u64 {
    if scalar::tag(h) != TAG_TABLE {
        return h;
    }
    let t = scalar::payload(h);
    let si = (t & (SHARDS as u64 - 1)) as usize;
    let shard = shards()[si].read();
    match (t >> SHARD_BITS).checked_sub(1).and_then(|i| shard.canon.get(i as usize).copied()) {
        Some(c) => handle(si, c),
        None => panic!("dynval::canonical: invalid handle {h}"),
    }
}

/// The number of interned values and the bytes of the tables holding them
/// (the handles' slots and the hash index; not the values' own heap
/// data), for memory statistics.
pub fn footprint() -> (usize, usize) {
    let (mut n, mut bytes) = (0, 0);
    for s in shards() {
        let t = s.read();
        n += t.vals.len();
        bytes += t.vals.capacity() * std::mem::size_of::<Value>()
            + t.canon.capacity() * std::mem::size_of::<u32>()
            + t.ids.capacity() * (8 + std::mem::size_of::<Ids>() + 1);
    }
    (n, bytes)
}

/// The heap bytes retained by the interned values themselves (their
/// composite parts, each shared allocation once; `footprint` counts only
/// the tables), for memory statistics. Walks every value: call it at the
/// end of a run.
pub fn retained_value_bytes() -> usize {
    let mut seen = std::collections::HashSet::new();
    shards().iter().map(|s| tlx_value::value::retained_heap_bytes(s.read().vals.iter(), &mut seen)).sum()
}

/// Look up an arbitrary raw handle. Invalid tags, payloads and unpublished
/// symbols are rejected before any handle is converted into a `Value`.
/// This is the checked boundary for external words; trusted encodings use
/// `lookup_unchecked` to avoid locking the symbol table.
pub fn try_lookup(h: u64) -> Option<Value> {
    // Scalars: the shared schema and checked decode (`crate::scalar`); an
    // unpublished or too-wide `Sym` id makes `symbol` return None.
    fn symbol(h: u64) -> Option<tlx_value::Sym> {
        tlx_value::Sym::try_from_id(u32::try_from(scalar::payload(h)).ok()?)
    }
    if let Some(v) = scalar::scalar_value(h, symbol) {
        return Some(v);
    }
    match scalar::tag(h) {
        TAG_TABLE => {
            let t = scalar::payload(h);
            let si = (t & (SHARDS as u64 - 1)) as usize;
            let i = usize::try_from((t >> SHARD_BITS).checked_sub(1)?).ok()?;
            shards()[si].read().vals.get(i).cloned()
        }
        _ => None,
    }
}

/// Decode a raw handle, panicking if it is invalid.
pub fn lookup(h: u64) -> Value {
    try_lookup(h).unwrap_or_else(|| panic!("dynval::lookup: invalid handle {h}"))
}

/// Decode a trusted handle without validating symbol publication.
///
/// Safe Rust cannot invoke the raw trusted decoder:
/// ```compile_fail
/// let _: fn(u64) -> tlx_value::Value = tlx_layout::dynval::lookup_unchecked;
/// ```
///
/// # Safety
/// `h` must come from `intern` in this process, or a snapshot restored after
/// its symbol table. It must have reached this thread through synchronization
/// with the thread that interned it. Integers with the immediate integer tag
/// are valid for every payload; other tags must have canonical payloads.
pub unsafe fn lookup_unchecked(h: u64) -> Value {
    let sym = || match u32::try_from(scalar::payload(h)) {
        // SAFETY: handles come from `intern` (in this process, or restored
        // after the string table): the id is that of an interned symbol,
        // and the state holding the handle reached this thread through the
        // search's synchronization.
        Ok(id) => unsafe { tlx_value::Sym::from_id(id) },
        Err(_) => panic!("dynval::lookup: invalid handle {h}"),
    };
    match scalar::tag(h) {
        TAG_TABLE => {}
        scalar::TAG_STR => return Value::Str(sym()),
        scalar::TAG_MODEL_VALUE => return Value::ModelValue(sym()),
        scalar::TAG_BOOL => return Value::Bool(scalar::payload(h) != 0),
        scalar::TAG_INT => return Value::Int((h as i64) >> TAG_BITS),
        _ => panic!("dynval::lookup: invalid handle {h}"),
    }
    let t = scalar::payload(h);
    let si = (t & (SHARDS as u64 - 1)) as usize;
    let shard = shards()[si].read();
    match (t >> SHARD_BITS).checked_sub(1).and_then(|i| shard.vals.get(i as usize)) {
        Some(v) => v.clone(),
        None => panic!("dynval::lookup: invalid handle {h}"),
    }
}

/// Number of shards (part of a snapshot's identity).
pub const SHARD_COUNT: usize = SHARDS;

/// The values of every shard in index order, for checkpoints. Handles stay
/// valid across `snapshot` + `restore`. Call it while nothing interns (at a
/// safepoint); values interned concurrently may or may not be included.
pub fn snapshot() -> Vec<Vec<Value>> {
    shards().iter().map(|s| s.read().vals.clone()).collect()
}

/// Re-insert a snapshot so that every value gets its old handle. Each
/// shard's current contents must be a prefix of the snapshot's (normally the
/// interner is empty: restore before the search starts). Errors if the
/// snapshot does not fit this build (shard count, shard selection by hash)
/// or contradicts the current contents.
pub fn restore(snap: &[Vec<Value>]) -> Result<(), String> {
    if snap.len() != SHARDS {
        return Err(format!("Dyn interner snapshot has {} shards, expected {SHARDS}", snap.len()));
    }
    for (si, vals) in snap.iter().enumerate() {
        let mut t = shards()[si].write();
        for (i, v) in vals.iter().enumerate() {
            let hash = hash(v);
            if shard_of(hash) != si {
                return Err(format!("Dyn interner snapshot: value {v} is in shard {si}, but hashes to another shard"));
            }
            if let Some(old) = t.vals.get(i) {
                if !old.exact_eq(v) {
                    return Err(format!("Dyn interner: handle {} is {old}, snapshot has {v}", handle(si, i as u32)));
                }
                continue;
            }
            if let Some(j) = t.find_by(hash, v, Value::exact_eq) {
                return Err(format!("Dyn interner snapshot: {v} occurs twice in shard {si} (indices {j} and {i})"));
            }
            t.insert(hash, v);
        }
    }
    Ok(())
}
