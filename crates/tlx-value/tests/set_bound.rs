//! `-maxSetSize` (TLC's `TLCGlobals.setBound`): the limit on the number of
//! elements of a set that is materialized, and where TLC does *not* apply it
//! (`docs/compat.md` section 5).
//!
//! TLC's `ValueVec` starts with ten slots and checks the bound only when it
//! grows, so a set that is appended to may hold up to `max(10, setBound)`
//! elements; a set literal and an interval are preallocated to their exact
//! size and are never limited, and `SUBSET S`/`kSubset(k, S)` stream.
//!
//! The limit is process-wide, as in TLC, so the tests of this file take a
//! lock and each sets and restores it (this file is a separate test binary:
//! the tests of `ops.rs` and the other files keep the default).

use std::sync::{Arc, Mutex, MutexGuard};

use tlx_value::ops::{self, BoundKind};
use tlx_value::{limits, LazySet, Value};

static LOCK: Mutex<()> = Mutex::new(());

/// A lock on the process-wide limit, restored on drop.
struct Bound {
    /// The lock of the test (the field exists only to be held).
    _guard: MutexGuard<'static, ()>,
}

impl Bound {
    /// Set the limit to `n` for the test, serialized; restored afterwards.
    fn new(n: i64) -> Bound {
        let guard = LOCK.lock().unwrap_or_else(|e| e.into_inner());
        limits::set_max_set_size(n);
        Bound { _guard: guard }
    }
}

impl Drop for Bound {
    fn drop(&mut self) {
        limits::set_max_set_size(limits::DEFAULT_MAX_SET_SIZE);
    }
}

fn set(es: impl IntoIterator<Item = i64>) -> Value {
    Value::Set(es.into_iter().map(Value::Int).collect::<Vec<_>>().into())
}

fn interval(lo: i64, hi: i64) -> Value {
    ops::interval(lo, hi)
}

/// `[1..d -> 1..r]`
fn fcn_set(d: i64, r: i64) -> Value {
    ops::fcn_set(&interval(1, d), &interval(1, r)).unwrap()
}

fn too_many(n: i64) -> String {
    format!("Attempted to construct a set with too many elements (>{n})")
}

#[test]
fn the_default_is_tlcs_million() {
    let _b = Bound::new(limits::DEFAULT_MAX_SET_SIZE);
    assert_eq!(limits::max_set_size(), 1_000_000);
    assert_eq!(limits::DEFAULT_MAX_SET_SIZE, 1_000_000);
    assert_eq!(limits::growth_limit(), 1_000_000);
}

#[test]
fn a_growing_set_admits_tlcs_ten_initial_slots() {
    // TLC's `ValueVec()` starts with ten slots and checks the bound only when
    // it grows: at bound 4 a set former of five elements is still built.
    let _b = Bound::new(4);
    assert_eq!(limits::growth_limit(), 10);
    assert_eq!(limits::max_set_size(), 4);
    let five = Value::set_enum((1..=5).map(Value::Int).collect()).unwrap();
    assert_eq!(ops::enumerate(&five).unwrap().len(), 5);
    // The eleventh element is the first that fails.
    let e = Value::set_enum((1..=11).map(Value::Int).collect()).unwrap_err().to_string();
    assert_eq!(e, too_many(4));
    let mut out = Vec::new();
    for i in 1..=11 {
        if let Err(e) = limits::push(&mut out, Value::Int(i)) {
            assert_eq!(e.to_string(), too_many(4));
            assert_eq!(i, 11, "the eleventh element is the first that fails");
            return;
        }
    }
    panic!("an eleventh element was pushed");
}

#[test]
fn materializing_a_set_over_the_bound_is_an_error() {
    // TLC builds `[S -> T]`, `\X` and record sets in a growing `ValueVec`,
    // which fails once it would hold more than the bound's elements.
    {
        let _b = Bound::new(10);
        assert_eq!(ops::enumerate(&fcn_set(3, 5)).unwrap_err().to_string(), too_many(10));
        let product = ops::product(vec![interval(1, 4), interval(1, 3)]).unwrap();
        assert_eq!(ops::enumerate(&product).unwrap_err().to_string(), too_many(10));
        let record = ops::record_set(vec![(tlx_value::Sym::new("a"), interval(1, 4)), (tlx_value::Sym::new("b"), interval(1, 3))]).unwrap();
        assert_eq!(ops::enumerate(&record).unwrap_err().to_string(), too_many(10));
    }
    // Exactly the bound is allowed (TLC's capacity grows up to `setBound`).
    let _b = Bound::new(125);
    assert_eq!(ops::enumerate(&fcn_set(3, 5)).unwrap().len(), 125);
}

#[test]
fn a_set_literal_and_an_interval_are_preallocated_in_tlc() {
    let _b = Bound::new(4);
    // TLC builds a literal in a `ValueVec` preallocated to its length, so it
    // never grows; a set former over the same elements does grow (`set_enum`).
    let literal = Value::set_literal((1..=10).map(Value::Int).collect()).unwrap();
    assert_eq!(ops::enumerate(&literal).unwrap().len(), 10);
    // `IntervalValue.toSetEnum` also fills an exactly sized array.
    assert_eq!(ops::enumerate(&interval(1, 100)).unwrap().len(), 100);
}

#[test]
fn the_paths_tlc_streams_are_not_limited() {
    let _b = Bound::new(4);
    // `SUBSET S` and `kSubset(k, S)` enumerate lazily in the normalized order.
    let powerset = ops::powerset(&set(1..=5)).unwrap();
    assert_eq!(ops::enumerate(&powerset).unwrap().len(), 32);
    assert_eq!(ops::enumerate_normalized(&powerset).unwrap().len(), 32);
    // An enumerated set is already built, and a streamed traversal
    // (`for_each_enumerated`) never builds the whole set.
    assert_eq!(ops::enumerate(&set(1..=10)).unwrap().len(), 10);
    let mut seen = 0;
    ops::for_each_enumerated(&interval(1, 100), &mut |_| {
        seen += 1;
        Ok(true)
    })
    .unwrap();
    assert_eq!(seen, 100);
    let mut seen = 0;
    ops::for_each_enumerated(&fcn_set(3, 5), &mut |_| {
        seen += 1;
        Ok(true)
    })
    .unwrap();
    assert_eq!(seen, 125);
}

#[test]
fn the_bound_decision_is_shared_with_the_compiled_tier() {
    let _b = Bound::new(10);
    assert_eq!(ops::bound_kind(&set(1..=3)), BoundKind::Share);
    assert_eq!(ops::bound_kind(&interval(1, 100)), BoundKind::Share);
    assert_eq!(ops::bound_kind(&ops::powerset(&set(1..=5)).unwrap()), BoundKind::Stream);
    assert_eq!(ops::bound_kind(&fcn_set(3, 5)), BoundKind::Materialize);
    // A function set over TLC's int: TLC's growing `ValueVec` reaches the
    // bound before the size could overflow.
    assert_eq!(ops::bound_kind(&fcn_set(5, 121)), BoundKind::Overflow);
    assert_eq!(ops::bound_kind(&Value::Int(1)), BoundKind::Materialize);
}

#[test]
fn over_set_bound_only_answers_for_cheaply_sized_sets() {
    let _b = Bound::new(10);
    assert!(ops::over_set_bound(&fcn_set(3, 5)));
    assert!(!ops::over_set_bound(&fcn_set(2, 3)));
    assert!(!ops::over_set_bound(&ops::powerset(&set(1..=5)).unwrap()));
    assert!(!ops::over_set_bound(&interval(1, 100)));
    let cup = ops::union(&ops::powerset(&set(1..=5)).unwrap(), &ops::powerset(&set(1..=2)).unwrap()).unwrap();
    assert!(matches!(&cup, Value::LazySet(l) if matches!(**l, LazySet::Cup(..))));
    assert!(!ops::over_set_bound(&cup));
}

#[test]
fn eager_set_algebra_applies_the_bound_to_the_result() {
    let _b = Bound::new(10);
    // `(1..10) \cup {}` is the interval: no copy, but TLC's `IntervalValue.cup`
    // would have copied ten elements, so exactly the bound is allowed ...
    assert_eq!(ops::union(&interval(1, 10), &Value::empty_set()).unwrap(), interval(1, 10));
    // ... and eleven is the same error as any other materialization.
    assert_eq!(ops::union(&interval(1, 11), &Value::empty_set()).unwrap_err().to_string(), too_many(10));
    // A union that stays within the bound.
    assert_eq!(ops::union(&set([1, 3]), &set([2, 3])).unwrap(), set(1..=3));
    // `UNION {{1..6}, {3..8}}` has eight distinct elements, not twelve
    // occurrences: TLC's eager `UnionValue.union` deduplicates as it appends.
    let union = ops::big_union(&Value::empty_set()).unwrap();
    assert_eq!(ops::enumerate(&union).unwrap(), Vec::<Value>::new());
    let outer = Value::set_from(vec![set(1..=6), set(3..=8)]).unwrap();
    assert_eq!(ops::big_union(&outer).unwrap(), set(1..=8));
    let too_big = Value::set_from(vec![set(1..=6), set(5..=11)]).unwrap();
    assert_eq!(ops::big_union(&too_big).unwrap_err().to_string(), too_many(10));
}

#[test]
fn the_size_preflight_never_enumerates_a_lazy_set() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[derive(Debug)]
    struct Counting(Arc<AtomicUsize>);
    impl tlx_value::CustomSet for Counting {
        fn contains(&self, _: &Value) -> tlx_value::Result<bool> {
            Ok(true)
        }
        fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
            unreachable!("the size must not be computed by enumerating")
        }
        fn for_each(&self, f: &mut dyn FnMut(Value) -> tlx_value::Result<bool>) -> tlx_value::Result<Option<bool>> {
            for i in 0..12 {
                self.0.fetch_add(1, Ordering::Relaxed);
                if !f(Value::Int(i))? {
                    return Ok(Some(false));
                }
            }
            Ok(Some(true))
        }
    }

    let _b = Bound::new(10);
    let visits = Arc::new(AtomicUsize::new(0));
    let custom = Value::LazySet(Arc::new(LazySet::Custom(Box::new(Counting(visits.clone())))));
    // (The compiler asks this while lowering: a set whose size is unknown is
    // left to the bounded visitor, which visits it and reports the bound.)
    assert!(!ops::over_set_bound(&custom));
    assert_eq!(visits.load(Ordering::Relaxed), 0, "over_set_bound enumerated a lazy set");

    // A known size is answered from the components: a product over a million
    // integers is over the bound without materializing anything.
    let product = ops::product(vec![interval(1, 1_000_000), interval(0, 0)]).unwrap();
    assert!(ops::over_set_bound(&product));
    assert_eq!(ops::size_if_known(&product), Some(1_000_000));
    assert_eq!(ops::size_if_known(&fcn_set(3, 5)), Some(125));
    assert_eq!(ops::size_if_known(&interval(1, 100)), Some(100));
    assert_eq!(ops::size_if_known(&custom), None);
    let lazy_cup = ops::union(&ops::powerset(&set(1..=2)).unwrap(), &ops::powerset(&set(1..=3)).unwrap()).unwrap();
    assert!(matches!(&lazy_cup, Value::LazySet(l) if matches!(**l, LazySet::Cup(..))));
    assert_eq!(ops::size_if_known(&lazy_cup), None);
    // (`SUBSET S` counts from its base; over an int it is an error, not a size.)
    assert_eq!(ops::size_if_known(&ops::powerset(&set(1..=5)).unwrap()), Some(32));
    assert_eq!(ops::size_if_known(&ops::powerset(&set(1..=31)).unwrap()), None);
}

#[test]
fn the_size_facts_are_recursive_and_never_enumerate() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[derive(Debug)]
    struct Counting(Arc<AtomicUsize>);
    impl tlx_value::CustomSet for Counting {
        fn contains(&self, _: &Value) -> tlx_value::Result<bool> {
            Ok(true)
        }
        fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
            unreachable!("a size must not be computed by enumerating")
        }
        fn for_each(&self, f: &mut dyn FnMut(Value) -> tlx_value::Result<bool>) -> tlx_value::Result<Option<bool>> {
            for i in 0..12 {
                self.0.fetch_add(1, Ordering::Relaxed);
                if !f(Value::Int(i))? {
                    return Ok(Some(false));
                }
            }
            Ok(Some(true))
        }
    }

    let _b = Bound::new(10);
    let visits = Arc::new(AtomicUsize::new(0));
    let custom = Value::LazySet(Arc::new(LazySet::Custom(Box::new(Counting(visits.clone())))));
    let wrapped = ops::product(vec![custom.clone(), interval(1, 1)]).unwrap();
    // A component whose size is unknown leaves the product unknown, and the
    // queries answer from the facts alone (the filter's predicate is not
    // evaluated while sizing).
    assert_eq!(ops::size_fact(&wrapped), ops::SizeFact::Unknown);
    assert_eq!(ops::size_if_known(&wrapped), None);
    assert!(!ops::over_set_bound(&wrapped));
    // A deferred enumeration containing a lazy set (`{custom, {}}`) must also
    // stay `Unknown` without sorting or enumerating `custom`.
    let deferred = Value::set_literal(vec![custom.clone(), Value::empty_set()]).unwrap();
    assert_eq!(ops::size_fact(&deferred), ops::SizeFact::Unknown);
    assert_eq!(ops::size_if_known(&deferred), None);
    assert!(!ops::over_set_bound(&deferred));
    assert_eq!(visits.load(Ordering::Relaxed), 0, "sizing enumerated the component");
    // A known empty component decides the product even beside an unknown one.
    let empty_product = ops::product(vec![custom.clone(), Value::empty_set()]).unwrap();
    assert_eq!(ops::size_fact(&empty_product), ops::SizeFact::Known(0));
    // Known components multiply; an overflow makes the product overflow.
    assert_eq!(ops::size_fact(&ops::product(vec![interval(1, 3), interval(1, 4)]).unwrap()), ops::SizeFact::Known(12));
    assert_eq!(ops::size_fact(&fcn_set(5, 121)), ops::SizeFact::Overflow);
}

#[test]
fn singleton_domains_are_not_empty() {
    // `SUBSET {}` is `{{}}` and `[{} -> {1}]` is `{<<>>}`, one element each:
    // an emptiness check must not prune them (TLC reaches the transition they
    // enable).
    let _b = Bound::new(10);
    let subset = ops::powerset(&Value::empty_set()).unwrap();
    assert_eq!(ops::size_fact(&subset), ops::SizeFact::Known(1));
    assert_ne!(ops::size_fact(&subset), ops::SizeFact::Known(0));
    let fcn = ops::fcn_set(&Value::empty_set(), &set([1])).unwrap();
    assert_eq!(ops::size_fact(&fcn), ops::SizeFact::Known(1));
    // (An undecided domain with an empty range is 1 or 0, not known 0.)
    let custom = Value::LazySet(Arc::new(LazySet::Custom(Box::new(UnknownSet))));
    let maybe = ops::fcn_set(&custom, &Value::empty_set()).unwrap();
    assert_eq!(ops::size_fact(&maybe), ops::SizeFact::Unknown);
    // A non-empty domain with an empty range is empty.
    let empty_range = ops::fcn_set(&set([1, 2]), &Value::empty_set()).unwrap();
    assert_eq!(ops::size_fact(&empty_range), ops::SizeFact::Known(0));
}

/// A set whose size is only known by enumerating it (`Unknown` as a fact).
#[derive(Debug)]
struct UnknownSet;
impl tlx_value::CustomSet for UnknownSet {
    fn contains(&self, _: &Value) -> tlx_value::Result<bool> {
        Ok(true)
    }
    fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
        unreachable!("a fact must not enumerate")
    }
    fn for_each(&self, _: &mut dyn FnMut(Value) -> tlx_value::Result<bool>) -> tlx_value::Result<Option<bool>> {
        unreachable!("a fact must not enumerate")
    }
}

#[test]
fn ksubset_facts_do_not_enumerate_the_base() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    /// Counts enumerations of a lazy base.
    #[derive(Debug)]
    struct Counting(Arc<AtomicBool>);
    impl tlx_value::CustomSet for Counting {
        fn contains(&self, _: &Value) -> tlx_value::Result<bool> {
            Ok(true)
        }
        fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
            self.0.store(true, Ordering::Relaxed);
            Ok(Some((0..12).map(Value::Int).collect()))
        }
        fn for_each(&self, _: &mut dyn FnMut(Value) -> tlx_value::Result<bool>) -> tlx_value::Result<Option<bool>> {
            self.0.store(true, Ordering::Relaxed);
            Ok(Some(true))
        }
    }

    let _b = Bound::new(10);
    let visited = Arc::new(AtomicBool::new(false));
    let base = Value::LazySet(Arc::new(LazySet::Custom(Box::new(Counting(visited.clone())))));
    // (The constant cases of `k` decide without the base.)
    assert_eq!(ops::size_fact(&ops::ksubset(&Value::Int(-1), &base).unwrap()), ops::SizeFact::Known(0));
    assert_eq!(ops::size_fact(&ops::ksubset(&Value::Int(0), &base).unwrap()), ops::SizeFact::Known(1));
    // A `k` that needs the base's size stays unknown — without enumerating it.
    assert_eq!(ops::size_fact(&ops::ksubset(&Value::Int(2), &base).unwrap()), ops::SizeFact::Unknown);
    assert!(!ops::over_set_bound(&ops::ksubset(&Value::Int(2), &base).unwrap()));
    assert!(!visited.load(Ordering::Relaxed), "the size fact enumerated the base");
    // A known base computes the binomial.
    assert_eq!(ops::size_fact(&ops::ksubset(&Value::Int(2), &set(1..=4)).unwrap()), ops::SizeFact::Known(6));
    assert_eq!(ops::size_fact(&ops::ksubset(&Value::Int(5), &set(1..=4)).unwrap()), ops::SizeFact::Known(0));
}

#[test]
fn a_comparison_converts_a_lazy_set_only_when_the_bound_allows_it() {
    use tlx_value::order::{cmp_tlc, eq_tlc};

    // `[1..2 -> 1..4]` (16 functions) compared with an explicit set: TLC
    // converts the function set first, so the bound applies (a size shortcut
    // may not answer before the conversion).
    let fcn = fcn_set(2, 4);
    {
        let _b = Bound::new(10);
        assert!(eq_tlc(&fcn, &Value::empty_set()).is_err(), "16 > 10 must report the bound");
        assert!(cmp_tlc(&fcn, &Value::empty_set()).is_err(), "normalizing it must report the bound");
        // Two function sets of the same kind compare structurally (equality),
        // while ordering them converts (TLC reports the bound at 10), even for
        // a smaller set against a larger one.
        assert_eq!(eq_tlc(&fcn, &fcn_set(2, 4)), Ok(true));
        assert!(cmp_tlc(&fcn, &fcn_set(2, 4)).is_err());
        assert_eq!(eq_tlc(&fcn_set(2, 3), &fcn_set(2, 4)), Ok(false));
        assert!(cmp_tlc(&fcn_set(2, 3), &fcn_set(2, 4)).is_err(), "9 and 16 must not be ordered by size");
        // A powerset's conversion is exempt from the growth bound: the size
        // decides without enumerating its 32,768 subsets.
        assert_eq!(eq_tlc(&ops::powerset(&interval(1, 15)).unwrap(), &Value::empty_set()), Ok(false));
    }
    {
        // The same comparison at a bound that admits the conversion succeeds.
        let _b = Bound::new(16);
        assert_eq!(eq_tlc(&fcn, &Value::empty_set()), Ok(false));
        assert_eq!(cmp_tlc(&fcn, &Value::empty_set()), Ok(std::cmp::Ordering::Greater));
        assert_eq!(cmp_tlc(&fcn, &fcn_set(2, 4)), Ok(std::cmp::Ordering::Equal));
        assert_eq!(cmp_tlc(&fcn_set(2, 3), &fcn_set(2, 4)), Ok(std::cmp::Ordering::Less));
    }
}

#[test]
fn an_ordering_shortcut_accounts_for_nested_conversions() {
    use tlx_value::order::eq_tlc;

    // A set of functions over a 16-element product domain holds one element,
    // but comparing it with an explicit set converts the domain (TLC's
    // `convertAndCache`), which reaches the bound; the same holds for a
    // powerset over that base. An interval powerset stays cheap.
    let edges = ops::product(vec![interval(1, 4), interval(1, 4)]).unwrap();
    let maps = ops::fcn_set(&edges, &set([0])).unwrap();
    let subsets = ops::powerset(&edges).unwrap();
    let cheap_subsets = ops::powerset(&interval(1, 15)).unwrap();
    {
        let _b = Bound::new(10);
        assert!(eq_tlc(&maps, &Value::empty_set()).is_err());
        assert!(eq_tlc(&subsets, &Value::empty_set()).is_err());
        assert_eq!(eq_tlc(&cheap_subsets, &Value::empty_set()), Ok(false));
    }
    {
        let _b = Bound::new(16);
        assert_eq!(eq_tlc(&maps, &Value::empty_set()), Ok(false));
        assert_eq!(eq_tlc(&subsets, &Value::empty_set()), Ok(false));
    }
}

#[test]
fn an_eager_union_checks_the_left_copy_first() {
    // TLC's cup appends the left operand before it converts or compares the
    // right: over the bound the union reports it instead of a type error, and
    // an overlapping interval union never scans the left side.
    let union = |a: &Value, b: &Value| ops::union(a, b);
    {
        let _b = Bound::new(10);
        let unknown = Value::set_literal(vec![Value::str("unknown")]).unwrap();
        let e = union(&interval(1, 11), &unknown).unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
        let e = union(&interval(1, 11), &interval(5, 12)).unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
        let e = union(&interval(1, 4_000_000), &interval(2_000_000, 4_000_001)).unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
    }
    {
        let _b = Bound::new(16);
        assert_eq!(union(&interval(1, 11), &interval(5, 12)).unwrap(), set(1..=12));
        assert!(union(&interval(1, 11), &Value::set_literal(vec![Value::str("unknown")]).unwrap()).is_err());
    }
}

#[test]
fn an_interval_union_is_enumerated_like_tlcs() {
    let _b = Bound::new(10);
    // TLC's `IntervalValue.cup` builds a `SetEnumValue` even when the right
    // operand adds nothing: a consumer that distinguishes the representation
    // (a function constructor makes an enumerated-domain function, whose
    // `EXCEPT` at an absent model-value key leaves it unchanged) must see a
    // set, not the interval.
    let u = ops::union(&interval(1, 3), &Value::empty_set()).unwrap();
    assert!(matches!(u, Value::Set(_)), "an interval union must be an enumerated set: {u}");
    assert_eq!(u, interval(1, 3));
    // A `Value::Set` keeps the identity (no copy), after the bound check.
    let s = set(1..=3);
    assert_eq!(ops::union(&s, &Value::empty_set()).unwrap(), s);
}

#[test]
fn big_union_merges_normalized_families_incrementally() {
    // Overlapping neighborhoods: 512 sets of 512 elements (262,144 occurrences),
    // shifting by 1 each time -> 1,023 distinct elements. At bound 512, the
    // k-way merge stops as soon as distinct element 513 is reached without
    // flattening every occurrence; at bound 1,023 it succeeds.
    let neighborhoods: Vec<Value> = (0..512).map(|i| set(i..i + 512)).collect();
    let family = Value::set_literal(neighborhoods).unwrap();
    {
        let _b = Bound::new(512);
        let e = ops::big_union(&family).unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
    }
    {
        let _b = Bound::new(1023);
        let u = ops::big_union(&family).unwrap();
        assert_eq!(ops::size(&u).unwrap(), 1023);
    }

    // Sparse ring: 4,095 two-element edges covering 4,096 distinct nodes
    // (8,190 occurrences > bound 4,096, distinct == 4,096).
    let edges: Vec<Value> = (0..4095).map(|i| set([i, i + 1])).collect();
    let ring = Value::set_literal(edges).unwrap();
    {
        let _b = Bound::new(4096);
        let u = ops::big_union(&ring).unwrap();
        assert_eq!(ops::size(&u).unwrap(), 4096);
    }
    {
        let _b = Bound::new(4095);
        let e = ops::big_union(&ring).unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
    }

    // Differently sized normalized integer sets stay `LazySet::Enum` at the
    // outer level, yet still take the k-way merge when their elements share a
    // comparison family.
    let mixed_lens = Value::set_literal(vec![set(1..=6), set(3..=8), set(1..=2)]).unwrap();
    assert!(matches!(mixed_lens, Value::LazySet(_)));
    {
        let _b = Bound::new(10);
        assert_eq!(ops::big_union(&mixed_lens).unwrap(), set(1..=8));
    }
}

#[test]
fn set_algebra_bound_uses_canonical_homogeneous_sets() {
    // Documented difference D-35: homogeneous explicit sets are immutable and
    // canonical, so `\cup`, `\cap` and `\` enforce `-maxSetSize` on distinct
    // elements rather than depending on duplicate-entry operand order or
    // mutable in-place normalization state.
    let _b = Bound::new(10);
    let dup_pair = Value::set_literal(vec![Value::Int(1), Value::Int(1)]).unwrap();
    let rest = interval(2, 10);
    assert_eq!(ops::union(&dup_pair, &rest).unwrap(), set(1..=10));
    assert_eq!(ops::union(&rest, &dup_pair).unwrap(), set(1..=10));

    // Distinct-entry interval copying still follows TLC's receiver rule:
    // `{} \cup (1..11)` succeeds, `(1..11) \cup {}` reports the bound.
    assert_eq!(ops::union(&Value::empty_set(), &interval(1, 11)).unwrap(), interval(1, 11));
    let e = ops::union(&interval(1, 11), &Value::empty_set()).unwrap_err();
    assert!(e.to_string().contains("too many elements"), "{e}");

    // A literal with 11 raw entries and 10 distinct elements fits bound 10 in
    // union, intersection, and difference regardless of prior `Cardinality`.
    let mut elems: Vec<Value> = (1..=10).map(Value::Int).collect();
    elems.push(Value::Int(1));
    let ten_distinct = Value::set_literal(elems).unwrap();
    assert_eq!(ops::union(&ten_distinct, &set([1])).unwrap(), set(1..=10));
    assert_eq!(ops::intersect(&ten_distinct, &interval(1, 10)).unwrap(), set(1..=10));
    assert_eq!(ops::difference(&ten_distinct, &Value::empty_set()).unwrap(), set(1..=10));

    // A literal with 11 *distinct* elements still fails on eager union,
    // intersection, and difference at 10.
    let eleven_distinct = Value::set_literal((1..=11).map(Value::Int).collect()).unwrap();
    for res in [
        ops::union(&eleven_distinct, &set([1])),
        ops::intersect(&eleven_distinct, &interval(1, 11)),
        ops::difference(&eleven_distinct, &Value::empty_set()),
    ] {
        let e = res.unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
    }
}

#[test]
fn mixed_filter_reducible_fails_fast_at_bound_before_incomparable_tail() {
    // A deferred enumeration (`{1..11, "sentinel"}`) intersected with `1..11`
    // or minus `{}` must report "too many elements" on the 11th kept integer
    // before testing the trailing string sentinel.
    let mut elems: Vec<Value> = (1..=11).map(Value::Int).collect();
    elems.push(Value::str("sentinel"));
    let mixed = Value::set_literal(elems).unwrap();
    {
        let _b = Bound::new(10);
        let e = ops::intersect(&mixed, &interval(1, 11)).unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
        let e = ops::difference(&mixed, &Value::empty_set()).unwrap_err();
        assert!(e.to_string().contains("too many elements"), "{e}");
    }
    {
        let _b = Bound::new(11);
        let e = ops::intersect(&mixed, &interval(1, 11)).unwrap_err();
        assert!(!e.to_string().contains("too many elements"), "should reach string comparison: {e}");
    }
}

#[test]
fn powerset_of_deferred_31_tuples_refuses_collection_without_allocating() {
    use tlx_value::ValueErrorKind;

    // 31 distinct tuples of different lengths remain a deferred `LazySet::Enum`.
    // Its powerset has `Unknown` size_fact (no normalization during sizing),
    // streams early-stop cleanly, and rejects full collection (`ops::enumerate`)
    // with `Overflow` before allocating any output subsets.
    let tuples: Vec<Value> = (1..=31).map(|len| Value::Tuple(vec![Value::Int(1); len].into())).collect();
    let base = Value::set_literal(tuples).unwrap();
    assert!(matches!(base, Value::LazySet(_)), "differently sized tuples stay deferred");
    let powerset = ops::powerset(&base).unwrap();

    assert_eq!(ops::size_fact(&powerset), ops::SizeFact::Unknown);
    assert!(matches!(ops::materialization_error(&powerset), Some(e) if e.kind == ValueErrorKind::Overflow));

    // Streaming visitor can still stop after the first subset (`{}`).
    let mut seen = Vec::new();
    let done = ops::for_each_enumerated(&powerset, &mut |e| {
        seen.push(e);
        Ok(false)
    })
    .unwrap();
    assert!(!done);
    assert_eq!(seen, vec![Value::empty_set()]);

    // Full collection must fail immediately with `Overflow`.
    let e = ops::enumerate(&powerset).unwrap_err();
    assert_eq!(e.kind, ValueErrorKind::Overflow, "{e}");
    assert!(e.to_string().contains("Overflow when computing"), "{e}");
}

#[test]
fn powerset_of_compositional_base_over_lazy_filter_reports_overflow_without_collecting_base() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use tlx_value::ValueErrorKind;

    /// A lazy filter yielding `1..=n`, tracking whether it was evaluated.
    #[derive(Debug)]
    struct RangeFilter {
        n: i64,
        visits: Arc<AtomicUsize>,
    }
    impl tlx_value::CustomSet for RangeFilter {
        fn contains(&self, v: &Value) -> tlx_value::Result<bool> {
            Ok(matches!(v, Value::Int(i) if *i >= 1 && *i <= self.n))
        }
        fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
            self.visits.fetch_add(1, Ordering::Relaxed);
            Ok(Some((1..=self.n).map(Value::Int).collect()))
        }
        fn for_each(&self, f: &mut dyn FnMut(Value) -> tlx_value::Result<bool>) -> tlx_value::Result<Option<bool>> {
            self.visits.fetch_add(1, Ordering::Relaxed);
            for i in 1..=self.n {
                if !f(Value::Int(i))? {
                    return Ok(Some(false));
                }
            }
            Ok(Some(true))
        }
    }

    // 1. `SUBSET (SUBSET Eligible)` with 20 eligible members (`QuorumFamilies20`):
    //    `size_fact` stays `Unknown` with zero filter evaluations, streaming
    //    stops early on `{}`, and `ops::enumerate` reports outer `Overflow`
    //    without materializing the 2^20 inner quorums.
    {
        let _b = Bound::new(limits::DEFAULT_MAX_SET_SIZE);
        let visits = Arc::new(AtomicUsize::new(0));
        let eligible = Value::LazySet(Arc::new(LazySet::Custom(Box::new(RangeFilter { n: 20, visits: visits.clone() }))));
        let quorums = ops::powerset(&eligible).unwrap();
        let families = ops::powerset(&quorums).unwrap();

        assert_eq!(ops::size_fact(&families), ops::SizeFact::Unknown);
        assert_eq!(visits.load(Ordering::Relaxed), 0, "size_fact must not evaluate Eligible");

        let e = ops::enumerate(&families).unwrap_err();
        assert_eq!(visits.load(Ordering::Relaxed), 1, "only Eligible should be sized once");
        assert_eq!(e.kind, ValueErrorKind::Overflow, "{e}");
        assert!(e.to_string().contains("Overflow when computing"), "{e}");
    }

    // 2. `SUBSET [1..5 -> Eligible]` with 2 eligible members at bound 10 (`Policy8`):
    //    `|[1..5 -> Eligible]| = 32 >= 31`, so collecting the outer powerset
    //    reports outer powerset `Overflow` rather than the inner function-set
    //    `-maxSetSize` growth error.
    {
        let _b = Bound::new(10);
        let visits = Arc::new(AtomicUsize::new(0));
        let eligible = Value::LazySet(Arc::new(LazySet::Custom(Box::new(RangeFilter { n: 2, visits: visits.clone() }))));
        let policies = ops::fcn_set(&interval(1, 5), &eligible).unwrap();
        let power_policies = ops::powerset(&policies).unwrap();

        assert_eq!(ops::size_fact(&power_policies), ops::SizeFact::Unknown);
        assert_eq!(visits.load(Ordering::Relaxed), 0);

        let e = ops::enumerate(&power_policies).unwrap_err();
        assert_eq!(e.kind, ValueErrorKind::Overflow, "{e}");
        assert!(e.to_string().contains("Overflow when computing"), "{e}");
        assert!(!e.to_string().contains("too many elements"), "{e}");
    }
}
