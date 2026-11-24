//! Shared value-operation policy: the primitives that more than one value
//! representation or executor reads.
//!
//! - `Witness`, `Schedule`, `KeyType` and `SCAN_LIMIT` describe how TLC built
//!   a finite function, which keys it admits and how it searches them; the
//!   schedule decides which comparison errors are observable. The boxed
//!   interpreter (`ops::fcns`), the stored-order lookup (`ir::store::ops`) and
//!   the compiled key-rank plan (`compile::types`) consume them.
//! - `Absent` is the missing-key rule the compiled tier carries on its
//!   `MapPutPlan` (`compile::ir`): EXCEPT leaves the function unchanged and
//!   `:>`/`@@` insert.
//! - `Direction` names the operand a comparison is directed by; `operands`
//!   orders an application or lookup (stored key first) and a membership or
//!   `@@` domain probe (probe first) as TLC's `compareTo`/`equals` receivers
//!   do.
//! - `ComparisonKind` and `FunctionComparison` are the ordered decisions the
//!   boxed (`value::order`) and stored (`ir::store::order`) finite-function
//!   comparison share.
//!
//! The unified per-operation plan (one plan object for every backend) is not
//! implemented: the operations of docs/value-store.md §4.2 run without a shared
//! plan object, so nothing in this module should be read as that contract.

use std::cmp::Ordering;
use std::ops::Range;

use crate::value::{FcnDom, Value};

/// How TLC built a function value, as far as it changes the result or
/// the errors of an operation (a witness of its evaluation behavior; equal
/// functions can have different witnesses, see `Value::Fcn`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Witness {
    /// `TupleValue`: domain `1..n`, also the empty function `<<>>`.
    Tuple,
    /// `RecordValue`: a non-empty domain of strings.
    Record,
    /// `FcnRcdValue` over an enumerated domain: keys are found by equality.
    Enumerated,
    /// `FcnRcdValue` over an integer interval: keys must be integers.
    Interval,
}

impl Witness {
    /// The witness of a finite function value (None for lazy functions and
    /// non-functions).
    pub fn of(f: &Value) -> Option<Witness> {
        match f {
            Value::Tuple(_) => Some(Witness::Tuple),
            Value::Record(_) => Some(Witness::Record),
            Value::Fcn(_, FcnDom::Enumerated) => Some(Witness::Enumerated),
            Value::Fcn(_, FcnDom::Interval) => Some(Witness::Interval),
            _ => None,
        }
    }

    /// Witness assigned by `Value::fcn_canonical_sorted` to sorted, distinct
    /// domain keys `dom`.
    pub fn canonical_of_sorted_keys<'a>(mut dom: impl Iterator<Item = &'a Value>) -> Witness {
        let Some(first) = dom.next() else {
            return Witness::Tuple;
        };
        match first {
            Value::Int(lo) => {
                let mut expected = *lo;
                for k in dom {
                    expected = match expected.checked_add(1) {
                        Some(n) if *k == Value::Int(n) => n,
                        _ => return Witness::Enumerated,
                    };
                }
                if *lo == 1 {
                    Witness::Tuple
                } else {
                    Witness::Interval
                }
            }
            Value::Str(_) => {
                if dom.all(|k| matches!(k, Value::Str(_))) {
                    Witness::Record
                } else {
                    Witness::Enumerated
                }
            }
            _ => Witness::Enumerated,
        }
    }

    /// Whether `DOMAIN f` for a function with this witness produces an integer
    /// interval (`Value::Interval`) rather than an enumerated `Value::Set`:
    /// `Tuple` (`1..n`) and `Interval` (`lo..hi`) yield an interval, while
    /// `Record` and `Enumerated` yield a `Value::Set`.
    pub fn domain_is_interval(self) -> bool {
        matches!(self, Witness::Tuple | Witness::Interval)
    }

    /// Build the `DOMAIN f` value for a finite function with this witness and
    /// sorted, distinct keys `keys`.
    pub fn domain_value<'a>(self, mut keys: impl ExactSizeIterator<Item = &'a Value> + DoubleEndedIterator) -> Value {
        if self.domain_is_interval() {
            match (keys.next(), keys.next_back()) {
                (Some(Value::Int(lo)), Some(Value::Int(hi))) => Value::Interval(*lo, *hi),
                (Some(Value::Int(lo)), None) => Value::Interval(*lo, *lo),
                _ => Value::Interval(1, 0),
            }
        } else {
            Value::Set(keys.cloned().collect())
        }
    }

    /// The keys a function of this witness accepts as arguments at all:
    /// any other key is a type error, also when it is absent and the
    /// operation (EXCEPT) would leave an absent key unchanged.
    pub fn key_type(self) -> KeyType {
        match self {
            Witness::Tuple | Witness::Interval => KeyType::Int,
            Witness::Record => KeyType::Str,
            Witness::Enumerated => KeyType::Any,
        }
    }

    /// TLC's search schedule for a key of a function of this witness with
    /// `len` entries.
    pub fn schedule(self, len: usize) -> Schedule {
        match self {
            Witness::Tuple | Witness::Interval => Schedule::Offset,
            Witness::Record => Schedule::Field,
            Witness::Enumerated if len < SCAN_LIMIT => Schedule::Scan,
            Witness::Enumerated => Schedule::Bisect,
        }
    }
}

/// Structural kind order for function domains. This is deliberately distinct
/// from fallible TLC comparison of mapped values: unequal domain kinds make
/// functions unequal rather than invalid (D-31).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ComparisonKind {
    ModelValue,
    Bool,
    Int,
    Str,
    Set,
    Function,
}

impl ComparisonKind {
    pub fn of(v: &Value) -> Self {
        match v {
            Value::ModelValue(_) => Self::ModelValue,
            Value::Bool(_) => Self::Bool,
            Value::Int(_) => Self::Int,
            Value::Str(_) => Self::Str,
            Value::Set(_) | Value::Interval(..) | Value::LazySet(_) => Self::Set,
            Value::Tuple(_) | Value::Record(_) | Value::Fcn(..) | Value::LazyFcn(_) => Self::Function,
        }
    }
}

/// The ordered decisions common to boxed and stored finite-function
/// comparison. Consumers keep their representation-specific loops and choose
/// structural comparison for domains, fallible TLC comparison for values.
/// Compare `length_order` first, then every domain key, then mapped values;
/// this order determines which comparison errors can be observed.
#[derive(Clone, Debug)]
pub struct FunctionComparison {
    pub length_order: Ordering,
    pub domains: Range<usize>,
    pub values: Range<usize>,
}

impl FunctionComparison {
    #[inline]
    pub fn new(left_len: usize, right_len: usize, left_tuple: bool, right_tuple: bool) -> Self {
        let length_order = left_len.cmp(&right_len);
        let len = if length_order == Ordering::Equal { left_len } else { 0 };
        // Two tuples have the same implicit domain after comparing lengths.
        let domains = if left_tuple && right_tuple { 0..0 } else { 0..len };
        Self { length_order, domains, values: 0..len }
    }
}

/// Keys a witness admits (`Witness::key_type`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum KeyType {
    Int,
    Str,
    Any,
}

impl KeyType {
    pub fn admits(self, k: &Value) -> bool {
        match self {
            KeyType::Int => matches!(k, Value::Int(_)),
            KeyType::Str => matches!(k, Value::Str(_)),
            KeyType::Any => true,
        }
    }
}

/// Entries below which an enumerated function is searched linearly
/// (`FcnRcdValue.select`); from here on by bisection with `compareTo`.
pub const SCAN_LIMIT: usize = 32;

/// How a key is searched in a function's domain. The schedules see
/// different comparison errors for ill-typed keys, so a faster lookup must
/// either prove the key comparable or follow the schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Schedule {
    /// An integer offset from the first key (tuples, interval domains).
    Offset,
    /// A record field by name.
    Field,
    /// Linear search with `equals` from the first key.
    Scan,
    /// Binary search with `compareTo`.
    Bisect,
}

/// What a put does when its key is absent from the function's domain (the
/// compiled tier's `MapPutPlan`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Absent {
    /// EXCEPT: the function is unchanged and the replacement is not
    /// evaluated (TLC warns).
    Unchanged,
    /// `k :> v`, `@@`: the key is added.
    Insert,
}

/// Which operand a comparison is directed by: TLC calls `compareTo` /
/// `equals` on one value with the other as argument, and the receiver
/// decides which mixtures are errors (`order::cmp_tlc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Direction {
    /// The stored key of a function lookup (`FcnRcdValue.select` compares
    /// its domain element with the argument).
    Stored,
    /// The probe of a membership test or `@@` domain search (`v \in S`
    /// compares `v` with each element).
    Probe,
}

impl Direction {
    /// Operand order for a search over stored entries: only a probe-directed
    /// operation reverses the supplied (stored, probe) order.
    #[inline]
    pub fn operands<T>(self, stored: T, probe: T) -> (T, T) {
        match self {
            Self::Stored => (stored, probe),
            Self::Probe => (probe, stored),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops;

    fn int(i: i64) -> Value {
        Value::Int(i)
    }

    /// The executable rules agree with the interpreter's operations on
    /// every witness (the interpreter is the reference implementation).
    #[test]
    fn witness_rules_match_the_interpreter() {
        let m = Value::model_value("m");
        let s = Value::str("a");
        let fns = [
            Value::tuple(vec![int(10), int(20)]),
            Value::tuple(vec![]),
            Value::record(vec![(crate::Sym::new("a"), int(1))]),
            Value::fcn_rcd_from_pairs(vec![(int(1), int(10)), (int(2), int(20))]).unwrap(),
            Value::empty_fcn(),
            Value::fcn_over(&Value::Interval(0, 1), vec![(int(0), int(1)), (int(1), int(2))]).unwrap(),
        ];
        for f in &fns {
            let w = Witness::of(f).unwrap();
            for k in [int(1), int(7), m.clone(), s.clone()] {
                let admitted = w.key_type().admits(&k);
                let selected = ops::select(f, &k);
                // An admitted key never raises a type error (absent keys are None);
                // a rejected key raises one (enumerated domains admit everything,
                // but comparing incomparable keys may still fail there).
                if admitted && w != Witness::Enumerated {
                    assert!(selected.is_ok(), "{f} [{k}]: {selected:?}");
                }
                if !admitted {
                    assert!(selected.is_err(), "{f} [{k}] should be rejected");
                }
            }
        }
    }

    #[test]
    fn schedules_follow_the_size_limit() {
        assert_eq!(Witness::Enumerated.schedule(SCAN_LIMIT - 1), Schedule::Scan);
        assert_eq!(Witness::Enumerated.schedule(SCAN_LIMIT), Schedule::Bisect);
        assert_eq!(Witness::Tuple.schedule(1000), Schedule::Offset);
    }
}
