mod common;

use std::collections::HashMap;
use std::sync::Arc;

use common::*;
use tlx_base::frame::FrameWriter;
use tlx_value::arith::*;
use tlx_value::fingerprint::{fingerprint, Fingerprinter};
use tlx_value::ser::Writer;
use tlx_value::{ops, LazySet, Sym, Value};

const MIN: i64 = i32::MIN as i64;
const MAX: i64 = i32::MAX as i64;

#[test]
fn arithmetic() {
    assert_eq!(add(MAX - 1, 1).unwrap(), MAX);
    assert_eq!(err_msg(add(MAX, 1)), "Overflow when computing 2147483647+1");
    assert!(add(MIN, -1).is_err());
    assert_eq!(sub(MIN + 1, 1).unwrap(), MIN);
    assert!(sub(MIN, 1).is_err());
    assert!(sub(0, MIN).is_err());
    assert_eq!(mul(65536, 32767).unwrap(), 2147418112);
    assert!(mul(65536, 32768).is_err());
    assert_eq!(mul(-65536, 32768).unwrap(), MIN);
    // ^
    assert_eq!(pow(2, 10).unwrap(), 1024);
    assert_eq!(pow(-2, 31).unwrap(), MIN);
    assert!(pow(2, 31).is_err());
    assert_eq!(pow(5, 0).unwrap(), 1);
    assert_eq!(err_msg(pow(0, 0)), "0^0 is undefined.");
    assert!(pow(2, -1).is_err());
    assert_eq!(pow(1, MAX).unwrap(), 1);
    assert_eq!(pow(-1, MAX).unwrap(), -1);
    assert_eq!(pow(0, 5).unwrap(), 0);
    assert!(pow(3, MAX).is_err());
    // unary minus
    assert_eq!(neg(MAX).unwrap(), -MAX);
    assert_eq!(err_msg(neg(MIN)), "Overflow when computing --2147483648");
    // %
    assert_eq!(modulo(7, 3).unwrap(), 1);
    assert_eq!(modulo(-7, 3).unwrap(), 2);
    assert_eq!(modulo(MIN, MAX).unwrap(), MAX - 1);
    assert!(modulo(7, 0).is_err());
    assert!(modulo(7, -3).is_err());
    // \div (Integers): floor
    assert_eq!(div_floor(7, 2).unwrap(), 3);
    assert_eq!(div_floor(-7, 2).unwrap(), -4);
    assert_eq!(div_floor(7, -2).unwrap(), -4);
    assert_eq!(div_floor(-7, -2).unwrap(), 3);
    assert_eq!(div_floor(-1, 2).unwrap(), -1);
    assert_eq!(div_floor(1, -2).unwrap(), -1);
    assert_eq!(div_floor(-6, 2).unwrap(), -3);
    assert_eq!(err_msg(div_floor(1, 0)), "The second argument of \\div is 0.");
    assert!(div_floor(MIN, -1).is_err());
    // \div (Naturals): truncation corrected only when the quotient is negative
    assert_eq!(div_naturals(7, 2).unwrap(), 3);
    assert_eq!(div_naturals(-7, 2).unwrap(), -4);
    assert_eq!(div_naturals(7, -2).unwrap(), -4);
    assert_eq!(div_naturals(-7, -2).unwrap(), 3);
    assert_eq!(div_naturals(-1, 2).unwrap(), 0); // floor would be -1
    assert_eq!(div_naturals(1, -2).unwrap(), 0);
    assert_eq!(div_naturals(-6, 2).unwrap(), -3);
    assert_eq!(div_naturals(MIN, -1).unwrap(), MIN); // Java int wrap-around
    assert!(div_naturals(1, 0).is_err());
    // DyadicRationals GCD: commons-math ArithmeticUtils.gcd (TLC's Reduce override)
    assert_eq!(gcd(12, 18).unwrap(), 6);
    assert_eq!(gcd(0, 2).unwrap(), 2);
    assert_eq!(gcd(-6, 4).unwrap(), 2);
    assert_eq!(gcd(4, -6).unwrap(), 2);
    assert_eq!(gcd(0, 0).unwrap(), 0);
    assert_eq!(gcd(MIN, 2).unwrap(), 2);
    assert_eq!(gcd(MIN, 6).unwrap(), 2);
    assert!(gcd(MIN, 0).is_err()); // 2^31
    assert!(gcd(MIN, MIN).is_err());
    assert_eq!(gcd(MAX, 0).unwrap(), MAX);
}

#[test]
fn fingerprints_are_representation_independent() {
    let fp = |v: &Value| fingerprint(v).unwrap();
    assert_eq!(fp(&ops::interval(1, 3)), fp(&ints(&[1, 2, 3])));
    assert_eq!(fp(&ops::interval(3, 1)), fp(&Value::empty_set()));
    let p = ops::powerset(&ints(&[1, 2])).unwrap();
    assert_eq!(fp(&p), fp(&p.normalize().unwrap()));
    let c = ops::union(&ops::powerset(&ints(&[1])).unwrap(), &ops::powerset(&ints(&[1, 2])).unwrap()).unwrap();
    assert_eq!(fp(&c), fp(&p));
    let u = ops::big_union(&set(vec![ops::interval(1, 2), ops::interval(2, 3)])).unwrap();
    assert_eq!(fp(&u), fp(&ops::interval(1, 3)));
    assert_eq!(fp(&scale(ops::interval(1, 3), 2)), fp(&tup(vec![int(2), int(4), int(6)])));
    assert_eq!(fp(&set(vec![ops::interval(1, 2)])), fp(&set(vec![ints(&[1, 2])])));
    let r1 = Value::record(vec![(Sym::new("fp_b"), int(1)), (Sym::new("fp_a"), int(2))]);
    let r2 = fcn(vec![(s("fp_a"), int(2)), (s("fp_b"), int(1))]);
    assert_eq!(fp(&r1), fp(&r2));
    let f1 = fcn(vec![(int(1), s("x")), (int(2), s("y"))]);
    assert_eq!(fp(&f1), fp(&tup(vec![s("x"), s("y")])));
    // distinct values
    assert_ne!(fp(&Value::empty_set()), fp(&tup(vec![])));
    assert_ne!(fp(&int(1)), fp(&s("1")));
    assert_ne!(fp(&s("a")), fp(&mv("a")));
    assert_ne!(fp(&Value::TRUE), fp(&int(1)));
    assert_ne!(fp(&ints(&[1, 2])), fp(&tup(vec![int(1), int(2)])));
    assert_ne!(fp(&tup(vec![int(1), int(2)])), fp(&tup(vec![int(2), int(1)])));
    assert_ne!(fp(&set(vec![ints(&[1]), ints(&[2])])), fp(&set(vec![ints(&[1, 2])])));
    assert_ne!(fp(&tup(vec![tup(vec![int(1)]), int(2)])), fp(&tup(vec![int(1), tup(vec![int(2)])])));
    // Fingerprinter is order sensitive
    let mut a = Fingerprinter::new();
    a.add(&int(1)).unwrap();
    a.add(&int(2)).unwrap();
    let mut b = Fingerprinter::new();
    b.add(&int(2)).unwrap();
    b.add(&int(1)).unwrap();
    assert_ne!(a.finish(), b.finish());
    let mut c = Fingerprinter::new();
    c.add(&tup(vec![int(1), int(2)])).unwrap();
    assert_ne!(a.finish(), c.finish());
    // infinite values cannot be fingerprinted
    assert!(fingerprint(&Value::LazySet(Arc::new(LazySet::Nat))).is_err());
    assert!(fingerprint(&scale(Value::LazySet(Arc::new(LazySet::Nat)), 1)).is_err());
}

/// Fixed golden fingerprints (CODE-21): the exact bits of the current
/// algorithm, not a self-comparison. The values pin persisted checkpoints and
/// state identity, so a changed algorithm must be a deliberate change here,
/// never an auto-refreshed expectation. Scalars are intern-order independent
/// because strings and model values hash their text (see `hash_bytes`); a
/// multi-field record is not, because its field order is `Sym`/intern order,
/// so the one composite below interns its own field names (see the guard).
#[test]
fn fingerprints_match_fixed_goldens() {
    let fp = |v: &Value| fingerprint(v).unwrap();
    // scalars
    assert_eq!(fp(&int(0)), 0x9d3d_aea7_0617_dd06);
    assert_eq!(fp(&int(42)), 0xd545_61c8_76b6_a418);
    assert_eq!(fp(&int(-1)), 0xa924_843c_fadd_f272);
    assert_eq!(fp(&Value::TRUE), 0xbcc0_0b63_37f5_1b79);
    assert_eq!(fp(&Value::FALSE), 0xc821_f96a_b47d_6bd0);
    // string content: the same text fingerprints the same however it is built
    assert_eq!(fp(&s("abc")), 0x8063_6b58_d404_d7d2);
    assert_eq!(fp(&s("abd")), 0x8f30_2ef3_3fe4_08f0);
    assert_eq!(fp(&Value::str(&String::from("content-golden"))), 0xa599_31db_c78a_a3cd);
    assert_eq!(fp(&mv("m")), 0x0d86_a032_7e5a_f9d0);
    // composites: set (order-independent), tuple, interval, function
    assert_eq!(fp(&Value::empty_set()), 0x6f99_a988_1e2a_1690);
    assert_eq!(fp(&set(vec![int(1), int(2)])), 0x78fa_1d08_54b7_24d3);
    assert_eq!(fp(&set(vec![int(2), int(1)])), 0x78fa_1d08_54b7_24d3);
    assert_eq!(fp(&tup(vec![int(1), s("a")])), 0x1040_18a7_b5a1_7fdf);
    assert_eq!(fp(&ops::interval(1, 3)), 0x3f59_8803_f9f7_4bba);
    assert_eq!(fp(&fcn(vec![(int(1), int(2)), (int(3), int(4))])), 0xa33d_1cb5_0476_013a);
    // A record and the equal function share one fingerprint (hetero-sem).
    // A record stores its fields in `Sym` (intern) order, so the two field
    // names are interned here, in a fixed order, and the guard makes a future
    // test that interns them the other way fail loudly instead of silently
    // rotating this golden with the test schedule.
    let rb = Sym::new("fp_golden_b");
    let ra = Sym::new("fp_golden_a");
    assert!(rb < ra, "the record field order is intern order; fp_golden_b must be interned first");
    let r = Value::record(vec![(rb, int(1)), (ra, int(2))]);
    let f = fcn(vec![(s("fp_golden_a"), int(2)), (s("fp_golden_b"), int(1))]);
    assert_eq!(r.to_string(), "[fp_golden_b |-> 1, fp_golden_a |-> 2]");
    assert_eq!(fp(&r), 0xc776_ce6c_abe3_a3ba);
    assert_eq!(fp(&f), 0xc776_ce6c_abe3_a3ba);
    // a lazy finite value fingerprints as its normal form
    assert_eq!(fp(&scale(ops::interval(1, 3), 2)), 0xd2e7_ebb3_4c4c_a6ec);
    // a nested composite
    let nested = tup(vec![set(vec![ints(&[1]), ints(&[2])]), rec(&[("fp_a", int(1))])]);
    assert_eq!(fp(&nested), 0xaab0_8d6d_2bf4_2721);
}

/// The incremental `Fingerprinter` feeds whole values in sequence; that word
/// order is a checkpoint's identity too (CODE-21).
#[test]
fn fingerprinter_sequence_matches_fixed_goldens() {
    let mut fp = Fingerprinter::new();
    fp.add(&int(1)).unwrap();
    fp.add(&int(2)).unwrap();
    assert_eq!(fp.finish(), 0x4602_7355_d10f_a01e);
    let mut fp = Fingerprinter::new();
    fp.add(&tup(vec![int(1), int(2)])).unwrap();
    assert_eq!(fp.finish(), 0xaaca_7b92_6894_1319);
}

/// Serialized state bytes and a framed checkpoint are fixed byte goldens
/// (CODE-21, CODE-23): the word stream above is what a checkpoint persists,
/// and the frame checksums are finalized by `tlx_base::hash::fmix64`, so the
/// exact bytes on disk are a stability contract like the fingerprints. The
/// build id is pinned explicitly (a real one hashes the running binary), so
/// the golden is deterministic. A changed stream order or finalizer must fail
/// here; never auto-refresh these bytes.
#[test]
fn serialized_state_and_checkpoint_frame_match_fixed_goldens() {
    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }
    // One value of every tag: bool, int, string, model value, set, interval,
    // tuple, record, function.
    let vals = [
        Value::TRUE,
        Value::FALSE,
        int(-1),
        int(42),
        s("abc"),
        mv("m"),
        set(vec![int(1), int(2)]),
        ops::interval(1, 3),
        tup(vec![int(1), s("a")]),
        Value::record(vec![(Sym::new("fp_a"), int(2))]),
        fcn(vec![(int(1), int(2))]),
    ];
    let mut w = Writer::new();
    for v in &vals {
        w.value(v).unwrap();
    }
    assert_eq!(w.len(), 47);
    assert_eq!(hex(w.as_bytes()), "0100020102540300036162630400016d05020202020406020607020202030001610801000466705f61020407010204");

    // A checkpoint file (header, two chunks, end marker) with a pinned build
    // id, so the whole file, checksums included, is fixed.
    const KIND: u32 = u32::from_le_bytes(*b"CKFP");
    let mut f = FrameWriter::with_build_id(Vec::new(), KIND, "tlx 0 golden").unwrap();
    f.chunk(w.as_bytes()).unwrap();
    f.chunk(b"second").unwrap();
    let file = f.finish().unwrap();
    assert_eq!(file.len(), 141);
    assert_eq!(
        hex(&file),
        "89544c585345520a01000000434b46500c000000746c78203020676f6c64656e432a34ac505739822f000000000000000b469632e262db600100020102540300036162630400016d05020202020406020607020202030001610801000466705f6102040701020406000000000000006374ee8d52bb380b7365636f6e64ffffffffffffffff2ff5d5b32b2f9ec1"
    );
}

/// Deterministic xorshift PRNG.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn random_value(r: &mut Rng, depth: u32) -> Value {
    let k = if depth == 0 { r.below(3) } else { r.below(6) };
    match k {
        0 => int(r.below(20) as i64 - 5),
        1 => Value::Bool(r.below(2) == 0),
        2 => s(["a", "b", "c", "d"][r.below(4) as usize]),
        3 => tup((0..r.below(4)).map(|_| random_value(r, depth - 1)).collect()),
        4 => ints(&(0..r.below(5)).map(|_| r.below(8) as i64).collect::<Vec<_>>()),
        _ => rec(&[("rnd_x", random_value(r, depth - 1)), ("rnd_y", int(r.below(5) as i64))]),
    }
}

#[test]
fn randomized_collision_sanity() {
    let mut r = Rng(0x1234_5678_9abc_def1);
    let mut seen: HashMap<u64, Value> = HashMap::new();
    let mut distinct = 0;
    // Miri runs ~1000x slower; shrink the sample (the fingerprint code is
    // identical) but keep enough values to catch a systematic collision.
    let iters = if cfg!(miri) { 200 } else { 200_000 };
    for _ in 0..iters {
        let v = random_value(&mut r, 3);
        let f = fingerprint(&v).unwrap();
        match seen.get(&f) {
            Some(old) => assert_eq!(old, &v, "fingerprint collision"),
            None => {
                seen.insert(f, v);
                distinct += 1;
            }
        }
    }
    assert!(distinct > iters / 20, "only {distinct} distinct values generated");
    // integer states: no collisions among the sampled pairs
    let pairs = if cfg!(miri) { 10 } else { 1000 };
    let mut fps = std::collections::HashSet::new();
    for i in 0..pairs as i64 {
        for j in 0..pairs as i64 {
            let mut fp = Fingerprinter::new();
            fp.add(&int(i)).unwrap();
            fp.add(&int(j)).unwrap();
            assert!(fps.insert(fp.finish()));
        }
    }
}

#[test]
fn printing() {
    assert_eq!(ints(&[2, 1]).to_string(), "{1, 2}");
    assert_eq!(Value::empty_set().to_string(), "{}");
    assert_eq!(tup(vec![int(1), s("a")]).to_string(), r#"<<1, "a">>"#);
    assert_eq!(tup(vec![]).to_string(), "<<>>");
    Sym::new("pr_a");
    Sym::new("pr_b");
    assert_eq!(rec(&[("pr_b", int(2)), ("pr_a", int(1))]).to_string(), "[pr_a |-> 1, pr_b |-> 2]");
    assert_eq!(fcn(vec![(int(1), int(2)), (int(3), int(4))]).to_string(), "(1 :> 2 @@ 3 :> 4)");
    assert_eq!(ops::interval(1, 3).to_string(), "1..3");
    assert_eq!(ops::interval(3, 1).to_string(), "{}");
    assert_eq!(int(-5).to_string(), "-5");
    assert_eq!(Value::TRUE.to_string(), "TRUE");
    assert_eq!(Value::FALSE.to_string(), "FALSE");
    assert_eq!(mv("pr_m").to_string(), "pr_m");
    assert_eq!(s("a\"b\\c\nd\te").to_string(), r#""a\"b\\c\nd\te""#);
    // lazy sets: expanded when small, symbolic otherwise
    assert_eq!(ops::powerset(&ints(&[1, 2])).unwrap().to_string(), "{{}, {1}, {2}, {1, 2}}");
    assert_eq!(ops::powerset(&ops::interval(1, 10)).unwrap().to_string(), "SUBSET (1..10)");
    let nat = Value::LazySet(Arc::new(LazySet::Nat));
    assert_eq!(ops::powerset(&nat).unwrap().to_string(), "SUBSET Nat");
    assert_eq!(ops::fcn_set(&ints(&[1]), &nat).unwrap().to_string(), "[{1} -> Nat]");
    assert_eq!(ops::product(vec![nat.clone(), ints(&[1])]).unwrap().to_string(), "(Nat \\X {1})");
    assert_eq!(ops::product(vec![ints(&[1]), ints(&[2])]).unwrap().to_string(), "{<<1, 2>>}");
    assert_eq!(ops::seq_set(&ints(&[1])).unwrap().to_string(), "Seq({1})");
    assert_eq!(ops::union(&nat, &ops::powerset(&ints(&[1])).unwrap()).unwrap().to_string(), "Nat \\cup {{}, {1}}");
    assert_eq!(Value::LazySet(Arc::new(LazySet::StringSet)).to_string(), "STRING");
    assert_eq!(Value::LazySet(Arc::new(LazySet::Int)).to_string(), "Int");
    assert_eq!(scale(ops::interval(1, 2), 1).to_string(), "<<1, 2>>");
}

#[test]
fn normalize_is_deep() {
    let p = ops::powerset(&ints(&[1])).unwrap();
    let v = tup(vec![p.clone(), set(vec![p.clone()]), rec(&[("nz_a", scale(ops::interval(1, 1), 5))])]);
    assert!(!v.is_normal());
    let n = v.normalize().unwrap();
    assert!(n.is_normal());
    assert_eq!(n.to_string(), "<<{{}, {1}}, {{{}, {1}}}, [nz_a |-> <<5>>]>>");
    assert_eq!(n, v);
    assert_eq!(fingerprint(&n).unwrap(), fingerprint(&v).unwrap());
    // intervals are kept (canonical compact form)
    assert!(matches!(ops::interval(1, 3).normalize().unwrap(), Value::Interval(1, 3)));
}
