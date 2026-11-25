//! Record formats of encoded blocks (docs/scale.md §5.1).
//!
//! A record is a queued state: its trace-log reference, its fingerprint and
//! its encoding (`StateCodec`, `W` words). Two block kinds:
//!
//! - raw: fixed-size records `log | fp | W words` (8-byte little-endian
//!   words), so that a record can be found by its index;
//! - XOR-varint: `varint(zigzag(log - previous log)) | fp (8 bytes) |
//!   bitmap of the words that differ from the previous record's (⌈W/8⌉
//!   bytes) | varint(word XOR previous word) for each of them`. The first
//!   record of a block is relative to zeros, so a block decodes on its own.

#[cfg(test)]
use tlx_base::bytes::put_uvar as put_varint;
use tlx_base::bytes::{get_uvar_trusted as get_varint, put_uvar_at as put_varint_at, unzigzag, zigzag};

/// Bytes of a raw record of `w` words.
#[inline]
pub(crate) fn raw_size(w: usize) -> usize {
    16 + 8 * w
}

/// The largest XOR-varint record of `w` words.
pub(crate) fn xor_max_size(w: usize) -> usize {
    10 + 8 + w.div_ceil(8) + 10 * w
}

/// Append a raw record.
#[inline]
pub(crate) fn put_raw(out: &mut Vec<u8>, log: u64, fp: u64, words: &[u64]) {
    out.reserve(raw_size(words.len()));
    out.extend_from_slice(&log.to_le_bytes());
    out.extend_from_slice(&fp.to_le_bytes());
    if cfg!(target_endian = "little") {
        // SAFETY: any initialized `u64`s are valid bytes.
        out.extend_from_slice(unsafe { std::slice::from_raw_parts(words.as_ptr().cast::<u8>(), 8 * words.len()) });
    } else {
        for w in words {
            out.extend_from_slice(&w.to_le_bytes());
        }
    }
}

#[inline]
fn u64_at(b: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(b[at..at + 8].try_into().unwrap())
}

/// Read the raw record `rec` (its bytes): `(log, fp)`, the words in `words`.
#[inline]
pub(crate) fn get_raw(rec: &[u8], words: &mut [u64]) -> (u64, u64) {
    let body = &rec[16..16 + 8 * words.len()];
    if cfg!(target_endian = "little") {
        // SAFETY: `body` has exactly the bytes of `words`, any bytes are a
        // valid `u64`, and the two do not overlap.
        unsafe { std::ptr::copy_nonoverlapping(body.as_ptr(), words.as_mut_ptr().cast::<u8>(), body.len()) };
    } else {
        for (i, w) in words.iter_mut().enumerate() {
            *w = u64_at(body, 8 * i);
        }
    }
    (u64_at(rec, 0), u64_at(rec, 8))
}

/// The previous record of an XOR-varint block (zeros before the first).
#[derive(Clone)]
pub(crate) struct XorPrev {
    pub(crate) log: u64,
    pub(crate) words: Vec<u64>,
}

impl XorPrev {
    pub(crate) fn new(w: usize) -> XorPrev {
        XorPrev { log: 0, words: vec![0; w] }
    }

    /// Start a block.
    pub(crate) fn reset(&mut self) {
        self.log = 0;
        self.words.fill(0);
    }
}

/// Append an XOR-varint record relative to `prev`, which becomes this record.
pub(crate) fn put_xor(out: &mut Vec<u8>, prev: &mut XorPrev, log: u64, fp: u64, words: &[u64]) {
    debug_assert_eq!(words.len(), prev.words.len());
    // (Written into the reserved spare capacity: no capacity check per byte.)
    let n = words.len();
    out.reserve(xor_max_size(n));
    let len = out.len();
    let buf = &mut out.spare_capacity_mut()[..xor_max_size(n)];
    let mut at = put_varint_at(buf, 0, zigzag(log.wrapping_sub(prev.log) as i64));
    prev.log = log;
    for (k, b) in fp.to_le_bytes().into_iter().enumerate() {
        buf[at + k].write(b);
    }
    at += 8;
    let bitmap = at;
    at += n.div_ceil(8);
    for (g, (ws, ps)) in words.chunks(8).zip(prev.words.chunks_mut(8)).enumerate() {
        // The changed words of the group (without a branch per word: most
        // are unchanged), then their XOR values.
        let mut bits = 0u8;
        for (i, (w, p)) in ws.iter().zip(ps.iter()).enumerate() {
            bits |= ((w != p) as u8) << i;
        }
        buf[bitmap + g].write(bits);
        while bits != 0 {
            let i = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            at = put_varint_at(buf, at, ws[i] ^ ps[i]);
            ps[i] = ws[i];
        }
    }
    // SAFETY: the first `at` bytes of the spare capacity were written.
    unsafe { out.set_len(len + at) };
}

/// Read the XOR-varint record at `*pos` of `b` relative to `prev` (which
/// becomes it); returns its fingerprint (the log is `prev.log`, the words
/// `prev.words`).
pub(crate) fn get_xor(b: &[u8], pos: &mut usize, prev: &mut XorPrev) -> u64 {
    prev.log = prev.log.wrapping_add(unzigzag(get_varint(b, pos)) as u64);
    let fp = u64_at(b, *pos);
    *pos += 8;
    let w = prev.words.len();
    let bitmap = *pos;
    *pos += w.div_ceil(8);
    for byte in 0..w.div_ceil(8) {
        let mut bits = b[bitmap + byte];
        while bits != 0 {
            let i = byte * 8 + bits.trailing_zeros() as usize;
            bits &= bits - 1;
            prev.words[i] ^= get_varint(b, pos);
        }
    }
    fp
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic pseudo-random generator (xorshift).
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }

    /// Records like a frontier's: siblings differing in a few small words,
    /// sometimes in extreme ones.
    fn records(rng: &mut Rng, w: usize, n: usize) -> Vec<(u64, u64, Vec<u64>)> {
        let mut cur = vec![0u64; w];
        let mut log = (rng.next() % 4) << 48;
        (0..n)
            .map(|_| {
                for _ in 0..rng.next() % 4 {
                    if w > 0 {
                        let i = (rng.next() % w as u64) as usize;
                        cur[i] = match rng.next() % 4 {
                            0 => u64::MAX,
                            1 => rng.next(),
                            _ => rng.next() % 16,
                        };
                    }
                }
                // Mostly increasing logs, sometimes not.
                log = if rng.next().is_multiple_of(8) { rng.next() } else { log.wrapping_add(rng.next() % 5) };
                (log, rng.next(), cur.clone())
            })
            .collect()
    }

    #[test]
    fn varint_round_trip() {
        let mut rng = Rng(7);
        let mut vals = vec![0, 1, 127, 128, 255, 16383, 16384, u64::MAX, u64::MAX - 1, 1 << 63];
        vals.extend((0..1000).map(|_| rng.next() >> (rng.next() % 64)));
        let mut b = Vec::new();
        for &v in &vals {
            put_varint(&mut b, v);
        }
        let mut pos = 0;
        for &v in &vals {
            assert_eq!(get_varint(&b, &mut pos), v);
        }
        assert_eq!(pos, b.len());
        for d in [0i64, 1, -1, i64::MAX, i64::MIN, 12345, -12345] {
            assert_eq!(unzigzag(zigzag(d)), d);
        }
    }

    #[test]
    fn xor_round_trip() {
        let mut rng = Rng(0x1234_5678);
        for w in [0, 1, 7, 8, 9, 17, 64, 287] {
            let recs = records(&mut rng, w, 300);
            let mut b = Vec::new();
            let mut prev = XorPrev::new(w);
            for (log, fp, words) in &recs {
                let before = b.len();
                put_xor(&mut b, &mut prev, *log, *fp, words);
                assert!(b.len() - before <= xor_max_size(w));
            }
            let mut prev = XorPrev::new(w);
            let mut pos = 0;
            for (log, fp, words) in &recs {
                assert_eq!(get_xor(&b, &mut pos, &mut prev), *fp);
                assert_eq!(prev.log, *log);
                assert_eq!(&prev.words, words);
            }
            assert_eq!(pos, b.len());
        }
    }

    #[test]
    fn raw_round_trip() {
        let mut rng = Rng(99);
        let recs = records(&mut rng, 13, 50);
        let mut b = Vec::new();
        for (log, fp, words) in &recs {
            put_raw(&mut b, *log, *fp, words);
        }
        assert_eq!(b.len(), recs.len() * raw_size(13));
        let mut words = vec![0; 13];
        for (k, (log, fp, want)) in recs.iter().enumerate().rev() {
            let at = k * raw_size(13);
            assert_eq!(get_raw(&b[at..at + raw_size(13)], &mut words), (*log, *fp));
            assert_eq!(&words, want);
        }
    }

    #[test]
    fn xor_worst_case_size() {
        let w = 9;
        let mut b = Vec::new();
        let mut prev = XorPrev::new(w);
        put_xor(&mut b, &mut prev, 1 << 63, u64::MAX, &[u64::MAX; 9]);
        // (A log delta whose zigzag needs all 64 bits.)
        put_xor(&mut b, &mut prev, 0, 0, &[0; 9]);
        let first = b.len();
        assert!(first <= 2 * xor_max_size(w));
        let mut prev = XorPrev::new(w);
        let mut pos = 0;
        assert_eq!(get_xor(&b, &mut pos, &mut prev), u64::MAX);
        assert_eq!((prev.log, prev.words.clone()), (1 << 63, vec![u64::MAX; 9]));
        assert_eq!(get_xor(&b, &mut pos, &mut prev), 0);
        assert_eq!((prev.log, prev.words.clone()), (0, vec![0; 9]));
    }
}
