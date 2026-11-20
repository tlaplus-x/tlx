use super::*;
use crate::explore::safepoint::Safepoint;
use std::collections::HashSet;
use std::sync::atomic::AtomicBool;

fn fp(i: u64) -> u64 {
    i.wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

#[test]
fn insert_contains_full() {
    // Miri is ~1000x slower and probe chains grow with the load factor,
    // so keep both the table and the fill small.
    let n: u64 = if cfg!(miri) { 500 } else { 200_000 };
    let s = FpSet::new(if cfg!(miri) { 1_000 } else { 300_000 });
    for i in 1..=n {
        assert!(s.try_insert(fp(i)).unwrap());
        assert!(!s.try_insert(fp(i)).unwrap());
    }
    assert_eq!(s.len(), n as usize);
    assert!(s.contains(fp(1)));
    assert!(!s.contains(12345));
    let small = FpSet::new(0);
    let mut n = 0u64;
    while small.try_insert(n.wrapping_mul(0xD6E8_FEB8_6659_FD93) | 2).is_ok() {
        n += 1;
    }
    assert_eq!(small.len(), small.max_entries());
}

#[test]
#[should_panic(expected = "fingerprint set too large")]
fn huge_reservation_is_refused() {
    // Must not wrap around to a tiny table.
    FpSet::new(usize::MAX / 2);
}

#[test]
fn fingerprint_zero_is_stored() {
    let s = FpSet::new(0);
    assert!(!s.contains(0));
    assert!(s.try_insert(0).unwrap());
    assert!(!s.try_insert(0).unwrap());
    assert!(s.contains(0));
    // 0 and 1 share a slot value (0 is remapped), as documented.
    assert!(s.contains(1));
}

/// The smallest table (`FpSet::new(0)`) fills up and refuses inserts
/// without panicking.
#[test]
fn a_tiny_set_fills_without_panicking() {
    let s = FpSet::new(0);
    assert_eq!(s.slots(), 1024);
    assert_eq!(s.max_entries(), 922);
    assert!(!s.growable());
    for i in 1..=s.max_entries() as u64 {
        assert!(s.try_insert(fp(i)).unwrap());
    }
    assert_eq!(s.try_insert(12345), Err(Full));
    assert_eq!(s.len(), s.max_entries());
}

/// Placement by the high bits: the table is sorted up to the order
/// within probe clusters, and the largest fingerprints probe into the
/// overflow area instead of wrapping around.
#[test]
fn high_bits_placement_and_the_overflow_area() {
    let s = FpSet::with_config(FpConfig::fixed(MIN_SLOTS));
    let t = s.table();
    assert_eq!(t.slots.len(), MIN_SLOTS + OVERFLOW);
    assert_eq!(t.home(0), 0);
    assert_eq!(t.home(u64::MAX), MIN_SLOTS - 1);
    assert_eq!(t.home(1 << 63), MIN_SLOTS / 2);
    // Fingerprints all at the very top: they fill the last home slot and
    // continue into the overflow area. (Miri is ~1000x slower and every
    // insert probes the whole run below the last home slot, so the run
    // is quadratic: keep it short there.)
    let m: u64 = if cfg!(miri) { 40 } else { 900 };
    for i in 0..m {
        assert!(s.try_insert(u64::MAX - i).unwrap());
    }
    assert!(t.slots[MIN_SLOTS..MIN_SLOTS + (m as usize - 1)].iter().all(|x| x.load(Ordering::Relaxed) != 0));
    assert!(t.slots[..MIN_SLOTS - 1].iter().all(|x| x.load(Ordering::Relaxed) == 0));
    for i in 0..m {
        assert!(s.contains(u64::MAX - i));
        assert!(!s.try_insert(u64::MAX - i).unwrap());
    }
    // Random fingerprints: the occupied slots are sorted outside clusters.
    // (Miri is ~1000x slower; a smaller fill still exercises the placement.)
    let n: u64 = if cfg!(miri) { 300 } else { 20_000 };
    let s = FpSet::with_config(FpConfig::fixed(if cfg!(miri) { 1 << 12 } else { 1 << 16 }));
    for i in 1..=n {
        s.try_insert(fp(i)).unwrap();
    }
    let vals: Vec<u64> = s.table().slots.iter().map(|x| x.load(Ordering::Relaxed)).filter(|&x| x != 0).collect();
    let inversions = vals.windows(2).filter(|w| w[0] > w[1]).count();
    assert!(inversions < vals.len() / 10, "{inversions} inversions in {}", vals.len());
}

/// The watermarks: `high` is called once, by the insert that reaches
/// 0.75 (only if the table can grow); inserts fail at 0.9.
// Filling to the 90% watermark needs thousands of inserts whose probe
// chains are very long at that load, and under Miri that takes tens of
// minutes even for the smallest legal table (`MIN_SLOTS`). `watermarks`
// has no unsafe code beyond the table's; `grow_serially_up_to_the_limit`
// and `grow_with_helper_threads` cover the growth path cheaply instead.
#[cfg_attr(miri, ignore)]
#[test]
fn watermarks() {
    for (config, growable) in [(FpConfig::fixed(10_000), false), (FpConfig::growing(20_000).with_initial(10_000), true)] {
        let s = FpSet::with_config(config);
        assert_eq!((s.high(), s.max_entries()), (7500, 9000));
        let mut calls = Vec::new();
        let mut i = 0u64;
        loop {
            i += 1;
            match s.insert(fp(i), &mut 0, || calls.push(s.len())) {
                Ok(true) => {}
                Ok(false) => unreachable!(),
                Err(Full) => break,
            }
        }
        assert_eq!(s.len(), 9000);
        assert_eq!(calls, if growable { vec![7500] } else { vec![] });
        assert_eq!(s.growable(), growable);
    }
}

/// Growing keeps every fingerprint, doubles the table up to the limit
/// (the last step may be smaller), and fails at the limit.
#[test]
fn grow_serially_up_to_the_limit() {
    if cfg!(miri) {
        // Inserting up to the 90% watermark takes tens of minutes under
        // Miri (long probe chains at that load, `MIN_SLOTS` tables are
        // unavoidable). Grow explicitly instead: the same rehash-and-swap
        // path, at low load.
        let s = FpSet::with_config(FpConfig::growing(2048).with_initial(1024));
        for i in 1..=200u64 {
            // SAFETY: single-threaded.
            assert_eq!(unsafe { s.insert_exclusive(fp(i)) }, Ok(true));
        }
        // SAFETY: single-threaded.
        assert!(unsafe { s.grow(None) });
        assert_eq!((s.slots(), s.len(), s.grows().0), (2048, 200, 1));
        for i in 1..=200u64 {
            assert!(s.contains(fp(i)), "{i}");
        }
        assert!(!s.contains(fp(201)));
        return;
    }
    let s = FpSet::with_config(FpConfig::growing(5000).with_initial(1024));
    let mut i = 0u64;
    let full = loop {
        i += 1;
        // SAFETY: single-threaded.
        match unsafe { s.insert_exclusive(fp(i)) } {
            Ok(new) => assert!(new),
            Err(Full) => break i,
        }
    };
    assert_eq!(s.slots(), 5000);
    assert_eq!(s.grows().0, 3);
    assert_eq!(s.len(), 4500);
    assert_eq!(full, 4501);
    for j in 1..full {
        assert!(s.contains(fp(j)), "{j}");
    }
    assert!(!s.contains(fp(full)));
    // 1024 -> 2048 -> 4096 -> 5000 slots: the largest pair is the last.
    assert_eq!(s.peak_bytes(), (4096 + 5000 + 2 * OVERFLOW) * 8);
    assert_eq!(s.gauge().bytes(), s.bytes());
}

/// Growing with threads of its own (no crew, or a crew smaller than
/// asked for): every fingerprint is in the new table.
#[test]
fn grow_with_helper_threads() {
    // Miri is ~1000x slower; fewer entries and a smaller grow to the same
    // target, but the helper threads (parts > 1) still run.
    let (n, initial, limit, target): (u64, usize, usize, usize) =
        if cfg!(miri) { (300, 1024, 4096, 2048) } else { (40_000, 1 << 16, 1 << 20, 1 << 19) };
    let s = FpSet::with_config(FpConfig::growing(limit).with_initial(initial));
    for i in 1..n {
        // SAFETY: single-threaded.
        assert_eq!(unsafe { s.insert_exclusive(fp(i)) }, Ok(true));
    }
    // SAFETY: single-threaded (the helpers only run inside).
    let threads = if cfg!(miri) { 3 } else { 5 };
    assert!(unsafe { s.grow_to(None, threads, target) });
    assert_eq!((s.slots(), s.len()), (target, (n - 1) as usize));
    for i in 1..n {
        assert!(s.contains(fp(i)), "{i}");
    }
    assert!(!s.contains(fp(n)));
}

#[test]
fn concurrent_inserts() {
    // Miri interleaves the threads faithfully but runs ~100x slower
    // (and its scheduler makes contended CAS loops much worse).
    let n: u64 = if cfg!(miri) { 1_000 } else { 100_000 };
    let s = FpSet::new(if cfg!(miri) { 2_000 } else { 200_000 });
    let new = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..8 {
            sc.spawn(|| {
                for i in 0..n {
                    if s.try_insert(i.wrapping_mul(0xD6E8_FEB8_6659_FD93) | 2).unwrap() {
                        new.fetch_add(1, Ordering::Relaxed);
                    }
                }
            });
        }
    });
    assert_eq!(new.load(Ordering::Relaxed), n as usize);
    assert_eq!(s.len(), n as usize);
}

/// Microbenchmark (`cargo test --profile test-release -p tlx-runtime
/// --lib -- --ignored --nocapture insert_throughput`): ns per new
/// insert and thread, with 1 and 8 threads, into tables too large to
/// reach their watermarks: a large table (cache misses dominate) and
/// rounds of small ones (the counting dominates).
#[test]
#[ignore]
fn insert_throughput() {
    for (per, rounds) in [(1u64 << 20, 1), (1 << 14, 64)] {
        for threads in [1u64, 8] {
            let mut ns = 0;
            for _ in 0..rounds {
                let s = FpSet::new((per * threads) as usize * 2);
                // (Fault the pages in first: their first writes would dominate.)
                for x in s.table().slots.iter() {
                    x.store(0, Ordering::Relaxed);
                }
                let t0 = Instant::now();
                std::thread::scope(|sc| {
                    for me in 0..threads {
                        let s = &s;
                        sc.spawn(move || {
                            for i in 0..per {
                                let _ = s.insert_by(me as usize, fp(1 + i * threads + me), &mut 0, || {});
                            }
                        });
                    }
                });
                ns += t0.elapsed().as_nanos();
                assert_eq!(s.len(), (per * threads) as usize);
            }
            let ns = ns as f64 / (per * rounds) as f64;
            println!("insert_throughput: {per} x {rounds}, {threads} threads: {ns:.2} ns per insert and thread");
        }
    }
}

/// Eight threads insert overlapping streams while the table grows from
/// the smallest size at safepoints (the explorer's protocol: request at
/// the high watermark, park between inserts, and at the hard limit
/// request, park, retry): every fingerprint is inserted exactly once,
/// and the set ends up equal to the inserted set.
#[test]
fn concurrent_inserts_while_growing() {
    const REQ: u32 = 1 << 2;
    let n = 8;
    let s = FpSet::with_config(FpConfig::growing(1 << 22).with_initial(MIN_SLOTS));
    let sp = Safepoint::new(n);
    let new = AtomicUsize::new(0);
    let grows = AtomicUsize::new(0);
    let serve = |req: u32, crew: &Crew<'_>| {
        assert_eq!(req, REQ);
        // SAFETY: every inserting thread is parked or has left.
        if unsafe { s.grow(Some(crew)) } {
            grows.fetch_add(1, Ordering::Relaxed);
        }
    };
    let fps = |me: u64| (0..60_000u64).map(move |i| fp(1 + (i * 7 + me * 20_000) % 300_000));
    let stuck = AtomicBool::new(false);
    std::thread::scope(|sc| {
        for me in 0..n as u64 {
            let (s, sp, new, serve, stuck) = (&s, &sp, &new, &serve, &stuck);
            sc.spawn(move || {
                for f in fps(me) {
                    if sp.control().get() != 0 {
                        sp.park(serve);
                    }
                    let r = loop {
                        match s.insert(f, &mut 0, || sp.control().request(REQ)) {
                            Ok(b) => break b,
                            Err(Full) => {
                                if !s.growable() {
                                    stuck.store(true, Ordering::Relaxed);
                                    break false;
                                }
                                sp.control().request(REQ);
                                sp.park(serve);
                            }
                        }
                    };
                    if r {
                        new.fetch_add(1, Ordering::Relaxed);
                    }
                }
                sp.leave(serve);
            });
        }
    });
    assert!(!stuck.load(Ordering::Relaxed));
    let all: HashSet<u64> = (0..n as u64).flat_map(fps).collect();
    assert_eq!(new.load(Ordering::Relaxed), all.len());
    assert_eq!(s.len(), all.len());
    assert!(all.iter().all(|&f| s.contains(f)));
    let stored: HashSet<u64> = s.table().slots.iter().map(|x| x.load(Ordering::Relaxed)).filter(|&x| x != 0).collect();
    assert_eq!(stored, all);
    assert!(grows.load(Ordering::Relaxed) >= 8, "{} grows", grows.load(Ordering::Relaxed));
    assert_eq!(s.grows().0 as usize, grows.load(Ordering::Relaxed));
    assert!(s.len() < s.high(), "{} entries, high watermark {}", s.len(), s.high());
}

/// Keep the parent owned while tlx creates and removes the spill directory.
fn spill(name: &str, fail_after: Option<u64>) -> (tlx_testkit::TempDir, Spill) {
    let scratch = tlx_testkit::TempDir::new(name);
    let dir = scratch.child_path("spill");
    let sp = Spill::new(crate::io::SpillConfig { dir: Some(dir), fail_after, ..Default::default() });
    (scratch, sp)
}

/// A stream of fingerprints with many repetitions, some far apart
/// (the 0 is remapped to 1, which also occurs).
fn stream(n: u64) -> impl Iterator<Item = u64> {
    (0..n).map(|i| {
        let k = match i % 5 {
            0 | 1 => i,
            2 => i / 2,
            3 => i.saturating_sub(5000),
            _ => (i * 7919) % (i + 1),
        };
        if k == 3 {
            0
        } else {
            fp(k + 1)
        }
    })
}

/// A set of the smallest tables rotates to disk again and again: it
/// answers every insert as a `HashSet` does (across the old table, the
/// runs, merges in progress and installed), and holds everything.
#[test]
fn rotating_to_disk_matches_a_hash_set() {
    let (_scratch, sp) = spill("reference", None);
    let s = FpSet::with_config(FpConfig::growing(2048).with_initial(1024)).with_disk(sp.clone());
    let mut reference = HashSet::new();
    for (i, f) in stream(60_000).enumerate() {
        // SAFETY: single-threaded.
        let new = unsafe { s.insert_exclusive(f) }.unwrap();
        assert_eq!(new, reference.insert(norm(f)), "insert {i} of {f:#x}");
        if i % 9973 == 0 {
            // SAFETY: single-threaded.
            unsafe { s.install_merge(true) };
        }
    }
    assert_eq!(s.len(), reference.len());
    let d = s.disk_stats().expect("the disk tier");
    assert!(d.rotations > 20 && d.merges > 2, "{d:?}");
    assert!(d.reads > 0 && d.hits > 0, "{d:?}");
    assert!(s.slots() <= 2048);
    // SAFETY: single-threaded.
    unsafe { s.install_merge(true) };
    // (The gauge counts what the set holds: tables, runs, no merge.)
    assert_eq!(s.gauge().bytes(), s.bytes());
    assert!(reference.iter().all(|&f| s.contains(f)));
    assert!(!s.contains(fp(1 << 40)));
    // Everything is on disk or in the table; runs are disjoint.
    let d = s.disk_stats().unwrap();
    assert_eq!(d.on_disk as usize + s.table_len(), s.len());
    assert!(sp.counters().used > 0 && sp.dir().is_some());
    drop(s);
    assert_eq!(sp.counters().used, 0);
    assert!(sp.dir().is_none(), "the spill directory is removed with the set");
}

/// Checkpoints: the table and the runs read out in ascending
/// order hold every fingerprint once; a set rebuilt from them (into a
/// table reserved beforehand, or as runs again) answers as the
/// original, and a large ascending load into a reserved table stays
/// fast (no pile-up in the part of a small table their high bits
/// select).
#[test]
fn sections_rebuild_the_set() {
    let (_scratch, sp) = spill("sections", None);
    let s = FpSet::with_config(FpConfig::growing(2048).with_initial(1024)).with_disk(sp);
    let mut reference = HashSet::new();
    for f in stream(30_000) {
        // SAFETY: single-threaded.
        unsafe { s.insert_exclusive(f) }.unwrap();
        reference.insert(norm(f));
    }
    let mut sections: Vec<Vec<u64>> = (0..s.run_count())
        .map(|k| {
            let mut v = Vec::new();
            s.for_each_in_run(k, |f| {
                let _: () = v.push(f);
                Ok(())
            })
            .unwrap();
            v
        })
        .collect();
    let mut table = Vec::new();
    // SAFETY: single-threaded.
    unsafe {
        s.for_each_in_table_part(0, 1, |f| {
            let _: () = table.push(f);
            Ok(())
        })
    }
    .unwrap();
    // The parts of the table, in order, are the table (one part, or taken
    // by several threads at once).
    for parts in [1, 2, 3, 7, 64] {
        let got: Vec<parking_lot::Mutex<Vec<u64>>> = (0..parts).map(|_| parking_lot::Mutex::new(Vec::new())).collect();
        std::thread::scope(|sc| {
            for t in 0..3 {
                let (s, got) = (&s, &got);
                sc.spawn(move || {
                    for part in (t..parts).step_by(3) {
                        let mut v = got[part].lock();
                        // SAFETY: no inserts; each part is taken once.
                        unsafe {
                            s.for_each_in_table_part(part, parts, |f| {
                                let _: () = v.push(f);
                                Ok(())
                            })
                        }
                        .unwrap();
                    }
                });
            }
        });
        let joined: Vec<u64> = got.into_iter().flat_map(|m| m.into_inner()).collect();
        assert_eq!(joined, table, "{parts} parts");
    }
    sections.push(table);
    assert!(sections.len() > 3, "{} sections", sections.len());
    for v in &sections {
        assert!(v.windows(2).all(|w| w[0] < w[1]), "ascending");
    }
    let all: Vec<u64> = sections.iter().flatten().copied().collect();
    assert_eq!(all.len(), reference.len());
    assert_eq!(all.iter().copied().collect::<HashSet<_>>(), reference);
    // Into a table (reserved for all of them), or as runs.
    for runs in [false, true] {
        let (_scratch, sp) = spill("rebuilt", None);
        let r = FpSet::with_config(FpConfig::growing(if runs { 2048 } else { 1 << 20 }).with_initial(1024)).with_disk(sp);
        // SAFETY: single-threaded.
        assert_eq!(unsafe { r.reserve(all.len(), usize::MAX) }, !runs);
        for v in &sections {
            if runs && r.takes_runs() {
                let mut chunks = v.chunks(1000).map(|c| c.to_vec());
                // SAFETY: single-threaded.
                unsafe { r.add_run(v.len(), &mut || Ok(chunks.next())) }.unwrap();
            } else {
                for &f in v {
                    // SAFETY: single-threaded.
                    assert!(unsafe { r.insert_exclusive(f) }.unwrap());
                }
            }
        }
        assert_eq!(r.len(), reference.len(), "runs {runs}");
        let mut reference = reference.clone();
        for f in stream(32_000) {
            // SAFETY: single-threaded.
            assert_eq!(unsafe { r.insert_exclusive(f) }.unwrap(), reference.insert(norm(f)), "runs {runs}");
        }
        assert_eq!(r.disk_stats().is_some(), runs);
        // SAFETY: single-threaded.
        unsafe { r.install_merge(true) };
        assert_eq!(r.gauge().bytes(), r.bytes(), "runs {runs}");
    }
    // Ascending fingerprints over the whole range, into a reserved
    // table: about one probe each.
    let big = FpSet::with_config(FpConfig::growing(1 << 22));
    let n = 2_000_000u64;
    // SAFETY: single-threaded.
    assert!(unsafe { big.reserve(n as usize, usize::MAX) });
    let mut probes = 0;
    for i in 0..n {
        let f = (i + 1) * (u64::MAX / (n + 1));
        assert!(big.insert(f, &mut probes, || panic!("no growth")).unwrap());
    }
    assert!(probes < 3 * n, "{probes} probes");
}

/// Rotating without keeping the old table (memory pressure), and
/// dropping it later: the answers do not change.
#[test]
fn rotating_without_the_old_table() {
    let (_scratch, sp) = spill("noold", None);
    let s = FpSet::with_config(FpConfig::growing(1024)).with_disk(sp);
    let mut reference = HashSet::new();
    for (i, f) in stream(20_000).enumerate() {
        let r = match s.insert(f, &mut 0, || {}) {
            Ok(b) => b,
            Err(Full) => {
                // SAFETY: single-threaded.
                unsafe { s.rotate(None, 3, 1024 + i % 2000, i % 2 == 0) }.unwrap();
                assert_eq!(s.old_bytes() > 0, i % 2 == 0);
                if i % 3 == 0 {
                    // SAFETY: single-threaded.
                    unsafe { s.drop_old() };
                    assert_eq!(s.old_bytes(), 0);
                }
                s.try_insert(f).unwrap()
            }
        };
        assert_eq!(r, reference.insert(norm(f)), "insert {i}");
    }
    assert_eq!(s.len(), reference.len());
    assert!(reference.iter().all(|&f| s.contains(f)));
    // SAFETY: single-threaded.
    unsafe { s.install_merge(true) };
    assert_eq!(s.gauge().bytes(), s.bytes());
}

/// A large table written by many threads (many ranges of slots, whose
/// boundaries cut clusters or fall just before them): the run holds
/// every fingerprint, once.
#[test]
fn a_large_table_written_in_ranges() {
    let (_scratch, sp) = spill("ranges", None);
    let s = FpSet::with_config(FpConfig::growing(1 << 20).with_initial(1 << 20)).with_disk(sp);
    let n = s.high() as u64 - 1;
    for i in 1..=n {
        assert!(s.try_insert(fp(i)).unwrap());
    }
    // SAFETY: single-threaded (the helpers only run inside).
    unsafe { s.rotate(None, 61, MIN_SLOTS, false) }.unwrap();
    let d = s.disk_stats().unwrap();
    assert_eq!((d.on_disk, s.table_len()), (n, 0));
    for i in 1..=n {
        assert!(s.contains(fp(i)), "{i}");
        assert_eq!(s.try_insert(fp(i)), Ok(false), "{i}");
    }
    assert!(!s.contains(fp(n + 1)));
}

/// Lookups read the runs through a mapping and verify a page's
/// checksum when they first read it: a page damaged on disk before that
/// fails the lookup with an IO error; the other pages still answer.
#[test]
fn a_corrupt_page_of_a_run_is_detected() {
    use std::os::unix::fs::FileExt;
    let (_scratch, sp) = spill("corrupt", None);
    let s = FpSet::with_config(FpConfig::growing(1024)).with_disk(sp.clone());
    let n = s.high() as u64 - 1;
    for i in 1..=n {
        assert!(s.try_insert(fp(i)).unwrap());
    }
    // SAFETY: single-threaded.
    unsafe { s.rotate(None, 0, 1024, false) }.unwrap();
    let mut sorted: Vec<u64> = (1..=n).map(|i| norm(fp(i))).collect();
    sorted.sort_unstable();
    // The largest fingerprint (in the last page) answers; then the first
    // page of the file is damaged before any lookup read it.
    assert_eq!(s.try_insert(sorted[sorted.len() - 1]), Ok(false));
    let dir = sp.dir().expect("the spill directory");
    let file = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .find(|p| p.file_name().unwrap().to_string_lossy().starts_with("fpset"))
        .expect("the run file");
    let f = std::fs::OpenOptions::new().read(true).write(true).open(&file).unwrap();
    let mut b = [0u8; 1];
    f.read_exact_at(&mut b, 8).unwrap();
    f.write_all_at(&[b[0] ^ 0x10], 8).unwrap();
    assert_eq!(s.try_insert(sorted[0]), Err(Full));
    let e = s.io_error().expect("the IO error");
    assert!(e.0.contains("checksum mismatch"), "{e}");
}

/// An IO error while rotating (a write fails) changes nothing: the set
/// stays full, cannot rotate any more, and reports the error.
#[test]
fn a_failed_rotation_leaves_the_set_full() {
    let (_scratch, sp) = spill("fail", Some(10_000));
    let s = FpSet::with_config(FpConfig::growing(1024)).with_disk(sp);
    let mut n = 0u64;
    let err = loop {
        n += 1;
        // SAFETY: single-threaded.
        if unsafe { s.insert_exclusive(fp(n)) }.is_err() {
            break n;
        }
    };
    assert!(err > 922, "{err}");
    assert!(!s.rotatable() && !s.can_make_room());
    let e = s.io_error().expect("the IO error");
    assert!(e.0.contains("injected write error"), "{e}");
    for i in 1..err {
        assert!(s.contains(fp(i)), "{i}");
    }
}

/// Eight threads insert overlapping streams into a set of small tables
/// that rotate to disk at safepoints (with merges installed there):
/// every fingerprint is inserted exactly once.
#[test]
fn concurrent_inserts_while_rotating() {
    const REQ: u32 = 1 << 2;
    let n = 8;
    let (_scratch, sp) = spill("concurrent", None);
    let s = FpSet::with_config(FpConfig::growing(1 << 12).with_initial(MIN_SLOTS)).with_disk(sp);
    let sp = Safepoint::new(n);
    let new = AtomicUsize::new(0);
    let serve = |req: u32, crew: &Crew<'_>| {
        assert_eq!(req, REQ);
        // SAFETY: every inserting thread is parked or has left.
        unsafe {
            s.install_merge(false);
            if s.at_high() {
                if s.spilling() || !s.growable() {
                    s.rotate(Some(crew), 0, s.slots(), true).unwrap();
                } else {
                    s.grow(Some(crew));
                }
            }
        }
    };
    let fps = |me: u64| (0..30_000u64).map(move |i| fp(1 + (i * 7 + me * 20_000) % 150_000));
    std::thread::scope(|sc| {
        for me in 0..n as u64 {
            let (s, sp, new, serve) = (&s, &sp, &new, &serve);
            sc.spawn(move || {
                for f in fps(me) {
                    if sp.control().get() != 0 {
                        sp.park(serve);
                    }
                    let r = loop {
                        match s.insert(f, &mut 0, || sp.control().request(REQ)) {
                            Ok(b) => break b,
                            Err(Full) => {
                                assert!(s.can_make_room());
                                sp.control().request(REQ);
                                sp.park(serve);
                            }
                        }
                    };
                    if r {
                        new.fetch_add(1, Ordering::Relaxed);
                    }
                }
                sp.leave(serve);
            });
        }
    });
    let all: HashSet<u64> = (0..n as u64).flat_map(fps).collect();
    assert_eq!(new.load(Ordering::Relaxed), all.len());
    assert_eq!(s.len(), all.len());
    assert!(all.iter().all(|&f| s.contains(f)));
    let d = s.disk_stats().unwrap();
    assert!(d.rotations >= 10, "{d:?}");
    assert_eq!(d.on_disk as usize + s.table_len(), s.len());
}

/// The cache-line padding the set relies on comes from the shared
/// `tlx_base::padded::Padded` now (CODE-23): the atomic payload is
/// unchanged (8 bytes), a padded counter is one 128-byte line, and the
/// table field puts the whole set on a 128-byte boundary.
#[test]
fn padded_layout_is_preserved() {
    assert_eq!((std::mem::size_of::<AtomicUsize>(), std::mem::align_of::<AtomicUsize>()), (8, 8));
    assert_eq!(std::mem::size_of::<Padded<AtomicUsize>>(), 128);
    assert_eq!(std::mem::align_of::<Padded<AtomicUsize>>(), 128);
    let s = FpSet::new(0);
    assert_eq!(std::mem::align_of_val(&s.table), 128);
    assert_eq!(std::mem::align_of_val(&s), 128);
}
