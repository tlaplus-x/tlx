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
    assert_eq!(t.slot_len(), MIN_SLOTS + OVERFLOW);
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
    assert!((MIN_SLOTS..MIN_SLOTS + (m as usize - 1)).all(|i| t.is_occupied(i)));
    assert!((0..MIN_SLOTS - 1).all(|i| !t.is_occupied(i)));
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
    let vals = s.table().entries_vec();
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
                s.table().fault_pages();
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
    let stored: HashSet<u64> = s.table().entries_vec().into_iter().collect();
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

fn test_seed() -> u64 {
    std::env::var("TLX_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(0x517C_C1B7_2722_0A95)
}

/// Lossless low-bit `fastrange` quotienting bijection across boundary `fp`
/// values, bucket boundaries, power-of-two and non-power-of-two slot counts
/// (including `2^32 - 1`, `2^32 + 1`, and `> 2^32` slots), and seeded random
/// property inputs.
#[test]
fn quotient_bijection_boundaries_and_property() {
    use super::table::Quotient;
    let seed = test_seed();
    let mut rng = tlx_testkit::XorShift64Star::new(seed);
    let fixed_ns: &[usize] = &[
        MIN_SLOTS,
        10_000,
        (1 << 20) - 1,
        1 << 20,
        1 << 21,
        2_345_679,
        (1 << 26) + 99,
        1 << 28,
        (1 << 28) + 777,
        (1usize << 32) - 1,
        1usize << 32,
        (1usize << 32) + 1,
        (1usize << 33) + 17,
    ];
    let random_ns: usize = if cfg!(miri) { 4 } else { 24 };
    let samples_per_n: usize = if cfg!(miri) { 64 } else { 2_000 };
    let mut all_ns = fixed_ns.to_vec();
    for _ in 0..random_ns {
        let shift = 10 + rng.below(24) as u32;
        let n = ((1usize << shift) + (rng.next_u64() as usize % (1usize << shift))).max(MIN_SLOTS);
        all_ns.push(n);
    }

    for n in all_ns {
        let q = Quotient::new(n);
        let q_limit = u64::MAX / (n as u64);
        assert!(q_limit < (1u64 << q.low_bits) || q.low_bits == 64, "seed={seed} n={n}");
        let mask = (1u64 << q.low_bits) - 1;

        let check = |x: u64| {
            let (home, low) = q.split(x);
            assert!(home < n, "seed={seed} n={n} x={x:#x} home={home}");
            assert!(low <= mask, "seed={seed} n={n} x={x:#x} low={low:#x} > {mask:#x}");
            assert_eq!(q.reconstruct(home, low), x, "seed={seed} n={n} x={x:#x}");
        };

        for b in [0u64, 1, 2, 3, (1u64 << 32) - 1, 1u64 << 32, (1u64 << 63) - 1, 1u64 << 63, u64::MAX - 2, u64::MAX - 1, u64::MAX] {
            check(b);
        }
        for h in [0usize, 1, 2, n / 3, n / 2, n.saturating_sub(2), n - 1] {
            let first = if h == 0 { 0 } else { (((h as u128) << 64).div_ceil(n as u128)) as u64 };
            check(first);
            if first > 0 {
                check(first - 1);
            }
            if first < u64::MAX {
                check(first + 1);
            }
        }
        let mut sample = Vec::with_capacity(samples_per_n);
        for _ in 0..samples_per_n {
            let x = rng.next_u64();
            check(x);
            sample.push(x);
        }
        sample.sort_unstable();
        sample.dedup();
        for w in sample.windows(2) {
            assert!(q.split(w[0]).0 <= q.split(w[1]).0, "home monotonicity failed for seed={seed} n={n}: {:#x} vs {:#x}", w[0], w[1]);
        }
    }
}

/// Exact 64-bit round-trip across `Compact48` (`>= 2^21` slots, non-power-of-two
/// and large `> 2^28` lazy `mmap` sizes) covering `0`, `1`, `u64::MAX`,
/// high-bit bucket collisions, displacements far exceeding inline tag bits,
/// near-collision absent probes, read-only `sorted_clusters`, `grow_to`
/// and `rotate` to `fpset/disk.rs`.
#[cfg_attr(miri, ignore)]
#[test]
fn compact_tiers_round_trip_boundaries_collisions_and_overflow() {
    let seed = test_seed();
    let mut rng = tlx_testkit::XorShift64Star::new(seed);

    let n48 = 2_345_679usize;
    let (_scratch, sp) = spill("compact48", None);
    let s = FpSet::with_config(FpConfig::growing(4_700_003).with_initial(n48)).with_disk(sp);
    assert_eq!(s.slots(), n48);
    assert!(s.table_bytes_now() < (n48 + OVERFLOW) * 8, "Compact48 must compress below 8 B/slot");

    let mut expected = HashSet::new();
    let mut add = |x: u64| {
        let want_new = expected.insert(norm(x));
        assert_eq!(s.try_insert(x), Ok(want_new), "seed={seed} fp={x:#x}");
        assert_eq!(s.try_insert(x), Ok(false), "duplicate seed={seed} fp={x:#x}");
    };

    for b in [0u64, 1, 2, u64::MAX - 1, u64::MAX] {
        add(b);
    }
    // 400 fingerprints in one interior home bucket (`d` up to 399 >> d_inline_max)
    // and 400 at the top home bucket `n - 1` (spilling into `OVERFLOW`).
    let mid_base = ((((n48 / 3) as u128) << 64).div_ceil(n48 as u128)) as u64;
    for j in 0..400u64 {
        add(mid_base + j * 2);
        add(u64::MAX - j * 2);
    }
    for _ in 0..5_000 {
        add(rng.next_u64());
    }
    assert!(s.table().overflow_bytes() > 0, "cluster of 400 must exercise Overflow");
    assert_eq!(s.len(), expected.len());
    assert_eq!(s.gauge().bytes(), s.bytes(), "gauge must include live overflow allocations");

    // Near-collision absent fingerprints sharing `(home, q_hi)` in both inline
    // and overflow positions must never false-positive.
    for j in 0..400u64 {
        let absent_mid = mid_base + j * 2 + 1;
        if !expected.contains(&norm(absent_mid)) {
            assert!(!s.contains(absent_mid), "false positive at mid {j}: {absent_mid:#x}");
        }
        let absent_top = u64::MAX - j * 2 - 1;
        if !expected.contains(&norm(absent_top)) {
            assert!(!s.contains(absent_top), "false positive at top {j}: {absent_top:#x}");
        }
    }
    assert!(expected.iter().all(|&x| s.contains(x)));

    // Two consecutive read-only `for_each_in_table_part` sweeps must yield
    // identical ascending fingerprints without touching `Overflow`.
    let mut sorted_want: Vec<u64> = expected.iter().copied().collect();
    sorted_want.sort_unstable();
    let ovf_before = s.table().overflow_bytes();
    for pass in 0..2 {
        let mut got = Vec::new();
        for part in 0..7 {
            // SAFETY: single-threaded.
            unsafe {
                s.for_each_in_table_part(part, 7, |x| {
                    got.push(x);
                    Ok(())
                })
            }
            .unwrap();
        }
        assert_eq!(got, sorted_want, "pass {pass}");
        assert_eq!(s.table().overflow_bytes(), ovf_before, "read-only sorted output must not allocate overflow");
    }
    assert!(expected.iter().all(|&x| s.contains(x)));

    // Grow to another non-power-of-two `Compact48` size and verify lossless recovery.
    // SAFETY: single-threaded.
    assert!(unsafe { s.grow_to(None, 4, 4_600_003) });
    assert_eq!((s.slots(), s.len()), (4_600_003, expected.len()));
    assert_eq!(s.gauge().bytes(), s.bytes(), "gauge must release old overflow after grow");
    assert!(expected.iter().all(|&x| s.contains(x)));

    // Rotate to disk (`fpset/disk.rs`) and verify exact 64-bit run contents + lookups.
    // SAFETY: single-threaded.
    unsafe { s.rotate(None, 4, MIN_SLOTS, true) }.unwrap();
    let mut disk_fps = Vec::new();
    s.for_each_in_run(0, |x| {
        disk_fps.push(x);
        Ok(())
    })
    .unwrap();
    assert_eq!(disk_fps, sorted_want);
    assert!(expected.iter().all(|&x| s.contains(x)));
    // Drop the read-only old table so lookups hit the disk run directly.
    // SAFETY: single-threaded.
    unsafe { s.drop_old() };
    assert_eq!(s.gauge().bytes(), s.bytes());
    assert!(expected.iter().all(|&x| s.contains(x) && s.try_insert(x) == Ok(false)));

    // Also verify large `Compact48` (`n > 2^28`, lazy anonymous `mmap` faults
    // only touched pages).
    let n_big = (1usize << 28) + 777;
    let s_big = FpSet::with_config(FpConfig::fixed(n_big));
    assert_eq!(s_big.table_bytes_now(), (n_big + OVERFLOW).div_ceil(10) * 64);
    let mut exp_big = HashSet::new();
    let base_big = ((((n_big / 5) as u128) << 64).div_ceil(n_big as u128)) as u64;
    for b in [0u64, 1, u64::MAX - 1, u64::MAX] {
        let want_new = exp_big.insert(norm(b));
        assert_eq!(s_big.try_insert(b), Ok(want_new));
    }
    for j in 0..200u64 {
        let x = base_big + j * 2;
        exp_big.insert(norm(x));
        assert_eq!(s_big.try_insert(x), Ok(true));
        let top = u64::MAX - j * 2;
        if exp_big.insert(norm(top)) {
            assert_eq!(s_big.try_insert(top), Ok(true));
        }
    }
    for _ in 0..1_000 {
        let x = rng.next_u64();
        assert_eq!(s_big.try_insert(x), Ok(exp_big.insert(norm(x))));
    }
    assert!(exp_big.iter().all(|&x| s_big.contains(x) && s_big.try_insert(x) == Ok(false)));
}

/// A failing `for_each_in_table_part` callback (such as a failed checkpoint
/// write) must leave both `Raw64` and `Compact48` tables completely intact,
/// preserving every fingerprint and succeeding on retry.
#[cfg_attr(miri, ignore)]
#[test]
fn sorted_clusters_callback_error_preserves_membership() {
    for &n in &[MIN_SLOTS, super::table::COMPACT48_MIN_SLOTS] {
        let s = FpSet::with_config(FpConfig::fixed(n));
        // Insert out-of-order pair `3, 2` into bucket 0, plus an overflow
        // cluster on `Compact48`.
        assert_eq!(s.try_insert(3), Ok(true));
        assert_eq!(s.try_insert(2), Ok(true));
        let mut expected = vec![2u64, 3];
        if n >= super::table::COMPACT48_MIN_SLOTS {
            let mid = ((((n / 2) as u128) << 64).div_ceil(n as u128)) as u64;
            for j in (0..80u64).rev() {
                let x = mid + j;
                assert_eq!(s.try_insert(x), Ok(true));
                expected.push(x);
            }
        }
        expected.sort_unstable();
        let ovf_before = s.table().overflow_bytes();

        // Fail on the very first emitted fingerprint.
        let mut seen_first = false;
        // SAFETY: single-threaded.
        let res = unsafe {
            s.for_each_in_table_part(0, 1, |_fp| {
                if !seen_first {
                    seen_first = true;
                    return Err("simulated checkpoint write failure".into());
                }
                Ok(())
            })
        };
        assert!(res.is_err());
        assert_eq!(s.len(), expected.len());
        assert_eq!(s.table().overflow_bytes(), ovf_before);
        for &x in &expected {
            assert!(s.contains(x), "n={n}: lost fingerprint {x} after callback error");
        }

        // Retry succeeds and emits every fingerprint in ascending order.
        let mut got = Vec::new();
        // SAFETY: single-threaded.
        unsafe {
            s.for_each_in_table_part(0, 1, |x| {
                got.push(x);
                Ok(())
            })
        }
        .unwrap();
        assert_eq!(got, expected);
    }
}

/// Pausing a thread immediately after it wins `hi[pos].compare_exchange` in
/// `Compact48` must not block other workers probing or inserting into the same
/// bucket: wait-free helping completes the publication in O(1).
#[cfg_attr(miri, ignore)]
#[test]
fn paused_claiming_worker_does_not_block_other_workers() {
    let n = super::table::COMPACT48_MIN_SLOTS;
    let s = FpSet::with_config(FpConfig::fixed(n));
    let bucket_base = ((((n / 3) as u128) << 64).div_ceil(n as u128)) as u64;
    let fp_claimed = bucket_base;

    let entered = std::sync::Arc::new(std::sync::Barrier::new(2));
    let release = std::sync::Arc::new(std::sync::Barrier::new(2));
    let entered_h = entered.clone();
    let release_h = release.clone();
    s.table().set_pause_after_claim(move || {
        entered_h.wait();
        release_h.wait();
    });

    std::thread::scope(|sc| {
        let s_ref = &s;
        let claimer = sc.spawn(move || s_ref.try_insert(fp_claimed));
        // Wait until `claimer` holds `CLAIM_HI` on `fp_claimed`'s slot and is paused.
        entered.wait();

        // Four peer workers probe `fp_claimed` and insert into the same bucket
        // while `claimer` remains suspended.
        let mut peers = Vec::new();
        for t in 0..4u64 {
            peers.push(sc.spawn(move || {
                assert!(s_ref.contains(fp_claimed), "peer {t} must help-publish and observe claimed fp");
                assert_eq!(s_ref.try_insert(fp_claimed), Ok(false));
                for k in 1..=32u64 {
                    let x = bucket_base + t * 64 + k;
                    assert_eq!(s_ref.try_insert(x), Ok(true));
                    assert!(s_ref.contains(x));
                }
            }));
        }
        for p in peers {
            p.join().expect("peer worker panicked");
        }

        // Now resume `claimer`; its redundant `lo`/`hi` stores are idempotent.
        release.wait();
        assert_eq!(claimer.join().expect("claimer panicked"), Ok(true));
    });

    assert_eq!(s.len(), 1 + 4 * 32);
    assert!(s.contains(fp_claimed));
    for t in 0..4u64 {
        for k in 1..=32u64 {
            assert!(s.contains(bucket_base + t * 64 + k));
        }
    }
}

/// Fixed `-fpmem` tables enforce their byte limit (including compact overflow
/// headroom), and `Overflow` segments charge the registered `Gauge` and
/// `peak_bytes` immediately as they are allocated and freed (before safepoints).
#[cfg_attr(miri, ignore)]
#[test]
fn fixed_mib_cap_and_live_overflow_gauge() {
    // 1. `fixed_mib(7)` stays strictly within 7 MiB + fixed probe tail.
    let s7 = FpSet::with_config(FpConfig::fixed_mib(7));
    let max7 = (7 << 20) + super::table::Table::probe_tail_bytes(s7.slots());
    let mut rng = tlx_testkit::XorShift64Star::new(test_seed());
    for _ in 0..s7.max_entries() {
        let _ = s7.try_insert(rng.next_u64());
    }
    assert!(s7.bytes() <= max7, "fixed_mib(7) bytes {} > {max7}", s7.bytes());
    assert_eq!(s7.gauge().bytes(), s7.bytes());
    assert!(s7.peak_bytes() >= s7.bytes());

    // 2. `fixed_mib(14)` (`Compact48`) enforces its overflow cap under heavy
    //    clustering and returns `Err(Full)` rather than exceeding 14 MiB + tail.
    let s14 = FpSet::with_config(FpConfig::fixed_mib(14));
    assert!(s14.slots() >= super::table::COMPACT48_MIN_SLOTS);
    assert_eq!(FpConfig::fixed_mib(14).limit_mib(), 14);
    let max14 = (14 << 20) + super::table::Table::probe_tail_bytes(s14.slots());
    let base14 = ((((s14.slots() / 4) as u128) << 64).div_ceil(s14.slots() as u128)) as u64;
    // Pack clusters of 200 across many buckets to drive overflow past 1 MiB.
    let mut saw_full = false;
    'outer: for b in 0..2000usize {
        let bucket = (b * 512) % s14.slots();
        let start = if bucket == 0 { 1 } else { (((bucket as u128) << 64).div_ceil(s14.slots() as u128)) as u64 };
        for j in 0..200u64 {
            match s14.try_insert(start.wrapping_add(j)) {
                Ok(_) => {}
                Err(Full) => {
                    saw_full = true;
                    break 'outer;
                }
            }
        }
    }
    let _ = base14;
    assert!(saw_full, "clustered inserts must hit fixed_mib(14) overflow cap");
    assert!(s14.bytes() <= max14, "fixed_mib(14) bytes {} > {max14}", s14.bytes());
    assert_eq!(s14.gauge().bytes(), s14.bytes(), "live gauge must match table bytes");
    assert!(s14.peak_bytes() >= s14.bytes());

    // 3. Growing `Compact48`: overflow segments charge gauge live BEFORE any
    //    safepoint, and release on grow.
    let n = super::table::COMPACT48_MIN_SLOTS;
    let sg = FpSet::with_config(FpConfig::growing(n * 2).with_initial(n));
    let initial_gauge = sg.gauge().bytes();
    assert_eq!(initial_gauge, sg.bytes());
    let bucket_base = ((((n / 2) as u128) << 64).div_ceil(n as u128)) as u64;
    for j in 0..2_200u64 {
        assert_eq!(sg.try_insert(bucket_base + j), Ok(true));
    }
    let ovf = sg.table().overflow_bytes();
    assert!(ovf >= 32_768, "expected multiple overflow segments, got {ovf}");
    assert_eq!(sg.gauge().bytes(), initial_gauge + ovf, "gauge must reflect overflow before safepoint");
    assert!(sg.peak_bytes() >= initial_gauge + ovf, "peak_bytes must reflect live overflow");
    // SAFETY: single-threaded.
    assert!(unsafe { sg.grow_to(None, 2, n * 2) });
    assert_eq!(sg.gauge().bytes(), sg.bytes(), "gauge must release old overflow after grow");
}

/// Growth admission (`grow_peak_bytes`), fitted sizing (`grow_fit_slots`), and
/// `peak_bytes` stay consistent across: (a) a tier crossing where the array
/// shrinks (`Raw64` -> `Compact48`), (b) worker counts whose chunks exceed the
/// old array, and (c) clustered workloads that allocate destination overflow.
#[cfg_attr(miri, ignore)]
#[test]
fn grow_admission_tier_crossing_large_workers_and_dest_overflow() {
    let cmin = super::table::COMPACT48_MIN_SLOTS;

    // (a) Tier crossing that shrinks the physical array (`2_000_000` Raw64 =
    //     16.03 MiB -> `2_097_152` Compact48 = 13.45 MiB).
    let raw_n = cmin - 97_152;
    let s_cross = FpSet::with_config(FpConfig::growing(cmin).with_initial(raw_n));
    let old_bytes = s_cross.table_bytes_now();
    let new_array = FpSet::table_bytes(cmin);
    assert!(old_bytes > new_array, "tier crossing must shrink array bytes");
    let predicted = s_cross.grow_peak_bytes(cmin, 1);
    assert!(predicted >= old_bytes, "predicted peak {predicted} must cover old mapping {old_bytes}");
    // SAFETY: single-threaded.
    assert!(unsafe { s_cross.grow_to(None, 1, cmin) });
    assert!(s_cross.peak_bytes() >= old_bytes);
    assert_eq!(s_cross.peak_bytes(), predicted);

    // (b) Worker count whose chunks exceed the old array (`1M` raw = 8 MiB,
    //     32 workers * 512 KiB = 16 MiB > 8 MiB): `grow_fit_slots` and
    //     `grow_peak_bytes` must both cap retained bytes at `old.bytes()`.
    let s_many = FpSet::with_config(FpConfig::growing(cmin * 2).with_initial(1 << 20));
    let old_m = s_many.table_bytes_now();
    let target_m = cmin;
    assert_eq!(s_many.grow_peak_bytes(target_m, 32), old_m + FpSet::table_bytes(target_m));
    let room = old_m + FpSet::table_bytes(target_m);
    let fit = s_many.grow_fit_slots(room, 32);
    assert!(fit >= target_m, "capped retained bytes must let grow_fit_slots reach {target_m}, got {fit}");

    // (c) Adversarial clustering (`48` fingerprints in every 128th destination
    //     bucket = 786,432 entries = 75% load of `1M` raw slots) growing from
    //     `Raw64` (`1M` slots) to `Compact48` (`2M` slots, `d_inline_max = 29`):
    //     `grow_peak_bytes` must bound actual destination allocation including
    //     destination overflow segments.
    let raw_src = 1usize << 20;
    let dst_n = cmin;
    let s_ovf = FpSet::with_config(FpConfig::growing(dst_n).with_initial(raw_src));
    for b in (0..dst_n).step_by(128) {
        let start = if b == 0 { 1 } else { (((b as u128) << 64).div_ceil(dst_n as u128)) as u64 };
        for j in 0..48u64 {
            assert_eq!(s_ovf.try_insert(start + j), Ok(true));
        }
    }
    let pred_ovf = s_ovf.grow_peak_bytes(dst_n, 1);
    // SAFETY: single-threaded.
    assert!(unsafe { s_ovf.grow_to(None, 1, dst_n) });
    assert!(s_ovf.table().overflow_bytes() > 0, "clustered grow must allocate destination overflow");
    assert!(
        pred_ovf >= s_ovf.bytes(),
        "grow_peak_bytes {pred_ovf} underestimated final destination bytes {} (overflow={})",
        s_ovf.bytes(),
        s_ovf.table().overflow_bytes()
    );
    assert_eq!(s_ovf.gauge().bytes(), s_ovf.bytes());
}

/// `-fpbits` controls work-unit granularity on mapped `grow_to` while keeping
/// every unit page-aligned so physical pages are still reclaimed.
#[cfg_attr(miri, ignore)]
#[test]
fn fpbits_controls_mapped_grow_granularity() {
    let initial = 2usize << 20;
    let target = 4usize << 20;
    let s0 = FpSet::with_config(FpConfig::growing(target).with_initial(initial).with_bits(0));
    let s8 = FpSet::with_config(FpConfig::growing(target).with_initial(initial).with_bits(8));
    let u0 = s0.table().rehash_unit_slots(s0.shards());
    let u8 = s8.table().rehash_unit_slots(s8.shards());
    assert!(u8 < u0, "-fpbits 8 unit ({u8}) must be finer than -fpbits 0 unit ({u0})");

    for i in 1..=20_000u64 {
        assert_eq!(s8.try_insert(fp(i)), Ok(true));
    }
    // SAFETY: single-threaded (4 helper threads inside `grow_to`).
    assert!(unsafe { s8.grow_to(None, 4, target) });
    assert_eq!((s8.slots(), s8.len()), (target, 20_000));
    for i in 1..=20_000u64 {
        assert!(s8.contains(fp(i)));
    }
}

/// Eight threads contend on the same home bucket in `Compact48`, driving
/// displacements past 2,400 slots (across three `Overflow` segments) while
/// racing on wait-free claim helping and duplicate inserts.
#[cfg_attr(miri, ignore)]
#[test]
fn concurrent_overflow_displacements_across_segments() {
    let n = super::table::COMPACT48_MIN_SLOTS;
    let (_scratch, sp) = spill("conc-ovf", None);
    let s = FpSet::with_config(FpConfig::growing(n * 2).with_initial(n)).with_disk(sp);
    let base = ((((n / 2) as u128) << 64).div_ceil(n as u128)) as u64;
    let count = 2_500u64;
    let inserted = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for t in 0..8u64 {
            let (s, inserted) = (&s, &inserted);
            sc.spawn(move || {
                for k in 0..count {
                    let idx = (k + t * 313) % count;
                    if s.try_insert(base + idx * 2).unwrap() {
                        inserted.fetch_add(1, Ordering::Relaxed);
                    }
                }
            });
        }
    });
    assert_eq!(inserted.load(Ordering::Relaxed), count as usize);
    assert_eq!(s.len(), count as usize);
    // > 2,048 overflow entries spans segments 0 (1024), 1 (1024) and 2 (2048).
    assert!(s.table().overflow_bytes() >= (1024 + 1024 + 2048) * 8);
    assert_eq!(s.gauge().bytes(), s.bytes());
    for k in 0..count {
        assert!(s.contains(base + k * 2));
        assert!(!s.contains(base + k * 2 + 1));
    }
    // SAFETY: single-threaded after scope ends.
    assert!(unsafe { s.grow(None) });
    assert_eq!(s.gauge().bytes(), s.bytes());
    for k in 0..count {
        assert!(s.contains(base + k * 2));
    }
    // SAFETY: single-threaded.
    unsafe { s.rotate(None, 4, MIN_SLOTS, false) }.unwrap();
    assert_eq!(s.gauge().bytes(), s.bytes());
    for k in 0..count {
        assert!(s.contains(base + k * 2));
    }
}

/// Chunked parallel rehash (`madvise` page reclamation) keeps both accounted
/// `peak_bytes` and per-mapping physical page residency (`mincore`) bounded by
/// `new_table + slack` across every rehash step rather than `old + new`.
///
/// The `mincore` measurements run on base pages (`MADV_NOHUGEPAGE`): Linux
/// splits a huge page on a partial-range `MADV_DONTNEED` and defers freeing the
/// remaining subpages until memory pressure, so asserting the exact residency
/// a chunk releases on a huge-page-backed mapping is kernel-dependent. The
/// final reclaim check therefore bounds the residual by a fraction of the old
/// table instead of requiring every page to be gone; the peak-residency bound
/// stays the tight physical assertion.
#[cfg_attr(miri, ignore)]
#[test]
fn chunked_grow_bounds_peak_bytes_and_rss() {
    let initial = 4usize << 20; // ~25.6 MiB
    let target = 8usize << 20; // ~51.2 MiB (`old + new` would be ~76.8 MiB)
    let s = FpSet::with_config(FpConfig::growing(target).with_initial(initial));
    let old_bytes = s.table_bytes_now();
    let new_bytes = FpSet::table_bytes(target);
    let fill = (initial * 3 / 4) as u64 - 64;
    std::thread::scope(|sc| {
        for me in 0..4u64 {
            let s = &s;
            sc.spawn(move || {
                for i in (me..fill).step_by(4) {
                    let _ = s.insert_by(me as usize, fp(i + 1), &mut 0, || {});
                }
            });
        }
    });
    assert_eq!(s.len(), fill as usize);
    // SAFETY: single-threaded (4 helper threads run inside `grow_to`).
    assert!(unsafe { s.grow_to(None, 4, target) });
    assert!(
        s.peak_bytes() <= new_bytes + 4 * super::table::REHASH_CHUNK_BYTES + (64 << 10),
        "peak_bytes={} exceeded new_bytes={} + chunk slack (old+new={})",
        s.peak_bytes(),
        new_bytes,
        old_bytes + new_bytes
    );

    // Also step chunk-by-chunk on Linux and measure exact `mincore` physical
    // residency of `old + new` while `old` is still mapped, immune to other
    // tests running concurrently in this process.
    #[cfg(target_os = "linux")]
    {
        let g = Arc::new(Gauge::new());
        let old = super::table::Table::new(initial, 0, g.clone(), usize::MAX);
        // Measure exact physical release on base pages: a partial-range
        // `MADV_DONTNEED` on a huge page splits it and leaves the rest resident
        // until memory pressure, which makes the `mincore` counts below depend
        // on the kernel's huge-page decisions instead of on the chunked rehash.
        old.disable_huge_pages();
        for i in 0..fill {
            old.place(norm(fp(i + 1)));
        }
        let new = super::table::Table::new(target, 0, g, usize::MAX);
        // Likewise, a huge-page fault in `new` would materialize 2 MiB per
        // touched block and blur the measured peak with untouched pages.
        new.disable_huge_pages();
        assert!(old.resident_bytes() >= old_bytes * 9 / 10, "old table should be resident before rehash");
        assert_eq!(new.resident_bytes(), 0, "new table mmap starts non-resident");
        let chunk = old.rehash_chunk_slots();
        let len = old.slot_len();
        let mut peak_res = old.resident_bytes() + new.resident_bytes();
        for c in 0..len.div_ceil(chunk) {
            let lo = c * chunk;
            let hi = ((c + 1) * chunk).min(len);
            old.rehash_range(lo, hi, &new);
            // SAFETY: single-threaded, `lo..hi` is never read again.
            unsafe { old.discard_slot_range(lo, hi) };
            peak_res = peak_res.max(old.resident_bytes() + new.resident_bytes());
        }
        // `old` is still mapped here, yet virtually all of its physical pages
        // have been reclaimed. Report old, destination, and saved peak
        // residency so a CI-only regression is diagnosable from the log alone.
        let old_res = old.resident_bytes();
        let new_res = new.resident_bytes();
        // A host that defers freeing the subpages of a huge page split by a
        // partial-range `MADV_DONTNEED` can leave up to one reclaim unit
        // resident even on a `MADV_NOHUGEPAGE` VMA. Require the chunked
        // discard to release at least three quarters of the old table rather
        // than an exact zero, so a kernel-dependent residual does not fail the
        // run; a discard that stopped releasing the old table would leave all
        // `old_bytes` resident, and `peak_res` below is the tight bound.
        assert!(
            old_res <= old_bytes / 4,
            "old table still holds {old_res} B resident (new {new_res} B, peak {peak_res} B, old_bytes {old_bytes} B)"
        );
        assert!(
            peak_res <= new_bytes + (4 << 20),
            "peak physical residency {} MiB exceeded new_bytes {} MiB + 4 MiB (old+new={} MiB; old={old_res} B, new={new_res} B)",
            peak_res >> 20,
            new_bytes >> 20,
            (old_bytes + new_bytes) >> 20
        );
    }
}

/// A mapped table starts on the `REHASH_CHUNK_BYTES` grid, so a 2 MiB chunked
/// `madvise` discard covers whole huge pages instead of partially covering one
/// (which some kernels leave resident). Covers both storage tiers, table sizes
/// that are and are not page multiples, and several OS-chosen base addresses.
#[cfg_attr(miri, ignore)]
#[test]
fn mapped_tables_are_chunk_aligned() {
    let g = Arc::new(Gauge::new());
    for slots in [1usize << 20, (1 << 20) + 1, (4 << 20) + 1, (8 << 20) + 4_096] {
        for _ in 0..8 {
            let t = super::table::Table::new(slots, 0, g.clone(), usize::MAX);
            assert!(t.is_mapped(), "{slots}-slot table should be mapped");
            assert_eq!(t.buffer_addr() % super::table::REHASH_CHUNK_BYTES, 0, "{slots}-slot table base is not chunk-aligned");
        }
    }
}

/// Interior probe clusters can travel past both `OVERFLOW` (4,096) and large
/// `d_inline_max` values (e.g. `7,679` at `2^29` slots). Both `fixed_mib(4096)`
/// and `grow_peak_bytes` targeting `>= 2^29` slots must preserve overflow
/// capacity and bound destination overflow without a `d_max >= OVERFLOW`
/// shortcut.
#[cfg_attr(miri, ignore)]
#[test]
fn large_fixed_mib_and_interior_cluster_grow_overflow() {
    // 0. Every integer `-fpmem` budget from 1 through 4,096 MiB must either
    //    pick Raw64 (using the full budget) or Compact48 with a full 1 MiB
    //    overflow reserve inside the byte budget. In particular, 13 MiB stays
    //    on Raw64 and 14 MiB enters Compact48 with 1 MiB of overflow, and all
    //    three adjacent budgets (12, 13, 14 MiB) accept `1..=64` in bucket 0.
    for mib in 1usize..=4_096 {
        let cfg = FpConfig::fixed_mib(mib);
        assert_eq!(cfg.limit_mib(), mib, "fixed_mib({mib}).limit_mib() mismatch");
        if mib <= 13 {
            assert!(cfg.limit < super::table::COMPACT48_MIN_SLOTS, "fixed_mib({mib}) must stay Raw64");
            assert_eq!(cfg.overflow_cap, Some(0));
            assert_eq!(super::table::Table::home_bytes(cfg.limit), mib << 20);
        } else {
            assert!(cfg.limit >= super::table::COMPACT48_MIN_SLOTS, "fixed_mib({mib}) must select Compact48");
            let cap = cfg.overflow_cap.expect("compact fixed_mib must cap overflow");
            assert!(cap >= (1 << 20), "fixed_mib({mib}) overflow cap {cap} < 1 MiB");
            assert!(super::table::Table::home_bytes(cfg.limit) + cap <= (mib << 20), "fixed_mib({mib}) home + overflow exceeded {mib} MiB");
        }
    }
    for mib in [12usize, 13usize, 14usize] {
        let s = FpSet::with_config(FpConfig::fixed_mib(mib));
        let max_bytes = (mib << 20) + super::table::Table::probe_tail_bytes(s.slots());
        if mib <= 13 {
            assert!(s.slots() < super::table::COMPACT48_MIN_SLOTS);
        } else {
            assert!(s.slots() >= super::table::COMPACT48_MIN_SLOTS);
        }
        for k in 1..=64u64 {
            assert_eq!(s.try_insert(k), Ok(true), "fixed_mib({mib}) failed at fingerprint {k}");
        }
        assert_eq!(s.len(), 64);
        assert!(s.bytes() <= max_bytes, "fixed_mib({mib}) bytes {} > {max_bytes}", s.bytes());
        assert_eq!(s.gauge().bytes(), s.bytes());
    }

    // 1. Increasing `-fpmem` across compact tier transitions (51 -> 52 MiB,
    //    204 -> 205 MiB, and 3072 -> 4096 MiB) must keep overflow capacity
    //    nondecreasing while staying within `mib MiB + probe_tail`.
    for mib in [51usize, 52usize, 205usize] {
        let s = FpSet::with_config(FpConfig::fixed_mib(mib));
        let max_bytes = (mib << 20) + super::table::Table::probe_tail_bytes(s.slots());
        for group in 0..512u64 {
            for j in 1..=200u64 {
                assert_eq!(s.try_insert((group << 52) + j), Ok(true), "fixed_mib({mib}) failed at ({group}, {j})");
            }
        }
        assert_eq!(s.len(), 512 * 200);
        assert!(s.bytes() <= max_bytes, "fixed_mib({mib}) bytes {} > {max_bytes}", s.bytes());
        assert_eq!(s.gauge().bytes(), s.bytes());
    }
    for mib in [51usize, 52usize] {
        let s = FpSet::with_config(FpConfig::fixed_mib(mib));
        for k in 1..=35_000u64 {
            assert_eq!(s.try_insert(k), Ok(true), "fixed_mib({mib}) failed at sequential key {k}");
        }
        assert_eq!(s.len(), 35_000);
        assert_eq!(s.gauge().bytes(), s.bytes());
    }
    for mib in [3072usize, 4096usize] {
        let s = FpSet::with_config(FpConfig::fixed_mib(mib));
        let max_bytes = (mib << 20) + super::table::Table::probe_tail_bytes(s.slots());
        for k in 1..=8_000u64 {
            assert_eq!(s.try_insert(k), Ok(true), "fixed_mib({mib}) failed at key {k}");
        }
        assert_eq!(s.len(), 8_000);
        assert!(s.bytes() <= max_bytes, "fixed_mib({mib}) bytes {} > {max_bytes}", s.bytes());
        assert_eq!(s.gauge().bytes(), s.bytes());
        for k in [1u64, 4_096, 7_679, 7_680, 8_000] {
            assert!(s.contains(k));
        }
    }

    // 2. Growing an interior cluster of 10,000 keys starting at `1 << 63` from
    //    `2^28` to `2^29` slots (`d_inline_max = 7,679 > OVERFLOW = 4,096`):
    //    `grow_peak_bytes` must account for the destination overflow segments.
    let src = 1usize << 28;
    let dst = 1usize << 29;
    let s = FpSet::with_config(FpConfig::growing(dst).with_initial(src));
    let start = 1u64 << 63;
    for k in 0..10_000u64 {
        assert_eq!(s.try_insert(start + k), Ok(true));
    }
    let dst_array = FpSet::table_bytes(dst);
    let pred_ovf = s.table().max_grow_overflow_bytes(dst, s.table_len());
    assert!(pred_ovf >= 32_768, "expected >= 32,768 B predicted destination overflow, got {pred_ovf}");
    let pred_peak = s.grow_peak_bytes(dst, 1);
    assert!(pred_peak >= dst_array + pred_ovf);
    // SAFETY: single-threaded.
    assert!(unsafe { s.grow_to(None, 4, dst) });
    assert_eq!(s.len(), 10_000);
    assert!(s.table().overflow_bytes() >= 32_768, "expected destination overflow >= 32 KiB, got {}", s.table().overflow_bytes());
    assert!(pred_ovf >= s.table().overflow_bytes(), "predicted {pred_ovf} < actual {}", s.table().overflow_bytes());
    assert_eq!(s.gauge().bytes(), s.bytes());
    for k in [0u64, 4_096, 7_679, 7_680, 9_999] {
        assert!(s.contains(start + k));
    }
}

/// Fixed-cap overflow uses a single demand-zero mapping (0 resident bytes
/// before use, zero candidate buffers under contention) and enforces its cap
/// strictly across concurrent writers.
#[cfg_attr(miri, ignore)]
#[test]
fn fixed_overflow_is_demand_zero_and_capped_under_contention() {
    let s = FpSet::with_config(FpConfig::fixed_mib(14));
    let max_bytes = (14 << 20) + super::table::Table::probe_tail_bytes(s.slots());
    #[cfg(target_os = "linux")]
    assert_eq!(s.table().overflow_fixed_resident_bytes(), 0, "fixed overflow mapping must start demand-zero");
    assert_eq!(s.table().overflow_bytes(), 0);
    assert_eq!(s.gauge().bytes(), s.bytes());

    let saw_full = AtomicBool::new(false);
    std::thread::scope(|sc| {
        for t in 0..8usize {
            let (s, saw_full) = (&s, &saw_full);
            sc.spawn(move || {
                for b in 0..400usize {
                    let bucket = ((t * 400 + b) * 512) % s.slots();
                    let start = if bucket == 0 { 1 } else { (((bucket as u128) << 64).div_ceil(s.slots() as u128)) as u64 };
                    for j in 0..200u64 {
                        if s.try_insert(start.wrapping_add(j)).is_err() {
                            saw_full.store(true, Ordering::Relaxed);
                            return;
                        }
                    }
                }
            });
        }
    });
    assert!(saw_full.load(Ordering::Relaxed), "concurrent overflow must hit fixed_mib(14) cap");
    assert!(s.bytes() <= max_bytes, "bytes {} exceeded fixed cap {max_bytes}", s.bytes());
    assert_eq!(s.gauge().bytes(), s.bytes());
    assert!(s.peak_bytes() >= s.bytes());
}
