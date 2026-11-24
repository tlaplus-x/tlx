use super::*;

/// States of `W` words: (i, i / 3, ...).
struct Words(usize);

impl StateCodec<Vec<u64>> for Words {
    fn words(&self) -> usize {
        self.0
    }
    fn encode(&self, s: &Vec<u64>, out: &mut [u64]) -> u64 {
        out.copy_from_slice(s);
        s.iter().fold(7, |h, w| h.wrapping_mul(31).wrapping_add(*w))
    }
    fn decode(&self, w: &[u64], depth: u32, fp: u64) -> Vec<u64> {
        assert_eq!(self.encode(&w.to_vec(), &mut vec![0; w.len()]), fp);
        let mut v = w.to_vec();
        v.push(depth as u64);
        v
    }
}

fn state(w: usize, i: u64) -> Vec<u64> {
    (0..w as u64).map(|k| if k == 0 { i } else { i / (k + 2) }).collect()
}

fn configs() -> Vec<Config> {
    let mut v = Vec::new();
    for kinds in [BlockKinds::Raw, BlockKinds::Xor, BlockKinds::Auto] {
        for seg_bytes in [64, 300, 4096, 1 << 20] {
            v.push(Config { seg_bytes, kinds, compress_above: 2000 });
        }
    }
    v
}

/// Write `n` states per depth for `depths`, install, read back: the
/// same states, in order, with segment boundaries anywhere.
#[test]
fn write_install_read_in_order() {
    for cfg in configs() {
        for w in [1, 5, 40] {
            let codec = Words(w);
            for encoded in [false, true] {
                let q: Queue<'_, Vec<u64>> = Queue::new(encoded.then_some(&codec as &dyn StateCodec<_>), cfg, 1);
                let mut wr = q.writer();
                let mut want = Vec::new();
                let mut i = 0;
                for depth in [3, 4] {
                    for _ in 0..700 {
                        let s = state(w, i);
                        want.push((s.clone(), 1000 + i, depth));
                        q.push(&mut wr, Task { state: s, log: 1000 + i, depth });
                        i += 1;
                    }
                }
                assert_eq!(wr.len(), 1400);
                q.submit(0, &mut wr);
                q.install();
                assert_eq!(q.unclaimed(), 1400);
                let mut prev = q.scratch();
                let mut got = Vec::new();
                while let Some(mut r) = q.claim(0, &mut prev).unwrap() {
                    assert!(r.left() <= BLOCK);
                    while let Some(t) = q.read(&mut r, &mut prev, &mut None) {
                        let mut s = t.state;
                        // (Decoded states end with their depth.)
                        if s.len() > w {
                            assert_eq!(s.pop(), Some(t.depth as u64));
                        }
                        got.push((s, t.log, t.depth));
                    }
                }
                assert_eq!(got, want, "{cfg:?} w={w} encoded={encoded}");
                assert_eq!(q.unclaimed(), 0);
                drop(prev);
                assert_eq!(q.mem().bytes(), 0);
            }
        }
    }
}

/// Several workers claim blocks of a level concurrently: every state is
/// read exactly once and the queue's memory is released (nothing here
/// depends on how the threads interleave).
#[test]
fn concurrent_claims() {
    for cfg in configs() {
        let codec = Words(3);
        for encoded in [false, true] {
            let q: Queue<'_, Vec<u64>> = Queue::new(encoded.then_some(&codec as &dyn StateCodec<_>), cfg, 8);
            let workers = 8;
            let per = 5000;
            std::thread::scope(|sc| {
                for me in 0..workers {
                    let q = &q;
                    sc.spawn(move || {
                        let mut wr = q.writer();
                        for k in 0..per {
                            let i = (me * per + k) as u64;
                            q.push(&mut wr, Task { state: state(3, i), log: i, depth: 1 });
                        }
                        q.submit(me, &mut wr);
                    });
                }
            });
            q.install();
            let total = (workers * per) as u64;
            assert_eq!(q.unclaimed(), total);
            let seen: Vec<AtomicU64> = (0..total).map(|_| AtomicU64::new(0)).collect();
            std::thread::scope(|sc| {
                for me in 0..workers {
                    let (seen, q) = (&seen, &q);
                    sc.spawn(move || {
                        let mut prev = q.scratch();
                        while let Some(mut r) = q.claim(me, &mut prev).unwrap() {
                            while let Some(t) = q.read(&mut r, &mut prev, &mut None) {
                                assert_eq!(&t.state[..3], &state(3, t.log)[..]);
                                seen[t.log as usize].fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    });
                }
            });
            assert!(seen.iter().all(|c| c.load(Ordering::Relaxed) == 1), "{cfg:?} encoded={encoded}");
            assert_eq!(q.mem().bytes(), 0);
        }
    }
}

/// With several lists, claims take only part of a block when few states
/// are left (guided self-scheduling), down to single states. One thread
/// claims everything, so the sizes are fixed by the queue, not by
/// scheduling; every state is still read exactly once, in list order.
#[test]
fn claims_take_parts_of_blocks() {
    for cfg in configs() {
        let codec = Words(3);
        for encoded in [false, true] {
            if encoded && cfg.kinds != BlockKinds::Raw {
                continue; // (Not every encoded block can be split.)
            }
            let lists = 8;
            let per = 5000;
            let q: Queue<'_, Vec<u64>> = Queue::new(encoded.then_some(&codec as &dyn StateCodec<_>), cfg, lists);
            for me in 0..lists {
                let mut wr = q.writer();
                for k in 0..per {
                    let i = (me * per + k) as u64;
                    q.push(&mut wr, Task { state: state(3, i), log: i, depth: 1 });
                }
                q.submit(me, &mut wr);
            }
            q.install();
            let total = (lists * per) as u64;
            assert_eq!(q.unclaimed(), total);
            let mut seen = vec![0u32; total as usize];
            let mut smallest = BLOCK;
            let mut prev = q.scratch();
            while let Some(mut r) = q.claim(0, &mut prev).unwrap() {
                smallest = smallest.min(r.left());
                while let Some(t) = q.read(&mut r, &mut prev, &mut None) {
                    assert_eq!(&t.state[..3], &state(3, t.log)[..]);
                    seen[t.log as usize] += 1;
                }
            }
            assert!(seen.iter().all(|&c| c == 1), "{cfg:?} encoded={encoded}");
            assert_eq!(smallest, 1, "claims of parts of blocks: {cfg:?} encoded={encoded}");
            assert_eq!(q.unclaimed(), 0);
            drop(prev);
            assert_eq!(q.mem().bytes(), 0);
        }
    }
}

/// Unclaimed blocks of the current level stay ahead of the next level's.
#[test]
fn install_keeps_unclaimed() {
    let q: Queue<'_, u32> = Queue::new(None, Config::default(), 1);
    let mut wr = q.writer();
    for i in 0..600 {
        q.push(&mut wr, Task { state: i, log: i as u64, depth: 1 });
    }
    q.submit(0, &mut wr);
    q.install();
    let mut prev = q.scratch();
    let mut r = q.claim(0, &mut prev).unwrap().unwrap();
    assert_eq!(q.read(&mut r, &mut prev, &mut None).unwrap().state, 0);
    for i in 600..610 {
        q.push(&mut wr, Task { state: i, log: i as u64, depth: 2 });
    }
    q.submit(1, &mut wr);
    q.install();
    assert_eq!(q.unclaimed(), 600 - 256 + 10);
    let mut got = Vec::new();
    while let Some(mut r) = q.claim(0, &mut prev).unwrap() {
        while let Some(t) = q.read(&mut r, &mut prev, &mut None) {
            got.push(t.state);
        }
    }
    assert_eq!(got, (256..610).collect::<Vec<_>>());
}

/// `BlockKinds::Auto`: objects, XOR blocks once the queue is large,
/// objects again once it is small; the order is kept throughout.
#[test]
fn auto_switches_kinds_in_order() {
    let codec = Words(4);
    let q: Queue<'_, Vec<u64>> = Queue::new(Some(&codec), Config { compress_above: 10_000, ..Config::default() }, 1);
    let kinds = |q: &Queue<'_, Vec<u64>>| -> Vec<bool> {
        let lists = q.level.read();
        lists[0].blocks.iter().map(|b| matches!(b.lock().as_ref(), Some(Block::Encoded { .. }))).collect()
    };
    let mut wr = q.writer();
    let mut prev = q.scratch();
    let mut i = 0;
    for round in 0..2 {
        for _ in 0..3 * BLOCK {
            q.push(&mut wr, Task { state: state(4, i), log: i, depth: 1 });
            i += 1;
        }
        q.submit(0, &mut wr);
        q.install();
        // (A block of objects of 4 words is about 18 KB, counted when closed.)
        assert_eq!(kinds(&q), [false, false, true], "round {round}");
        let mut got = Vec::new();
        while let Some(mut r) = q.claim(0, &mut prev).unwrap() {
            while let Some(t) = q.read(&mut r, &mut prev, &mut None) {
                got.push(t.log);
            }
        }
        assert_eq!(got, (i - 3 * BLOCK as u64..i).collect::<Vec<_>>());
    }
}

/// XOR blocks are much smaller than raw ones for sibling-like states.
#[test]
fn xor_blocks_compress() {
    let codec = Words(20);
    let size = |kinds| {
        let q: Queue<'_, Vec<u64>> = Queue::new(Some(&codec), Config { kinds, ..Config::default() }, 1);
        let mut wr = q.writer();
        for i in 0..10_000 {
            q.push(&mut wr, Task { state: state(20, i), log: i, depth: 1 });
        }
        q.submit(0, &mut wr);
        q.install();
        q.mem().bytes()
    };
    let (raw, xor) = (size(BlockKinds::Raw), size(BlockKinds::Xor));
    assert!(raw >= 10_000 * codec::raw_size(20), "{raw}");
    assert!(xor * 4 < raw, "raw {raw} xor {xor}");
}

/// Keep the parent owned while tlx creates and removes its spill directory.
fn spill_at(name: &str, f: impl FnOnce(&mut crate::io::SpillConfig)) -> (tlx_testkit::TempDir, Spill) {
    let scratch = tlx_testkit::TempDir::new(name);
    let mut cfg =
        crate::io::SpillConfig { mode: crate::io::SpillMode::Always, dir: Some(scratch.child_path("spill")), ..Default::default() };
    f(&mut cfg);
    (scratch, Spill::new(cfg))
}

/// Read the current level with one worker, pushing a new state for
/// each state read while `more` (as a search does): the logs read.
fn read_level(q: &Queue<'_, Vec<u64>>, wr: &mut Writer<Vec<u64>>, prev: &mut XorPrev, next: &mut u64, more: bool) -> Vec<u64> {
    let mut got = Vec::new();
    while let Some(mut r) = q.claim(0, prev).unwrap() {
        while let Some(t) = q.read(&mut r, prev, &mut None) {
            assert_eq!(&t.state[..5], &state(5, t.log)[..]);
            got.push(t.log);
            if more {
                q.push(wr, Task { state: state(5, *next), log: *next, depth: t.depth + 1 });
                *next += 1;
                if (*next).is_multiple_of(300) {
                    q.spill_writer(wr);
                }
            }
        }
    }
    got
}

/// One worker, the next level written (and spilled) while the current
/// one is read back: the exact FIFO order; nothing left in memory or on
/// disk at the end.
#[test]
fn spilled_levels_read_back_in_order() {
    for kinds in [BlockKinds::Raw, BlockKinds::Xor] {
        for seg_bytes in [300, 4096] {
            let codec = Words(5);
            let (_scratch, sp) = spill_at("order", |_| {});
            let q: Queue<'_, Vec<u64>> =
                Queue::new(Some(&codec as &dyn StateCodec<_>), Config { seg_bytes, kinds, compress_above: 0 }, 1).with_spill(&sp, "queue");
            assert!(q.spill_on(true));
            let mut wr = q.writer();
            let mut prev = q.scratch();
            let mut next = 0;
            for _ in 0..3000 {
                q.push(&mut wr, Task { state: state(5, next), log: next, depth: 1 });
                next += 1;
            }
            let mut got = Vec::new();
            for level in 0..4 {
                q.submit(0, &mut wr);
                q.install();
                got.extend(read_level(&q, &mut wr, &mut prev, &mut next, level < 3));
            }
            assert_eq!(got, (0..12_000).collect::<Vec<_>>(), "{kinds:?} {seg_bytes}");
            let c = sp.counters();
            // (Not the first segments of a level: read first.)
            assert!(q.spilled_segments() > 2 && c.read > 0, "{kinds:?} {seg_bytes}: {c:?}");
            assert_eq!(q.mem().bytes(), 0);
            assert_eq!(c.used, 0, "disk space given back");
            assert!(sp.error().is_none());
            drop(q);
            // IO threads own their store references until they finish each
            // request, even after publishing its result. Wait for both
            // barriers before checking spill-directory cleanup.
            sp.wait_for_writes();
            sp.wait_for_reads();
            assert!(sp.dir().is_none());
        }
    }
}

/// Eight workers claim a level while its tail goes to disk and is read
/// ahead: every state is read exactly once.
#[test]
fn concurrent_claims_of_spilled_segments() {
    for kinds in [BlockKinds::Raw, BlockKinds::Xor] {
        let codec = Words(3);
        let (_scratch, sp) = spill_at("claims", |_| {});
        let workers = 8;
        let q: Queue<'_, Vec<u64>> =
            Queue::new(Some(&codec as &dyn StateCodec<_>), Config { seg_bytes: 1000, kinds, compress_above: 0 }, workers)
                .with_spill(&sp, "queue");
        let per = 5000;
        std::thread::scope(|sc| {
            for me in 0..workers {
                let q = &q;
                sc.spawn(move || {
                    let mut wr = q.writer();
                    for k in 0..per {
                        let i = (me * per + k) as u64;
                        q.push(&mut wr, Task { state: state(3, i), log: i, depth: 1 });
                    }
                    q.submit(me, &mut wr);
                });
            }
        });
        q.install();
        q.spill_on(true);
        q.spill_tail();
        let total = (workers * per) as u64;
        let seen: Vec<AtomicU64> = (0..total).map(|_| AtomicU64::new(0)).collect();
        let done = AtomicBool::new(false);
        std::thread::scope(|sc| {
            let (seen, q, done) = (&seen, &q, &done);
            // (The budget monitor's part.)
            sc.spawn(move || {
                while !done.load(Ordering::Relaxed) {
                    q.spill_tail();
                    std::thread::yield_now();
                }
            });
            let hs: Vec<_> = (0..workers)
                .map(|me| {
                    sc.spawn(move || {
                        let mut prev = q.scratch();
                        while let Some(mut r) = q.claim(me, &mut prev).unwrap() {
                            while let Some(t) = q.read(&mut r, &mut prev, &mut None) {
                                assert_eq!(&t.state[..3], &state(3, t.log)[..]);
                                seen[t.log as usize].fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    })
                })
                .collect();
            for h in hs {
                h.join().unwrap();
            }
            done.store(true, Ordering::Relaxed);
        });
        assert!(seen.iter().all(|c| c.load(Ordering::Relaxed) == 1), "{kinds:?}");
        assert!(q.spilled_segments() > 0 && sp.counters().read > 0, "{kinds:?}");
        assert_eq!(q.mem().bytes(), 0);
        assert!(sp.error().is_none());
    }
}

/// Writes that fail keep the segments in memory: the level reads the
/// same; the error is recorded (the search stops with it).
#[test]
fn failed_writes_keep_segments() {
    let codec = Words(5);
    let (_scratch, sp) = spill_at("fail", |c| c.fail_after = Some(2000));
    let q: Queue<'_, Vec<u64>> =
        Queue::new(Some(&codec as &dyn StateCodec<_>), Config { seg_bytes: 600, kinds: BlockKinds::Xor, compress_above: 0 }, 1)
            .with_spill(&sp, "queue");
    q.spill_on(true);
    let mut wr = q.writer();
    let mut prev = q.scratch();
    let mut next = 0;
    for _ in 0..2000 {
        q.push(&mut wr, Task { state: state(5, next), log: next, depth: 1 });
        next += 1;
    }
    q.submit(0, &mut wr);
    q.install();
    assert_eq!(read_level(&q, &mut wr, &mut prev, &mut next, false), (0..2000).collect::<Vec<_>>());
    assert!(sp.error().is_some_and(|e| e.0.contains("injected write error")), "{:?}", sp.error());
}

/// A corrupt spilled segment: claiming its first block fails (the block
/// stays unclaimed, and so do the following ones), with the checksum
/// error.
#[test]
fn corrupt_segment_fails_its_claim() {
    use std::os::unix::fs::FileExt;
    let codec = Words(5);
    let (_scratch, sp) = spill_at("corrupt", |_| {});
    let q: Queue<'_, Vec<u64>> =
        Queue::new(Some(&codec as &dyn StateCodec<_>), Config { seg_bytes: 8192, kinds: BlockKinds::Xor, compress_above: 0 }, 1)
            .with_spill(&sp, "queue");
    q.spill_on(true);
    let mut wr = q.writer();
    for i in 0..20_000 {
        q.push(&mut wr, Task { state: state(5, i), log: i, depth: 1 });
    }
    q.submit(0, &mut wr);
    assert!(q.spilled_segments() > 0);
    while sp.counters().blocks < q.spilled_segments() {
        std::thread::yield_now();
    }
    let file = std::fs::read_dir(sp.dir().unwrap())
        .unwrap()
        .map(|e| e.unwrap().path())
        .find(|p| p.extension().is_some_and(|e| e == "spill"))
        .unwrap();
    std::fs::OpenOptions::new().write(true).open(file).unwrap().write_all_at(&[0xA5; 64], 100).unwrap();
    q.install();
    let mut prev = q.scratch();
    let mut read = 0;
    let e = loop {
        match q.claim(0, &mut prev) {
            Ok(Some(mut r)) => {
                while q.read(&mut r, &mut prev, &mut None).is_some() {
                    read += 1;
                }
            }
            Ok(None) => panic!("no error"),
            Err(e) => break e,
        }
    };
    assert!(e.0.contains("corrupt"), "{e}");
    assert!(read > 0);
    assert_eq!(q.unclaimed(), 20_000 - read);
    assert!(q.claim(0, &mut prev).is_err());
    assert!(sp.error().is_some());
}
