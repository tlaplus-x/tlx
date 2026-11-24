use super::*;
use crate::io::SpillConfig;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn shuffle<T>(rng: &mut Rng, xs: &mut [T]) {
    for i in (1..xs.len()).rev() {
        let j = (rng.next() as usize) % (i + 1);
        xs.swap(i, j);
    }
}

#[test]
fn no_punch_recovery_bounds_dead_interval_metadata() {
    let mut peaks = Vec::new();
    for n in [2048u64, 8192] {
        let scratch = tlx_testkit::TempDir::new("sort-no-punch-dead");
        let spill = Spill::new(SpillConfig {
            mode: SpillMode::Always,
            dir: Some(scratch.child_path("spill")),
            no_punch: true,
            ..Default::default()
        });
        let gauge = Gauge::new();
        let cfg = SortConfig::for_budget(SortFormat::Bytes, 1 << 20, 1 << 20, 4096, SpillMode::Always);
        let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
        for i in 0..n / 2 {
            for pos in [i, n / 2 + i] {
                sorter.push_bytes(pos, pos, pos, &[1; 3000]).unwrap();
            }
        }
        let ext = sorter.ext_store.clone().unwrap();
        let mut peak = 0usize;
        let mut seen = 0u64;
        sorter
            .finish(|r| {
                let Record::Bytes { pos, .. } = r else { unreachable!() };
                assert_eq!(pos, seen);
                peak = peak.max(ext.dead_intervals_len());
                seen += 1;
                Ok(())
            })
            .unwrap();
        assert_eq!(seen, n);
        peaks.push(peak);
    }
    assert_eq!(peaks, vec![0, 0], "no_punch path must not retain dead intervals");
}

#[test]
fn words_in_memory_and_multipass_disk_merge() {
    let mut rng = Rng(0xDEAD_BEEF_CAFE_BABEu64);
    for w in [0usize, 1, 7, 8, 9, 64] {
        let n = 800usize;
        let mut want: Vec<(u64, u64, u64, Vec<u64>)> = Vec::with_capacity(n);
        let mut state = vec![0u64; w];
        for pos in 0..n as u64 {
            if w > 0 {
                for _ in 0..3 {
                    let k = (rng.next() as usize) % w;
                    state[k] = match rng.next() % 4 {
                        0 => 0,
                        1 => u64::MAX,
                        2 => rng.next() % 32,
                        _ => rng.next(),
                    };
                }
            }
            let log = ((pos % 4) << 48) | (pos * 3 + 7);
            let fp = rng.next();
            want.push((pos, log, fp, state.clone()));
        }
        let mut input = want.clone();
        shuffle(&mut rng, &mut input);

        for (name, cfg, mode) in [
            ("in-memory", SortConfig::for_budget(SortFormat::Words(w), usize::MAX, usize::MAX, 4096, SpillMode::Off), SpillMode::Off),
            (
                "forced-multipass",
                SortConfig {
                    format: SortFormat::Words(w),
                    run_limit: 2048,
                    chunk_bytes: 1024,
                    merge_budget: 2048,
                    force_spill: true,
                    can_spill: true,
                },
                SpillMode::Always,
            ),
            ("auto-tight", SortConfig::for_budget(SortFormat::Words(w), 1 << 20, 0, 4096, SpillMode::Auto), SpillMode::Auto),
        ] {
            let scratch = tlx_testkit::TempDir::new(&format!("sort-words-{name}-w{w}"));
            let dir = scratch.child_path("spill");
            let spill = Spill::new(SpillConfig { mode, dir: Some(dir), ..Default::default() });
            let gauge = Gauge::new();
            let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
            for &(pos, log, fp, ref words) in &input {
                sorter.push_words(pos, log, fp, words).unwrap();
            }
            let mut got = Vec::with_capacity(n);
            sorter
                .finish(|rec| {
                    let Record::Words { pos, log, fp, words } = rec else { unreachable!() };
                    got.push((pos, log, fp, words.to_vec()));
                    Ok(())
                })
                .unwrap();
            assert_eq!(got, want, "{name} w={w}");
            assert_eq!(gauge.bytes(), 0, "{name} w={w}: gauge leaked");
            assert_eq!(spill.counters().used, 0, "{name} w={w}: disk leaked");
            if mode == SpillMode::Off {
                assert_eq!(spill.counters().written, 0, "{name} w={w}: spilled when off");
            }
            if name == "forced-multipass" {
                assert!(spill.counters().written > 0, "expected spilled runs");
                assert!(gauge.peak() < 64 << 10, "peak {} too high", gauge.peak());
            }
        }
    }
}

#[test]
fn bytes_in_memory_and_multipass_disk_merge() {
    let mut rng = Rng(0x1234_5678_9ABC_DEF0u64);
    let n = 600usize;
    let mut want: Vec<(u64, u64, u64, Vec<u8>)> = (0..n as u64)
        .map(|pos| {
            let len = (rng.next() % 120) as usize;
            let payload: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
            (pos, pos * 5 + 1, rng.next(), payload)
        })
        .collect();
    want.push((n as u64, 99999, 0xABCD, vec![0x5Au8; 6000]));
    let mut input = want.clone();
    shuffle(&mut rng, &mut input);

    for (name, cfg, mode) in [
        ("in-memory", SortConfig::for_budget(SortFormat::Bytes, usize::MAX, usize::MAX, 4096, SpillMode::Off), SpillMode::Off),
        (
            "forced-multipass",
            SortConfig {
                format: SortFormat::Bytes,
                run_limit: 2048,
                chunk_bytes: 1024,
                merge_budget: 2048,
                force_spill: true,
                can_spill: true,
            },
            SpillMode::Always,
        ),
    ] {
        let scratch = tlx_testkit::TempDir::new(&format!("sort-bytes-{name}"));
        let dir = scratch.child_path("spill");
        let spill = Spill::new(SpillConfig { mode, dir: Some(dir), ..Default::default() });
        let gauge = Gauge::new();
        let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
        for &(pos, log, fp, ref payload) in &input {
            sorter.push_bytes(pos, log, fp, payload).unwrap();
        }
        let mut got = Vec::with_capacity(want.len());
        sorter
            .finish(|rec| {
                let Record::Bytes { pos, log, fp, payload } = rec else { unreachable!() };
                got.push((pos, log, fp, payload.to_vec()));
                Ok(())
            })
            .unwrap();
        assert_eq!(got, want, "{name}");
        assert_eq!(gauge.bytes(), 0, "{name}: gauge leaked");
        assert_eq!(spill.counters().used, 0, "{name}: disk leaked");
    }
}

/// Regression for oversized serialized payloads across multiple runs:
/// fifteen 1 MiB payloads under a 1 MiB merge budget (with `SpillMode::Always`
/// and with `SpillMode::Auto`) must keep peak memory near a single payload
/// rather than loading one 1 MiB block per run simultaneously.
#[test]
fn oversized_records_across_multiple_runs_stay_within_budget() {
    const PAYLOAD_BYTES: usize = 1 << 20;
    const COUNT: usize = 15;
    let mut rng = Rng(0xFACE_B00C_1234_5678u64);
    let mut order: Vec<u64> = (0..COUNT as u64).collect();
    shuffle(&mut rng, &mut order);

    for (label, mode, run_limit) in [
        ("always-multi-run", SpillMode::Always, 4096),
        ("always-1mib", SpillMode::Always, PAYLOAD_BYTES),
        ("auto-1mib", SpillMode::Auto, PAYLOAD_BYTES),
    ] {
        let scratch = tlx_testkit::TempDir::new(&format!("sort-oversized-{label}"));
        let dir = scratch.child_path("spill");
        let spill = Spill::new(SpillConfig { mode, dir: Some(dir), ..Default::default() });
        let gauge = Gauge::new();
        let cfg = SortConfig {
            format: SortFormat::Bytes,
            run_limit,
            chunk_bytes: 64 << 10,
            merge_budget: PAYLOAD_BYTES,
            force_spill: mode == SpillMode::Always,
            can_spill: true,
        };
        let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
        let mut payload = vec![0u8; PAYLOAD_BYTES];
        for &pos in &order {
            payload.fill((pos as u8).wrapping_mul(17).wrapping_add(3));
            payload[..8].copy_from_slice(&pos.to_le_bytes());
            sorter.push_bytes(pos, pos * 11, pos ^ 0xA5A5_5A5A, &payload).unwrap();
        }
        let mut seen = 0u64;
        sorter
            .finish(|rec| {
                let Record::Bytes { pos, log, fp, payload } = rec else { unreachable!() };
                assert_eq!(pos, seen, "{label}: out of order");
                assert_eq!(log, pos * 11);
                assert_eq!(fp, pos ^ 0xA5A5_5A5A);
                assert_eq!(payload.len(), PAYLOAD_BYTES);
                assert_eq!(u64::from_le_bytes(payload[..8].try_into().unwrap()), pos);
                assert_eq!(payload[PAYLOAD_BYTES - 1], (pos as u8).wrapping_mul(17).wrapping_add(3));
                seen += 1;
                Ok(())
            })
            .unwrap();
        assert_eq!(seen, COUNT as u64);
        assert_eq!(gauge.bytes(), 0, "{label}: gauge leaked");
        assert_eq!(spill.counters().used, 0, "{label}: disk leaked");
        // Peak memory must stay bounded near a single 1 MiB payload plus
        // small run/index buffers, never `COUNT * 1 MiB` (15 MiB).
        assert!(gauge.peak() < (2 << 20), "{label}: peak {} bytes exceeded 2 MiB for {COUNT}x1 MiB payloads", gauge.peak());
    }

    // Also verify oversized `Words` records select merge batches using
    // actual maximum block sizes rather than the target chunk size.
    let w = 2048usize; // 16 KiB raw per state
    let mut worder: Vec<u64> = (0..16u64).collect();
    shuffle(&mut rng, &mut worder);
    let scratch = tlx_testkit::TempDir::new("sort-oversized-words");
    let dir = scratch.child_path("spill");
    let spill = Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir), ..Default::default() });
    let gauge = Gauge::new();
    let cfg = SortConfig {
        format: SortFormat::Words(w),
        run_limit: 4096,
        chunk_bytes: 4096,
        merge_budget: 64 << 10,
        force_spill: true,
        can_spill: true,
    };
    let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
    let mut words = vec![0u64; w];
    for &pos in &worder {
        for (i, slot) in words.iter_mut().enumerate() {
            *slot = (pos + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        }
        sorter.push_words(pos, pos, pos * 3, &words).unwrap();
    }
    let mut seen = 0u64;
    sorter
        .finish(|rec| {
            let Record::Words { pos, log, fp, words } = rec else { unreachable!() };
            assert_eq!((pos, log, fp), (seen, seen, seen * 3));
            assert_eq!(words[0], (pos + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            seen += 1;
            Ok(())
        })
        .unwrap();
    assert_eq!(seen, 16);
    assert_eq!(gauge.bytes(), 0);
    assert_eq!(spill.counters().used, 0);
    // Opening all 16 oversized ~20 KiB blocks at once would exceed 320 KiB;
    // actual-block-size batch selection keeps peak well below that.
    assert!(gauge.peak() < 160 << 10, "words oversized peak {} bytes too high", gauge.peak());
}

/// Total OS-allocated disk bytes across all live `*.spill` files in `dir`.
fn allocated_spill_bytes(dir: &std::path::Path) -> u64 {
    use std::os::unix::fs::MetadataExt;
    let Ok(rd) = std::fs::read_dir(dir) else {
        return 0;
    };
    let mut total = 0u64;
    for entry in rd.flatten() {
        let path = entry.path();
        if path.extension().is_some_and(|e| e == "spill") {
            if let Ok(meta) = std::fs::metadata(&path) {
                total = total.saturating_add(meta.blocks().saturating_mul(512));
            }
        }
    }
    total
}

/// Probe whether the temporary filesystem supports page-level hole punching.
fn fs_supports_punch() -> bool {
    let scratch = tlx_testkit::TempDir::new("sort-punch-probe");
    let dir = scratch.child_path("spill");
    let spill = Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir), ..Default::default() });
    let Ok(store) = spill.store("punch-probe") else {
        return false;
    };
    let Ok(b) = store.append(&vec![0xA5u8; PAGE]) else {
        return false;
    };
    // Keep a second block live so `delete_reclaimable(b)` exercises
    // page-level hole punching rather than empty-store truncation.
    if store.append(&vec![0x5Au8; PAGE]).is_err() {
        return false;
    }
    store.delete_reclaimable(b);
    store.bytes() == PAGE as u64
}

/// Regression for height-two+ on-disk block trees: popping an exhausted
/// root before descending into its final child must preserve logical tree
/// depth so every leaf block through the very last record is drained cleanly,
/// under both hole-punching and unlink-on-drop reclamation modes.
#[test]
fn block_tree_height_two_drains_through_last_leaf() {
    for no_punch in [false, true] {
        let tag = if no_punch { "sort-tree-nopunch" } else { "sort-tree-punch" };
        let scratch = tlx_testkit::TempDir::new(tag);
        let dir = scratch.child_path("spill");
        let spill = Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir.clone()), no_punch, ..Default::default() });
        let store = spill.store("tree-test").unwrap();
        // 4 KiB index blocks hold ~170 24-byte BlockRefs; 400 data blocks forces
        // height == 2 (3 level-1 index blocks under 1 level-2 root).
        let total_blocks = 400u64;
        let mut writer = BlockTreeWriter::new(store.clone(), 4096);
        let mut page = vec![0u8; PAGE];
        for i in 0..total_blocks {
            page[..8].copy_from_slice(&i.to_le_bytes());
            let b = store.append(&page).unwrap();
            writer.push_data_block(b).unwrap();
        }
        let tree = writer.finish().unwrap().expect("non-empty tree");
        assert_eq!(tree.height, 2, "expected height-2 block tree");
        let total_written = spill.counters().written;
        let mut reader = BlockTreeReader::open(&store, tree).unwrap();
        let mut got = 0u64;
        while let Some(b) = reader.next_block(&store).unwrap() {
            let data = store.read(&b).unwrap();
            assert_eq!(u64::from_le_bytes(data[..8].try_into().unwrap()), got);
            store.delete_reclaimable(b);
            got += 1;
        }
        assert_eq!(got, total_blocks);
        if !no_punch {
            // Only the small conservative extent-metadata reserve may stay
            // charged while the sparse file still exists before unlink;
            // once drained, final truncation reclaims even without punch.
            assert!(
                spill.counters().used <= (8 * PAGE) as u64,
                "expected punched blocks reclaimed before drop, got {} bytes (of {total_written})",
                spill.counters().used
            );
            assert!(
                allocated_spill_bytes(&dir) <= (4 * PAGE) as u64,
                "expected punched blocks freed on disk, got {}",
                allocated_spill_bytes(&dir)
            );
        } else {
            // Explicit unlink-only mode: all data and index blocks stay
            // honestly charged until the store is dropped and unlinked.
            assert_eq!(spill.counters().used, total_written, "un-punched blocks must remain charged until unlink");
        }
        drop(store);
        assert_eq!(spill.counters().used, 0, "all bytes must be credited on unlink (no_punch={no_punch})");
        assert_eq!(allocated_spill_bytes(&dir), 0, "all disk blocks must be freed on unlink (no_punch={no_punch})");
    }
}

/// Regression for bounded run metadata, non-quadratic rewrites, and real
/// allocated disk space under `-maxdisk`:
/// scaling the input size 1x -> 4x -> 16x -> 64x (up to 32,000 records,
/// exercising height-two block trees through their final leaves) under a
/// fixed tiny budget (4 KiB chunks) must keep peak gauge memory roughly
/// constant, bytes written per record logarithmic, and actual allocated
/// filesystem blocks (`st_blocks * 512`) sampled during compaction and
/// final merge strictly within `-maxdisk` (4 MiB when hole punching is
/// available; 8 MiB with unlink-on-drop fallback).
#[test]
fn scaling_level_size_at_fixed_budget_bounds_metadata_and_rewrites() {
    let fs_punches = fs_supports_punch();
    let disk_limit: u64 = if fs_punches { 4 << 20 } else { 8 << 20 };
    let mut rng = Rng(0xCAFE_1234_5678_9ABCu64);
    let sizes = [500usize, 2_000, 8_000, 32_000];
    let mut peaks = Vec::new();
    let mut written_per_rec = Vec::new();

    for &n in &sizes {
        let scratch = tlx_testkit::TempDir::new(&format!("sort-scale-n{n}"));
        let dir = scratch.child_path("spill");
        let spill =
            Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir.clone()), maxdisk: Some(disk_limit), ..Default::default() });
        let gauge = Gauge::new();
        let cfg = SortConfig {
            format: SortFormat::Bytes,
            run_limit: 4096,
            chunk_bytes: 4096,
            merge_budget: 16 << 10,
            force_spill: true,
            can_spill: true,
        };
        let mut order: Vec<u64> = (0..n as u64).collect();
        shuffle(&mut rng, &mut order);

        let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
        let mut payload = [0u8; 96];
        let mut peak_alloc_ingest = 0u64;
        for (idx, &pos) in order.iter().enumerate() {
            payload[..8].copy_from_slice(&pos.to_le_bytes());
            payload[8..16].copy_from_slice(&pos.wrapping_mul(31).to_le_bytes());
            sorter.push_bytes(pos, pos * 7, pos ^ 0x55AA, &payload).unwrap();
            if idx % 256 == 255 {
                peak_alloc_ingest = peak_alloc_ingest.max(allocated_spill_bytes(&dir));
            }
        }
        let pre_merge_alloc = allocated_spill_bytes(&dir);
        peak_alloc_ingest = peak_alloc_ingest.max(pre_merge_alloc);

        let mut seen = 0u64;
        let mut peak_alloc_merge = pre_merge_alloc;
        sorter
            .finish(|rec| {
                let Record::Bytes { pos, log, fp, payload } = rec else { unreachable!() };
                assert_eq!((pos, log, fp), (seen, seen * 7, seen ^ 0x55AA));
                assert_eq!(u64::from_le_bytes(payload[..8].try_into().unwrap()), pos);
                seen += 1;
                if seen.is_multiple_of(256) {
                    peak_alloc_merge = peak_alloc_merge.max(allocated_spill_bytes(&dir));
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(seen, n as u64);
        assert_eq!(gauge.bytes(), 0);
        assert_eq!(spill.counters().used, 0);
        assert_eq!(allocated_spill_bytes(&dir), 0, "n={n}: spill files left allocated after finish");
        let peak_alloc = peak_alloc_ingest.max(peak_alloc_merge);
        assert!(spill.counters().peak <= disk_limit, "n={n}: counter peak {} exceeded -maxdisk {disk_limit}", spill.counters().peak);
        assert!(
            peak_alloc <= disk_limit,
            "n={n}: allocated disk peak {peak_alloc} (pre-merge {pre_merge_alloc}) exceeded -maxdisk {disk_limit}"
        );
        if n == 32_000 {
            assert!(pre_merge_alloc > (2 << 20), "expected live spill files before final merge, got {pre_merge_alloc}");
        }
        peaks.push(gauge.peak());
        written_per_rec.push(spill.counters().written as f64 / n as f64);
    }

    // Across a 64x increase in total data under a fixed 16 KiB merge budget,
    // peak gauge memory stays tightly bounded (no linear growth of BlockRef
    // arrays in RAM).
    assert!(peaks[3] < 64 << 10, "peak memory grew with level size: {peaks:?}");
    // Bytes written per record grows logarithmically with N, nowhere near
    // the ~64x jump of an O(N^2) rewrite loop.
    assert!(written_per_rec[3] < written_per_rec[0] * 3.5, "rewrite amplification grew super-logarithmically: {written_per_rec:?}");
}

/// Regression for the `punch_hole == false` fallback path: without mid-run
/// hole punching, a 4 MiB quota must reject the 32,000-record merge before
/// physical allocation exceeds 4 MiB and clean up to 0 bytes, while an
/// 8 MiB quota succeeds by unlinking consumed run files between merges.
#[test]
fn scaling_without_hole_punch_enforces_quota_and_reclaims_on_unlink() {
    let mut rng = Rng(0xBADC_0FFE_E123_4567u64);
    let n = 32_000usize;
    let mut order: Vec<u64> = (0..n as u64).collect();
    shuffle(&mut rng, &mut order);
    let cfg = SortConfig {
        format: SortFormat::Bytes,
        run_limit: 4096,
        chunk_bytes: 4096,
        merge_budget: 16 << 10,
        force_spill: true,
        can_spill: true,
    };

    // 1. Tight 4 MiB quota without hole punching: must fail cleanly with
    //    `-maxdisk` before allocated bytes exceed 4 MiB and free everything.
    let tight: u64 = 4 << 20;
    let scratch_tight = tlx_testkit::TempDir::new("sort-nopunch-tight");
    let dir_tight = scratch_tight.child_path("spill");
    let spill_tight = Spill::new(SpillConfig {
        mode: SpillMode::Always,
        dir: Some(dir_tight.clone()),
        maxdisk: Some(tight),
        no_punch: true,
        ..Default::default()
    });
    let gauge_tight = Gauge::new();
    let mut sorter = QueueSorter::new(cfg, &spill_tight, &gauge_tight);
    let mut payload = [0u8; 96];
    let mut peak_alloc = 0u64;
    let mut err = None;
    for (idx, &pos) in order.iter().enumerate() {
        payload[..8].copy_from_slice(&pos.to_le_bytes());
        if let Err(e) = sorter.push_bytes(pos, pos * 7, pos ^ 0x55AA, &payload) {
            err = Some(e);
            break;
        }
        if idx % 256 == 255 {
            peak_alloc = peak_alloc.max(allocated_spill_bytes(&dir_tight));
        }
    }
    let err = err.or_else(|| {
        sorter
            .finish(|_| {
                peak_alloc = peak_alloc.max(allocated_spill_bytes(&dir_tight));
                Ok(())
            })
            .err()
    });
    assert!(err.as_deref().is_some_and(|e| e.contains("-maxdisk")), "expected -maxdisk rejection without hole punching, got {err:?}");
    assert!(peak_alloc <= tight, "allocated disk {peak_alloc} exceeded {tight} before rejection");
    assert!(spill_tight.counters().peak <= tight);
    assert_eq!(gauge_tight.bytes(), 0);
    assert_eq!(spill_tight.counters().used, 0);
    assert_eq!(allocated_spill_bytes(&dir_tight), 0, "spill files leaked after no-punch -maxdisk error");

    // 2. 8 MiB quota without hole punching: unlinking consumed run files
    //    keeps allocated disk space <= 8 MiB (far below the 30.9 MiB
    //    monotonic growth bug) and frees everything on completion.
    let roomy: u64 = 8 << 20;
    let scratch_roomy = tlx_testkit::TempDir::new("sort-nopunch-roomy");
    let dir_roomy = scratch_roomy.child_path("spill");
    let spill_roomy = Spill::new(SpillConfig {
        mode: SpillMode::Always,
        dir: Some(dir_roomy.clone()),
        maxdisk: Some(roomy),
        no_punch: true,
        ..Default::default()
    });
    let gauge_roomy = Gauge::new();
    let mut sorter = QueueSorter::new(cfg, &spill_roomy, &gauge_roomy);
    let mut peak_alloc = 0u64;
    for (idx, &pos) in order.iter().enumerate() {
        payload[..8].copy_from_slice(&pos.to_le_bytes());
        sorter.push_bytes(pos, pos * 7, pos ^ 0x55AA, &payload).unwrap();
        if idx % 256 == 255 {
            peak_alloc = peak_alloc.max(allocated_spill_bytes(&dir_roomy));
        }
    }
    let pre_merge = allocated_spill_bytes(&dir_roomy);
    peak_alloc = peak_alloc.max(pre_merge);
    let mut seen = 0u64;
    sorter
        .finish(|rec| {
            let Record::Bytes { pos, log, fp, payload } = rec else { unreachable!() };
            assert_eq!((pos, log, fp), (seen, seen * 7, seen ^ 0x55AA));
            assert_eq!(u64::from_le_bytes(payload[..8].try_into().unwrap()), pos);
            seen += 1;
            if seen.is_multiple_of(256) {
                peak_alloc = peak_alloc.max(allocated_spill_bytes(&dir_roomy));
            }
            Ok(())
        })
        .unwrap();
    assert_eq!(seen, n as u64);
    assert!(pre_merge > (2 << 20), "expected live spill files before final merge, got {pre_merge}");
    assert!(peak_alloc <= roomy, "no-punch allocated disk {peak_alloc} exceeded {roomy}");
    assert!(spill_roomy.counters().peak <= roomy);
    assert_eq!(gauge_roomy.bytes(), 0);
    assert_eq!(spill_roomy.counters().used, 0);
    assert_eq!(allocated_spill_bytes(&dir_roomy), 0, "spill files leaked after no-punch finish");
}

#[test]
fn maxdisk_quota_bounds_allocated_bytes_and_cleans_up_on_error() {
    const DISK_LIMIT: u64 = 1 << 20;
    let scratch = tlx_testkit::TempDir::new("sort-maxdisk-quota");
    let dir = scratch.child_path("spill");
    let spill =
        Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir.clone()), maxdisk: Some(DISK_LIMIT), ..Default::default() });
    let gauge = Gauge::new();
    let cfg = SortConfig {
        format: SortFormat::Bytes,
        run_limit: 4096,
        chunk_bytes: 4096,
        merge_budget: 16 << 10,
        force_spill: true,
        can_spill: true,
    };
    let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
    let payload = [0xA5u8; 96];
    let mut peak_alloc = 0u64;
    let mut err = None;
    for pos in 0..32_000u64 {
        if let Err(e) = sorter.push_bytes(pos, pos, pos, &payload) {
            err = Some(e);
            break;
        }
        if pos.is_multiple_of(128) {
            peak_alloc = peak_alloc.max(allocated_spill_bytes(&dir));
        }
    }
    let err = err.or_else(|| sorter.finish(|_| Ok(())).err());
    assert!(err.as_deref().is_some_and(|e| e.contains("-maxdisk")), "expected -maxdisk error, got {err:?}");
    assert!(peak_alloc <= DISK_LIMIT, "allocated disk {peak_alloc} exceeded -maxdisk {DISK_LIMIT}");
    assert_eq!(gauge.bytes(), 0);
    assert_eq!(spill.counters().used, 0);
    assert_eq!(allocated_spill_bytes(&dir), 0, "spill files leaked after -maxdisk error");
}

#[test]
fn io_failure_cleans_up_gauge_and_store() {
    let scratch = tlx_testkit::TempDir::new("sort-io-fail");
    let dir = scratch.child_path("spill");
    let spill = Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir), fail_after: Some(512), ..Default::default() });
    let gauge = Gauge::new();
    let cfg = SortConfig {
        format: SortFormat::Words(4),
        run_limit: 1024,
        chunk_bytes: 512,
        merge_budget: 2048,
        force_spill: true,
        can_spill: true,
    };
    let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
    let mut err = None;
    for pos in 0..200u64 {
        if let Err(e) = sorter.push_words(pos, pos, pos * 7, &[pos, pos + 1, pos + 2, pos + 3]) {
            err = Some(e);
            break;
        }
    }
    let err = err.or_else(|| sorter.finish(|_| Ok(())).err());
    assert!(err.is_some_and(|e| e.contains("fail_after")), "expected injected IO error");
    assert_eq!(gauge.bytes(), 0, "gauge must return to zero on error");
    assert_eq!(spill.counters().used, 0, "disk accounting must return to zero on error");
}

#[test]
fn empty_and_just_flushed_sorters_finish_cleanly() {
    let scratch = tlx_testkit::TempDir::new("sort-empty-flushed");
    let spill = Spill::new(SpillConfig { mode: SpillMode::Auto, dir: Some(scratch.child_path("spill")), ..Default::default() });
    let gauge = Gauge::new();
    let cfg = SortConfig::for_budget(SortFormat::Words(2), 1 << 20, 1 << 20, 4096, SpillMode::Auto);
    QueueSorter::new(cfg, &spill, &gauge).finish(|_| panic!("unexpected record")).unwrap();
    assert_eq!(gauge.bytes(), 0);

    let mut sorter = QueueSorter::new(cfg, &spill, &gauge);
    sorter.push_words(1, 10, 100, &[1, 2]).unwrap();
    sorter.push_words(0, 20, 200, &[3, 4]).unwrap();
    sorter.refresh_budget(1 << 20, 0, 4096).unwrap();
    sorter.flush_run().unwrap();
    assert!(sorter.entries.is_empty() && !sorter.runs.is_empty());
    let mut got = Vec::new();
    sorter
        .finish(|rec| {
            let Record::Words { pos, log, .. } = rec else { unreachable!() };
            got.push((pos, log));
            Ok(())
        })
        .unwrap();
    assert_eq!(got, vec![(0, 20), (1, 10)]);
    assert_eq!(gauge.bytes(), 0);
    assert_eq!(spill.counters().used, 0);
}
