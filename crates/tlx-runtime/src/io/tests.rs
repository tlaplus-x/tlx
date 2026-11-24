use super::*;

fn spill_in(dir: &Path) -> Spill {
    Spill::new(SpillConfig { dir: Some(dir.to_path_buf()), ..Default::default() })
}

fn data(n: usize, seed: u64) -> Vec<u8> {
    (0..n).map(|i| ((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(seed) >> 29) as u8).collect()
}

#[test]
fn store_round_trip() {
    let scratch = tlx_testkit::TempDir::new("io-store");
    let dir = scratch.child_path("spill");
    let spill = spill_in(&dir);
    let store = spill.store("blocks").unwrap();
    let blocks: Vec<Vec<u8>> = [0, 1, 4095, 4096, 4097, 100_000].iter().enumerate().map(|(k, &n)| data(n, k as u64)).collect();
    let refs: Vec<BlockRef> = blocks.iter().map(|b| store.append(b).unwrap()).collect();
    for (b, r) in blocks.iter().zip(&refs) {
        assert_eq!(&store.read(r).unwrap(), b);
        // Ranges across page boundaries.
        for (at, len) in [(0, 1), (4090, 12), (5000, 3000)] {
            if at + len <= b.len() {
                let mut out = vec![0; len];
                store.read_range(r, at, &mut out).unwrap();
                assert_eq!(&out, &b[at..at + len]);
            }
        }
    }
    let c = spill.counters();
    assert_eq!(c.used, blocks.iter().map(|b| b.len() as u64).sum::<u64>());
    assert_eq!(c.blocks, blocks.len() as u64);
    store.delete(refs[5].clone());
    assert_eq!(spill.counters().used, c.used - 100_000);
    assert!(spill.error().is_none());
    // The directory did not exist: tlx creates it and removes it with
    // the last store, while the RAII parent stays alive.
    assert!(dir.join("LOCK").exists());
    drop(store);
    assert!(!dir.exists());
    assert!(scratch.is_dir(), "tlx removes the spill child before its RAII parent is dropped");
}

#[test]
fn panic_removes_owned_spill_resources() {
    let scratch = tlx_testkit::TempDir::new("io-panic");
    let parent = scratch.path().to_path_buf();
    let result = std::panic::catch_unwind(move || {
        let dir = scratch.child_path("spill");
        let spill = spill_in(&dir);
        let store = spill.store("blocks").unwrap();
        store.append(b"written before panic").unwrap();
        assert!(dir.join("LOCK").is_file());
        panic!("intentional panic after creating spill resources");
    });
    assert!(result.is_err());
    assert!(!parent.exists(), "the owned parent and spill child survived unwinding");
}

#[test]
fn checksum_detects_corruption() {
    let scratch = tlx_testkit::TempDir::new("io-corrupt");
    let dir = scratch.child_path("spill");
    let spill = spill_in(&dir);
    let store = spill.store("blocks").unwrap();
    let b = data(10_000, 7);
    let r = store.append(&b).unwrap();
    // Flip a byte of the second page behind the store's back.
    let f = OpenOptions::new().write(true).open(store.path()).unwrap();
    f.write_all_at(&[b[5000] ^ 0x40], r.off + 5000).unwrap();
    let e = store.read(&r).unwrap_err();
    assert!(e.0.contains("checksum mismatch at offset 4096"), "{e}");
    // The first page is still fine on its own.
    let mut out = [0u8; 16];
    store.read_range(&r, 100, &mut out).unwrap();
    assert_eq!(spill.error(), Some(e));
}

use std::fs::OpenOptions;
use std::os::unix::fs::FileExt;

#[test]
fn maxdisk_quota() {
    let scratch = tlx_testkit::TempDir::new("io-quota");
    let dir = scratch.child_path("spill");
    let spill = Spill::new(SpillConfig { dir: Some(dir.clone()), maxdisk: Some(64 << 10), ..Default::default() });
    let store = spill.store("blocks").unwrap();
    // 60 KiB of data + 4 KiB conservative extent-tree reserve fits in 64 KiB.
    for k in 0..3 {
        store.append(&data(16 << 10, k)).unwrap();
    }
    store.append(&data(12 << 10, 3)).unwrap();
    let e = store.append(&[0u8; 1]).unwrap_err();
    assert!(e.0.contains("-maxdisk 64 KiB") && e.0.contains(&dir.display().to_string()), "{e}");
    assert!(spill.failed());
    // Zero-byte append needs no new allocation unit.
    let r = store.append(&[]).unwrap();
    store.delete(r);
}

#[test]
fn interleaved_paged_appends_respect_physical_maxdisk() {
    use std::os::unix::fs::MetadataExt;
    let scratch = tlx_testkit::TempDir::new("io-fragmented-appends");
    let limit = 260 * 1024;
    let spill = Spill::new(SpillConfig { dir: Some(scratch.child_path("spill")), maxdisk: Some(limit), ..Default::default() });
    let stores: Vec<_> = (0..16).map(|_| spill.store("recover-run").unwrap()).collect();
    for index in 0..65 {
        let store = &stores[index % 16];
        if store.append(&[3; PAGE]).is_err() {
            break;
        }
        File::open(store.path()).unwrap().sync_all().unwrap();
        let physical = stores.iter().map(|s| std::fs::metadata(s.path()).unwrap().blocks() * 512).sum::<u64>();
        assert!(physical <= limit, "append {}, quota {limit}, charged {}, allocated {physical}", index + 1, spill.counters().used);
    }
    drop(stores);
    assert_eq!(spill.counters().used, 0);
}

#[test]
fn mixed_store_subpage_tail_respects_physical_maxdisk() {
    use std::os::unix::fs::MetadataExt;
    for (limit, run_len) in [(17 << 10, 16 << 10), (parse_size("1025K").unwrap(), 1000 << 10)] {
        let scratch = tlx_testkit::TempDir::new("io-page-tail");
        let spill = Spill::new(SpillConfig { dir: Some(scratch.child_path("spill")), maxdisk: Some(limit), ..Default::default() });
        let run = spill.store("recover-run").unwrap();
        let queue = spill.store("queue").unwrap();
        run.append(&vec![17; run_len]).unwrap();
        let res = queue.append(&[3; 1024]);
        assert!(res.is_err(), "1 KiB append into a new store allocates a full 4 KiB page and must not exceed {limit}");
        let physical = [&run, &queue]
            .iter()
            .map(|s| {
                let file = File::open(s.path()).unwrap();
                file.sync_all().unwrap();
                file.metadata().unwrap().blocks() * 512
            })
            .sum::<u64>();
        assert!(physical <= limit, "quota {limit}, charged {}, allocated {physical}", spill.counters().used);
        drop((run, queue));
        assert_eq!(spill.counters().used, 0);
    }
}

#[test]
fn fragmented_extents_respect_physical_maxdisk_after_sync() {
    use std::os::unix::fs::MetadataExt;
    const LIMIT: u64 = 8 << 20;
    let scratch = tlx_testkit::TempDir::new("io-frag-quota");
    let dir = scratch.child_path("spill");
    let spill = Spill::new(SpillConfig { dir: Some(dir.clone()), maxdisk: Some(LIMIT), ..Default::default() });
    let s1 = spill.store("ext").unwrap();
    let payload = vec![0x5Au8; 3000];
    let mut refs = Vec::with_capacity(2048);
    for _ in 0..2048 {
        match s1.append_paged(&(payload.len() as u64).to_le_bytes(), &payload) {
            Ok(r) => refs.push(r),
            Err(e) => {
                assert!(e.0.contains("-maxdisk"), "unexpected error: {e}");
                break;
            }
        }
    }
    assert!(refs.len() >= 1900, "expected most of 8 MiB admitted before extent reserve, got {}", refs.len());
    // Punch alternating pages to maximize filesystem extent fragmentation.
    for (i, r) in refs.into_iter().enumerate() {
        if i % 2 == 0 {
            s1.delete_reclaimable(r);
        }
    }
    let s2 = spill.store("run").unwrap();
    let page = vec![0xA5u8; PAGE];
    let mut hit_quota = false;
    for _ in 0..1024 {
        if let Err(e) = s2.append(&page) {
            assert!(e.0.contains("-maxdisk"), "unexpected error: {e}");
            hit_quota = true;
            break;
        }
    }
    // Sync both live spill files so delayed allocation materializes extent
    // metadata blocks before measuring physical disk occupancy.
    File::open(s1.path()).unwrap().sync_all().unwrap();
    File::open(s2.path()).unwrap().sync_all().unwrap();
    let allocated = std::fs::metadata(s1.path()).unwrap().blocks() * 512 + std::fs::metadata(s2.path()).unwrap().blocks() * 512;
    assert!(hit_quota, "expected conservative extent-metadata accounting to enforce -maxdisk before 1024 pages");
    assert!(spill.counters().used <= LIMIT, "logical used {} exceeded {LIMIT}", spill.counters().used);
    assert!(spill.counters().peak <= LIMIT, "logical peak {} exceeded {LIMIT}", spill.counters().peak);
    assert!(allocated <= LIMIT, "physical st_blocks*512 ({allocated}) exceeded -maxdisk {LIMIT}");
    drop((s1, s2));
    assert_eq!(spill.counters().used, 0);
    assert!(!dir.exists());
}

#[test]
#[cfg(target_os = "linux")]
fn drained_reused_queue_store_reclaims_quota_over_lifetime() {
    use std::os::unix::fs::MetadataExt;
    let scratch = tlx_testkit::TempDir::new("io-reuse-pages");
    let limit = 64 << 10;
    let spill = Spill::new(SpillConfig { dir: Some(scratch.child_path("spill")), maxdisk: Some(limit), ..Default::default() });
    let queue = spill.store("queue").unwrap();
    let file = File::open(queue.path()).unwrap();
    let first = queue.append(&[3; PAGE]).unwrap();
    queue.delete(first);
    file.sync_all().unwrap();
    if file.metadata().unwrap().blocks() != 0 {
        return; // Filesystem does not reclaim punched pages.
    }
    for i in 1..2048 {
        let block = queue.append(&[3; PAGE]).unwrap_or_else(|err| {
            file.sync_all().unwrap();
            panic!("append {}, physical {}, logical {}, {err}", i + 1, file.metadata().unwrap().blocks() * 512, spill.counters().used);
        });
        queue.delete(block);
    }
    drop(queue);
    assert_eq!(spill.counters().used, 0);
}

#[test]
#[cfg(target_os = "linux")]
fn large_paged_appends_account_for_multi_extent_metadata() {
    use std::os::unix::fs::MetadataExt;
    let scratch = tlx_testkit::TempDir::new("io-large-extents");
    const BLOCK: usize = 129 << 20;
    let limit = (4 * BLOCK) as u64;
    let spill = Spill::new(SpillConfig { dir: Some(scratch.child_path("spill")), maxdisk: Some(limit), ..Default::default() });
    let external = spill.store("recover-external").unwrap();
    let payload = vec![17; BLOCK - 8];
    let header = (payload.len() as u64).to_le_bytes();
    for _ in 0..4 {
        if let Err(err) = external.append_paged(&header, &payload) {
            assert!(err.0.contains("-maxdisk"), "unexpected error: {err}");
            break;
        }
    }
    let file = File::open(external.path()).unwrap();
    file.sync_all().unwrap();
    let physical = file.metadata().unwrap().blocks() * 512;
    assert!(physical <= limit, "physical {physical}, quota {limit}, logical {}", spill.counters().used);
    drop(external);
    assert_eq!(spill.counters().used, 0);
}

#[test]
#[cfg(target_os = "linux")]
fn small_fragmented_paged_writes_respect_physical_maxdisk() {
    use std::os::unix::fs::MetadataExt;
    const BLOCK: usize = 8192;
    const LIMIT: u64 = (3 * BLOCK) as u64;
    let scratch = tlx_testkit::TempDir::new("io-small-frag");
    let dir = scratch.child_path("spill");
    let spill = Spill::new(SpillConfig { dir: Some(dir.clone()), maxdisk: Some(LIMIT), ..Default::default() });
    let target = spill.store("recover-ext").unwrap();
    let f = File::open(target.path()).unwrap();
    let competing = File::create(dir.join("competing-file")).unwrap();
    let mut peak = 0u64;
    for _ in 0..3 {
        let res = target.append_paged_hook(&[1; 8], &[7; BLOCK - 8], || {
            f.sync_all().unwrap();
            peak = peak.max(f.metadata().unwrap().blocks() * 512);
            competing.write_all_at(&[1; PAGE], competing.metadata().unwrap().len()).unwrap();
            competing.sync_all().unwrap();
        });
        if let Err(e) = res {
            assert!(e.0.contains("-maxdisk"), "unexpected error: {e}");
            break;
        }
        f.sync_all().unwrap();
        peak = peak.max(f.metadata().unwrap().blocks() * 512);
        competing.write_all_at(&[1; PAGE], competing.metadata().unwrap().len()).unwrap();
        competing.sync_all().unwrap();
    }
    let actual = f.metadata().unwrap().blocks() * 512;
    assert!(peak <= LIMIT, "in-flight peak {peak} exceeded quota {LIMIT}");
    assert!(actual <= LIMIT, "spill file {actual}, quota {LIMIT}, logical {}", target.bytes());
    drop(target);
    assert_eq!(spill.counters().used, 0);
}

#[test]
#[cfg(target_os = "linux")]
fn fragmented_writes_respect_inflight_peak_and_unlistable_metadir() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    for listable in [true, false] {
        let scratch = tlx_testkit::TempDir::new("io-inflight-quota");
        let dir = scratch.child_path("spill");
        let limit = 5 * PAGE as u64;
        let spill = Spill::new(SpillConfig { dir: Some(dir.clone()), maxdisk: Some(limit), ..Default::default() });
        let store = spill.store("recover-run").unwrap();
        let file = File::open(store.path()).unwrap();
        let neighbor = File::create(dir.join("competing-file")).unwrap();
        let saved = std::fs::metadata(&dir).unwrap().permissions();
        if !listable {
            std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o300)).unwrap();
        }
        let mut peak = 0u64;
        for _ in 0..5 {
            let res = store.append_paged_hook(&[7; PAGE], &[], || {
                file.sync_all().unwrap();
                peak = peak.max(file.metadata().unwrap().blocks() * 512);
                neighbor.write_all_at(&[1; PAGE], neighbor.metadata().unwrap().len()).unwrap();
                neighbor.sync_all().unwrap();
            });
            if let Err(e) = res {
                assert!(e.0.contains("-maxdisk"), "unexpected error: {e}");
                break;
            }
        }
        std::fs::set_permissions(&dir, saved).unwrap();
        file.sync_all().unwrap();
        let final_bytes = file.metadata().unwrap().blocks() * 512;
        assert!(peak <= limit, "listable={listable}: in-flight peak {peak} exceeded quota {limit}");
        assert!(final_bytes <= limit, "listable={listable}: final {final_bytes} exceeded quota {limit}");
        drop(store);
        assert_eq!(spill.counters().used, 0);
    }
}

#[test]
fn disjoint_subpage_deletes_bound_dead_intervals() {
    let scratch = tlx_testkit::TempDir::new("io-bounded-dead");
    let spill = spill_in(&scratch.child_path("spill"));
    let store = spill.store("subpage").unwrap();
    let payload = [9u8; 3000];
    let refs: Vec<_> = (0..512).map(|_| store.append(&payload).unwrap()).collect();
    for (i, r) in refs.into_iter().enumerate() {
        if i % 2 == 0 {
            store.delete(r);
        }
    }
    assert!(store.dead_intervals_len() <= 64, "unbounded dead intervals: {}", store.dead_intervals_len());
}

#[test]
fn reuse_after_disjoint_subpage_deletes_reclaims_quota() {
    use std::os::unix::fs::MetadataExt;
    let scratch = tlx_testkit::TempDir::new("io-disjoint-drain");
    let limit = 1 << 20;
    let sp = Spill::new(SpillConfig { dir: Some(scratch.child_path("spill")), maxdisk: Some(limit), ..Default::default() });
    let store = sp.store("queue").unwrap();
    let f = File::open(store.path()).unwrap();
    for cycle in 0..16 {
        let mut odd = Vec::new();
        let mut even = Vec::new();
        for i in 0..256 {
            let b = store.append(&[9; 3000]).unwrap_or_else(|e| {
                f.sync_all().unwrap();
                panic!("cycle {cycle}, block {i}, allocated {}, live {}: {e}", f.metadata().unwrap().blocks() * 512, store.bytes());
            });
            if i % 2 == 0 {
                even.push(b);
            } else {
                odd.push(b);
            }
        }
        for b in even.into_iter().chain(odd) {
            store.delete(b);
        }
        assert_eq!(store.bytes(), 0);
        f.sync_all().unwrap();
        assert_eq!(f.metadata().unwrap().blocks() * 512, 0, "cycle {cycle}: drained store retained blocks");
    }
    drop(store);
    assert_eq!(sp.counters().used, 0);
}

#[test]
#[cfg(target_os = "linux")]
fn unlink_failure_retains_physical_quota_and_surfaces_error() {
    use std::os::unix::fs::MetadataExt;
    let scratch = tlx_testkit::TempDir::new("io-unlink-fail");
    let dir = scratch.child_path("spill");
    let limit = 16 << 10;
    let sp = Spill::new(SpillConfig { dir: Some(dir.clone()), maxdisk: Some(limit), ..Default::default() });
    let run = sp.store("recover-run").unwrap();
    let dest = sp.store("queue").unwrap();
    run.append(&[7; 16 << 10]).unwrap();
    let run_path = run.path().to_owned();
    let retained = dir.join("retained.spill");
    std::fs::rename(&run_path, &retained).unwrap();
    // Replacing the path with a directory forces `remove_file` to fail
    // deterministically (EISDIR) even under root / CAP_DAC_OVERRIDE.
    std::fs::create_dir(&run_path).unwrap();
    drop(run);
    let err = sp.error().expect("failed unlink must surface spill error");
    assert!(err.0.contains("cannot remove the spill file"), "{err}");
    let res = dest.append(&[7; 16 << 10]);
    assert!(res.is_err(), "second store must not reuse quota of an un-unlinked file");
    std::fs::remove_dir(&run_path).unwrap();
    let mut bytes = 0u64;
    for path in [retained.as_path(), dest.path()] {
        if let Ok(f) = File::open(path) {
            f.sync_all().unwrap();
            bytes += f.metadata().unwrap().blocks() * 512;
        }
    }
    assert!(bytes <= limit, "allocated {bytes} exceeded quota {limit}");
    drop(dest);
    let _ = std::fs::remove_file(&retained);
}

#[test]
#[cfg(target_os = "linux")]
fn partial_write_error_retains_physical_reservation_for_queued_writes() {
    use std::os::unix::fs::MetadataExt;
    if std::env::var_os("IO_PARTIAL_WRITE_TEST_CHILD").is_none() {
        let status = std::process::Command::new("bash")
            .args([
                "-c",
                "trap '' XFSZ && ulimit -f 6144 && exec \"$1\" --exact io::tests::partial_write_error_retains_physical_reservation_for_queued_writes --nocapture",
                "partial-write",
            ])
            .arg(std::env::current_exe().unwrap())
            .env("IO_PARTIAL_WRITE_TEST_CHILD", "1")
            .status()
            .unwrap();
        assert!(status.success(), "child process failed: {status}");
        return;
    }
    // Test both an exact 8 MiB cap and a 9 MiB cap (the 9 MiB cap admits the
    // 8 MiB write into `write_all_at` so it writes 6 MiB and hits EFBIG, proving
    // the partial write's reservation blocks the already-queued 4 MiB write).
    for (tag, limit) in [("cap-8m", 8 << 20), ("cap-9m", 9 << 20)] {
        let scratch = tlx_testkit::TempDir::new(&format!("io-partial-write-{tag}"));
        let spill = Spill::new(SpillConfig { dir: Some(scratch.child_path("spill")), maxdisk: Some(limit), ..Default::default() });
        let queue = spill.store("queue").unwrap();
        let trace = spill.store("trace").unwrap();
        let first = spill.write_async(&queue, Box::new(vec![17u8; 8 << 20]));
        let second = spill.write_async(&trace, Box::new(vec![3u8; 4 << 20]));
        spill.wait_for_writes();
        assert!(first.wait().is_err(), "{tag}: first write must fail");
        if limit == 9 << 20 {
            let err = second.wait().expect_err("queued 4 MiB write must be blocked by partial write's physical reservation");
            assert!(err.0.contains("-maxdisk"), "{tag}: unexpected second error: {err}");
        }
        let physical: u64 = [&queue, &trace]
            .into_iter()
            .map(|s| {
                let f = File::open(s.path()).unwrap();
                f.sync_all().unwrap();
                f.metadata().unwrap().blocks() * 512
            })
            .sum();
        assert!(physical <= limit, "{tag}: physical {physical}, quota {limit}, logical {}", spill.counters().used);
        drop((queue, trace));
        assert_eq!(spill.counters().used, 0, "{tag}: leaked logical bytes");
    }
}

/// Punching a fragmented store back down to <= 4 live pages can still leave an
/// extent-tree leaf block allocated on ext4; other stores filling the remaining
/// nominal data budget must not bypass `-maxdisk`.
#[cfg(unix)]
#[test]
fn orphaned_extent_tree_metadata_after_punch_respects_maxdisk() {
    use std::io::Write;
    use std::os::unix::fs::MetadataExt;

    let scratch = tlx_testkit::TempDir::new("io-orphan-extent-meta");
    let dir = scratch.child_path("spill");
    let other_path = scratch.child_path("interleave.bin");
    let limit = 10 * PAGE as u64; // 40 KiB
    let spill = Spill::new(SpillConfig { dir: Some(dir.clone()), maxdisk: Some(limit), ..Default::default() });
    let s1 = spill.store("frag").unwrap();
    let mut other = std::fs::OpenOptions::new().create(true).write(true).truncate(true).open(&other_path).unwrap();
    let page = vec![0x33u8; PAGE];
    let mut refs = Vec::new();
    for _ in 0..9 {
        match s1.append(&page) {
            Ok(r) => {
                refs.push(r);
                let f = std::fs::File::open(s1.path()).unwrap();
                f.sync_all().unwrap();
                other.write_all(&page).unwrap();
                other.sync_all().unwrap();
            }
            Err(e) => {
                assert!(e.0.contains("-maxdisk"), "{e}");
                break;
            }
        }
    }
    assert!(refs.len() >= 6, "expected at least 6 pages written, got {}", refs.len());
    // Punch down to 3 live pages (<= 4 inline extents); ext4 keeps its extent-tree block.
    while refs.len() > 3 {
        s1.delete_reclaimable(refs.pop().unwrap());
    }
    let s2 = spill.store("fill-a").unwrap();
    let s3 = spill.store("fill-b").unwrap();
    for s in [&s2, &s3] {
        for _ in 0..4 {
            match s.append(&page) {
                Ok(_) => {}
                Err(e) => {
                    assert!(e.0.contains("-maxdisk"), "{e}");
                    break;
                }
            }
        }
    }
    let total_alloc: u64 = std::fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .filter(|e| e.path().extension().is_some_and(|x| x == "spill"))
        .map(|e| {
            let f = std::fs::File::open(e.path()).unwrap();
            f.sync_all().unwrap();
            f.metadata().unwrap().blocks() * 512
        })
        .sum();
    assert!(total_alloc <= limit, "physical allocated bytes {total_alloc} exceeded -maxdisk {limit} with orphaned extent-tree metadata");
}

#[test]
fn injected_write_error_keeps_data() {
    let scratch = tlx_testkit::TempDir::new("io-inject");
    let dir = scratch.child_path("spill");
    let spill = Spill::new(SpillConfig { dir: Some(dir.clone()), fail_after: Some(3 * 1024), ..Default::default() });
    let mut v: SpillVec<u64> = SpillVec::new(1024, "log");
    for i in 0..1000u64 {
        v.push(i * 3);
    }
    // Blocks of 128 values (1 KiB): the first three are written, the
    // others fail and stay in memory.
    v.spill(&spill, false).unwrap_or(());
    let e = v.settle().unwrap_err();
    assert!(e.0.contains("injected write error"), "{e}");
    assert_eq!(spill.error(), Some(e));
    assert_eq!(v.spilled_blocks(), 3);
    for i in 0..1000 {
        assert_eq!(v.get(i).unwrap(), i as u64 * 3);
    }
    assert_eq!(v.iter(Some(&spill)).collect::<Vec<_>>(), (0..1000).map(|i| i * 3).collect::<Vec<_>>());
}

#[test]
fn spillvec_round_trip() {
    let scratch = tlx_testkit::TempDir::new("io-vec");
    let dir = scratch.child_path("spill");
    let spill = spill_in(&dir);
    let mut v: SpillVec<[u64; 2]> = SpillVec::new(4096, "trace");
    assert_eq!(v.block_len(), 256);
    let n = 10_000u64;
    for i in 0..n {
        assert_eq!(v.push([i, !i]), i as usize);
        if i % 1000 == 999 {
            v.spill(&spill, false).unwrap();
        }
    }
    v.settle().unwrap();
    assert!(v.spilled_blocks() >= 35, "{}", v.spilled_blocks());
    assert!(v.bytes() <= 2 * 4096, "{}", v.bytes());
    for i in (0..n).step_by(7) {
        assert_eq!(v.get(i as usize).unwrap(), [i, !i]);
    }
    // Everything, the partial last block too; then appending again reads
    // that block back.
    v.spill(&spill, true).unwrap();
    v.settle().unwrap();
    assert_eq!(v.spilled_blocks(), n.div_ceil(256) as usize);
    v.unseal().unwrap();
    v.push([n, !n]);
    v.set(5, [55, 55]).unwrap();
    let all: Vec<[u64; 2]> = v.iter(Some(&spill)).collect();
    assert_eq!(all.len(), n as usize + 1);
    assert_eq!(all[5], [55, 55]);
    assert_eq!(all[n as usize], [n, !n]);
    assert!(spill.counters().read > 0);
    let before = spill.counters().used;
    let mut it = v.drain(Some(&spill));
    let drained: Vec<[u64; 2]> = it.by_ref().collect();
    assert!(it.error().is_none());
    assert_eq!(drained, all);
    // (Draining gives the disk space back.)
    assert!(spill.counters().used < before);
    drop(it);
    // The IO requests own stores until the worker has finished the request,
    // even after publishing a result. Observe cleanup after both barriers.
    spill.wait_for_writes();
    spill.wait_for_reads();
    assert!(!dir.exists(), "the spill directory is removed with its last store");
    assert!(spill.error().is_none());
}

#[test]
fn concurrent_appends() {
    let scratch = tlx_testkit::TempDir::new("io-concurrent");
    let dir = scratch.child_path("spill");
    let spill = spill_in(&dir);
    let store = spill.store("blocks").unwrap();
    let refs: Vec<Vec<(u64, BlockRef)>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..8u64)
            .map(|t| {
                let store = &store;
                sc.spawn(move || {
                    (0..50u64).map(|k| (t * 100 + k, store.append(&data(3000 + k as usize * 37, t * 100 + k)).unwrap())).collect()
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for (seed, r) in refs.into_iter().flatten() {
        assert_eq!(store.read(&r).unwrap(), data(r.len, seed));
    }
}

#[test]
fn wait_for_writes_finishes_and_releases_stores() {
    let scratch = tlx_testkit::TempDir::new("io-wait-writes");
    let dir = scratch.child_path("spill");
    let spill = spill_in(&dir);
    spill.wait_for_writes();
    assert!(spill.dir().is_none(), "waiting without writes creates nothing");
    let store = spill.store("blocks").unwrap();
    let pending: Vec<_> = (0..8).map(|_| spill.write_async(&store, Box::new(vec![42u8; 4096]))).collect();
    drop(store);
    spill.wait_for_writes();
    assert!(pending.iter().all(|p| matches!(p.try_done(), Some(Ok(_)))));
    assert_eq!(spill.counters().written, 8 * 4096);
    assert!(spill.error().is_none());
    assert!(spill.dir().is_none(), "the writer released its last store reference");
    assert!(!dir.exists());
}

#[test]
fn wait_for_reads_finishes_and_releases_stores() {
    let scratch = tlx_testkit::TempDir::new("io-wait-reads");
    let dir = scratch.child_path("spill");
    let spill = spill_in(&dir);
    spill.wait_for_reads();
    assert!(spill.dir().is_none(), "waiting without reads creates nothing");
    let store = spill.store("blocks").unwrap();
    let bytes = vec![42u8; 4096];
    let block = store.append(&bytes).unwrap();
    let pending: Vec<_> = (0..8).map(|_| spill.prefetch(&store, &block)).collect();
    drop(store);
    spill.wait_for_reads();
    assert!(pending.iter().all(|p| p.ready()));
    for p in pending {
        assert_eq!(p.wait().unwrap(), bytes);
    }
    assert_eq!(spill.counters().used, 0);
    assert!(spill.error().is_none());
    assert!(spill.dir().is_none(), "the reader released its last store reference");
    assert!(!dir.exists());
}

#[test]
fn async_writes_and_prefetch() {
    let scratch = tlx_testkit::TempDir::new("io-async");
    let dir = scratch.child_path("spill");
    let spill = spill_in(&dir);
    let store = spill.store("blocks").unwrap();
    let pend: Vec<_> = (0..40u64).map(|k| spill.write_async(&store, Box::new((0..5000u64).map(|i| i ^ k).collect::<Vec<u64>>()))).collect();
    let refs: Vec<BlockRef> = pend.iter().map(|p| p.wait().unwrap()).collect();
    assert!(pend.iter().all(|p| p.with_data(|_| ()).is_none()), "written blocks free their data");
    let pre: Vec<_> = refs.iter().map(|r| spill.prefetch(&store, r)).collect();
    for (k, p) in pre.iter().enumerate() {
        let b = p.wait().unwrap();
        let mut v = vec![0u64; 5000];
        as_bytes_mut(&mut v).copy_from_slice(&b);
        assert!(v.iter().enumerate().all(|(i, &x)| x == i as u64 ^ k as u64));
    }
}

#[test]
fn default_directory_and_lock() {
    let scratch = tlx_testkit::TempDir::new("io-base");
    let base = scratch.path().to_path_buf();
    let spill = Spill::new(SpillConfig { base: Some(base.clone()), ..Default::default() });
    assert!(spill.dir().is_none(), "no directory before the first store");
    let s1 = spill.store("a").unwrap();
    let d = spill.dir().unwrap();
    assert_eq!(d.parent().unwrap(), base.join("states"));
    // Another run on the same spec gets its own directory.
    let other = Spill::new(SpillConfig { base: Some(base.clone()), ..Default::default() });
    let s2 = other.store("a").unwrap();
    assert_ne!(other.dir().unwrap(), d);
    // A directory in use cannot be shared.
    let third = Spill::new(SpillConfig { dir: Some(d.clone()), ..Default::default() });
    let e = third.store("a").err().unwrap();
    assert!(e.0.contains("in use by another process"), "{e}");
    drop((s1, s2));
    assert!(!base.join("states").exists(), "the states directory tlx created is removed when empty");
}

#[test]
fn sizes() {
    assert_eq!(parse_size("512"), Some(512 << 20));
    assert_eq!(parse_size("8G"), Some(8 << 30));
    assert_eq!(parse_size("64k"), Some(64 << 10));
    for bad in ["0", "x", "1.5", "-1", ""] {
        assert_eq!(parse_size(bad), None, "{bad}");
    }
    assert_eq!(SpillMode::parse("Always"), Some(SpillMode::Always));
    assert_eq!(SpillMode::parse("maybe"), None);
    assert_eq!(disk_reserve(10 << 30), (10 << 30) / 50);
    assert_eq!(disk_reserve(1 << 40), 1 << 30);
    assert!(disk_space(&std::env::temp_dir()).is_some());
}

#[test]
fn write_creating_parents_and_append() {
    let scratch = tlx_testkit::TempDir::new("io-files");
    let dir = scratch.child_path("spill");
    let f = dir.join("a/b/out.txt");
    write_creating_parents(&f, b"one").unwrap();
    write_creating_parents(&f, b"two").unwrap();
    assert_eq!(std::fs::read(&f).unwrap(), b"two");
    append_to(&f, b"\nthree").unwrap();
    append_to(&dir.join("new.csv"), b"x\n").unwrap();
    assert_eq!(std::fs::read(&f).unwrap(), b"two\nthree");
    assert_eq!(std::fs::read(dir.join("new.csv")).unwrap(), b"x\n");
    // A parent that cannot be created: the write's error.
    std::fs::write(dir.join("file"), b"").unwrap();
    assert!(write_creating_parents(&dir.join("file/x"), b"").is_err());
}
