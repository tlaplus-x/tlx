use super::super::tracelog::{log_ref, LogRef};
use super::store::Words3;
use super::*;

#[test]
fn bfs_metadata_stays_accounted_while_workers_hold_old_positions() {
    let order = Order::new(2);
    let baseline = order.gauge().bytes();
    order.start(Arc::new(Positions::of_seq(&[0, 1, 2])));
    let before = order.gauge().bytes();
    assert!(before >= baseline + 3 * 8 + 3 * 4, "positions and counts must be registered");
    let old = order.current();
    order.advance();
    let held = order.gauge().bytes();
    drop(old);
    assert!(order.gauge().bytes() < held, "old positions stay charged until their last reader leaves");
}

#[test]
fn recovered_positions_follow_their_entries_not_the_order_read() {
    // A level read from a checkpoint in worker order, its BFS positions
    // recorded: the same positions as the level queued in BFS order.
    let read = [(log_ref(1, 5), 2), (log_ref(0, 7), 0), (log_ref(1, 4), 3), (log_ref(0, 9), 1)];
    let placed = Positions::of_places(&read).expect("valid positions");
    let mut bfs = read;
    bfs.sort_by_key(|&(_, p)| p);
    let refs: Vec<LogRef> = bfs.iter().map(|&(r, _)| r).collect();
    let sorted = Positions::of_seq(&refs);
    for (r, p) in read {
        assert_eq!((placed.pos(r), sorted.pos(r)), (p, p));
    }
    assert_eq!(placed.len, 4);
}

#[test]
fn recovered_positions_must_cover_the_level_once() {
    let twice = [(log_ref(0, 1), 0), (log_ref(0, 2), 0)];
    assert_eq!(Positions::of_places(&twice).err(), Some("a position twice"));
    let past = [(log_ref(0, 1), 0), (log_ref(0, 2), 2)];
    assert_eq!(Positions::of_places(&past).err(), Some("a position past the level"));
    assert_eq!(Positions::of_places(&[]).map(|p| p.len).ok(), Some(0));
}

#[test]
fn resumed_positions_move_to_the_new_search_registry() {
    let positions = Arc::new(Positions::of_seq(&[0, 1, 2]));
    let old = Order::new(2);
    old.start(positions.clone());
    let expected = old.gauge().bytes();
    let new = Order::new(2);
    new.start(positions);
    assert_eq!(new.gauge().bytes(), expected);
}

#[test]
fn cleared_candidates_keep_capacity_charged_until_pressure_reclaims_it() {
    let order = Order::new(2);
    let codec = Words3;
    let mut local = OrderLocal::new(&order, Some(&codec), 1 << 20);
    let baseline = order.gauge().bytes();
    for i in 0..5000 {
        let at = local.store.push(vec![i, i * 2, i * 3], i, Meta { parent: 0, depth: 1, action: 0 });
        local.cands.push((i, 0), at, i);
    }
    local.charge.set(order.gauge(), cand_bytes(&local));
    let full = order.gauge().bytes();
    local.cands.clear();
    local.store.clear();
    local.charge.set(order.gauge(), cand_bytes(&local));
    assert_eq!(order.gauge().bytes(), full);
    local.cands.shrink_to_fit();
    local.store.shrink();
    local.charge.set(order.gauge(), cand_bytes(&local));
    assert!(order.gauge().bytes() < baseline + 1024);
    drop(local);
    assert_eq!(order.gauge().bytes(), baseline);
}

/// A class's bit is set by `mark` and stays set; another class's bit is
/// clear unless it shares the word and bit; the filter is sized from
/// the level's states within its bounds.
#[test]
fn new_classes_filter() {
    let gauge = Arc::new(Gauge::new());
    let f = NewClasses::new(1000, &gauge);
    assert_eq!(f.words.len(), 256);
    let (a, b) = (0x1234_5678_9abc_def0u64, 0x0fed_cba9_8765_4321u64);
    assert!(!f.may_hold(a) && !f.may_hold(b));
    f.mark(a);
    f.mark(a);
    assert!(f.may_hold(a) && !f.may_hold(b));
    assert_eq!(NewClasses::new(0, &gauge).words.len(), 1 << 6);
    assert_eq!(NewClasses::new(u64::MAX, &gauge).words.len(), 1 << 22);
    assert!(gauge.bytes() >= 256 * 8);
    drop(f);
}

#[test]
fn compacted_metadata_sizes_and_gauge_accounting() {
    // 1. Order::best packs values into 8 B u64 instead of 16 B (u64, u64).
    let order = Order::new(2);
    let best_base = order.gauge().bytes();
    {
        let s = shard(1);
        let mut best = order.best[s].lock();
        for i in 0..1024u64 {
            let fp = (1u64 << 32) | i;
            let key = (i, i % 17);
            best.insert_new(fp, key, pack_key(key));
        }
        let buckets = (best.packed.capacity() + 1).next_power_of_two();
        let expected_packed = buckets * (std::mem::size_of::<(u64, u64)>() + 1) + 16;
        let old_unpacked = buckets * (std::mem::size_of::<(u64, Key)>() + 1) + 16;
        assert_eq!(best.bytes(), expected_packed);
        assert!(expected_packed < old_unpacked, "packed best shard must be strictly smaller than 16 B values");
        order.best_parts[s].set(order.gauge(), best.bytes());
    }
    assert!(order.gauge().bytes() > best_base);

    // 2. OrderLocal CandBuf uses 20 B/cand (8 + 4 + 8) vs 24 B/cand before.
    let mut cands = CandBuf::default();
    let n = 4096usize;
    for i in 0..n as u64 {
        cands.push((i, 3), i as u32, i);
    }
    assert_eq!(cands.bytes(), cands.keys.capacity() * 8 + cands.ats.capacity() * 4 + cands.fps.capacity() * 8);
    assert_eq!(cands.keys.capacity(), n);
    assert_eq!(cands.ats.capacity(), n);
    assert_eq!(cands.fps.capacity(), n);
    assert_eq!(cands.bytes(), n * 20);

    // 3. Narrow Table (8 B/state), Counts (4 B/parent), and Ranks (4 B/cand)
    //    are accurately charged to the gauge.
    let gauge = Arc::new(Gauge::new());
    let refs: Vec<LogRef> = (0..n).map(|i| log_ref(0, i)).collect();
    let positions = Positions::of_seq(&refs);
    positions.account(&gauge);
    let pos_bytes = gauge.bytes();
    let expected_table_entries = n * 8;
    let old_table_entries = n * 16;
    assert!(pos_bytes >= expected_table_entries);
    assert!(pos_bytes < old_table_entries, "narrow Table must stay near 8 B/state, got {pos_bytes}");

    let counts_gauge = Arc::new(Gauge::new());
    let counts = Counts::zeros(n as u64, &counts_gauge);
    let counts_bytes = counts_gauge.bytes();
    assert!(counts_bytes >= n * 4);
    assert!(counts_bytes < n * 8, "narrow Counts must stay near 4 B/parent, got {counts_bytes}");
    drop(counts);
    assert_eq!(counts_gauge.bytes(), 0);

    let ranks = Ranks::new(n);
    assert_eq!(ranks.bytes(), n * 4);
}

#[test]
fn packed_key_overflow_boundary_and_mixed_ordering() {
    // Exact inline/overflow boundaries.
    assert_ne!(pack_key((0, 0)), OVERFLOW_KEY);
    assert_eq!(unpack_fast(pack_key((0, 0))), (0, 0));
    assert_ne!(pack_key((0, IDX_LIMIT - 1)), OVERFLOW_KEY);
    assert_eq!(unpack_fast(pack_key((0, IDX_LIMIT - 1))), (0, IDX_LIMIT - 1));
    assert_eq!(pack_key((0, IDX_LIMIT)), OVERFLOW_KEY);
    assert_ne!(pack_key((POS_LIMIT - 1, IDX_LIMIT - 1)), OVERFLOW_KEY);
    assert_eq!(unpack_fast(pack_key((POS_LIMIT - 1, IDX_LIMIT - 1))), (POS_LIMIT - 1, IDX_LIMIT - 1));
    assert_eq!(pack_key((POS_LIMIT, 0)), OVERFLOW_KEY);

    let big_idx = IDX_LIMIT + 3;
    let huge_idx = (u32::MAX as u64) + 17;

    // Mixed comparisons in BestShard in both arrival orders.
    let offer = |shard: &mut BestShard, fp: u64, key: Key| -> bool {
        let p = pack_key(key);
        match shard.update_if_less(fp, key, p) {
            Some(less) => less,
            None => {
                shard.insert_new(fp, key, p);
                true
            }
        }
    };

    let mut s = BestShard::default();

    // (5, (1 << 24) + 3) < (6, 0): overflow beats existing fast-path.
    assert!(offer(&mut s, 10, (6, 0)));
    assert!(offer(&mut s, 10, (5, big_idx)));
    assert_eq!(s.get_key(10), Some((5, big_idx)));
    assert_eq!(s.get_packed(10), Some(OVERFLOW_KEY));

    // (6, 0) does NOT beat existing overflow (5, (1 << 24) + 3).
    assert!(offer(&mut s, 11, (5, big_idx)));
    assert!(!offer(&mut s, 11, (6, 0)));
    assert_eq!(s.get_key(11), Some((5, big_idx)));

    // (4, 9) < (5, 1 << 24): fast-path replaces overflow AND clears stale cold entry.
    assert!(offer(&mut s, 12, (5, IDX_LIMIT)));
    assert!(s.overflow.as_ref().is_some_and(|ov| ov.contains_key(&12)));
    assert!(offer(&mut s, 12, (4, 9)));
    assert_eq!(s.get_key(12), Some((4, 9)));
    assert_eq!(s.get_packed(12), Some(pack_key((4, 9))));
    assert!(s.overflow.as_ref().is_none_or(|ov| !ov.contains_key(&12)));

    // (5, 1 << 24) does NOT beat existing fast-path (4, 9).
    assert!(offer(&mut s, 13, (4, 9)));
    assert!(!offer(&mut s, 13, (5, IDX_LIMIT)));
    assert_eq!(s.get_key(13), Some((4, 9)));

    // Same parent: fast-path (5, 9) beats overflow (5, 1 << 24) and removes stale entry.
    assert!(offer(&mut s, 14, (5, IDX_LIMIT)));
    assert!(offer(&mut s, 14, (5, 9)));
    assert_eq!(s.get_key(14), Some((5, 9)));
    assert!(s.overflow.as_ref().is_none_or(|ov| !ov.contains_key(&14)));

    // Overflow vs overflow with idx > u32::MAX (no u32 truncation).
    assert!(offer(&mut s, 15, (5, huge_idx + 10)));
    assert!(offer(&mut s, 15, (5, huge_idx)));
    assert!(!offer(&mut s, 15, (5, huge_idx + 1)));
    assert_eq!(s.get_key(15), Some((5, huge_idx)));

    // pos overflow boundary: ((1 << 40) - 2, IDX_LIMIT - 1) < ((1 << 40) - 1, 0).
    assert!(offer(&mut s, 16, (POS_LIMIT, 0)));
    assert!(offer(&mut s, 16, (POS_LIMIT - 1, IDX_LIMIT - 1)));
    assert_eq!(s.get_key(16), Some((POS_LIMIT - 1, IDX_LIMIT - 1)));
    assert!(s.overflow.as_ref().is_none_or(|ov| !ov.contains_key(&16)));
}

#[test]
fn cand_buf_overflow_retain_and_sort_order() {
    let order = Order::new(2);
    let mut cands = CandBuf::default();
    let big_idx = IDX_LIMIT + 3;
    let huge_idx = (u32::MAX as u64) + 5;

    let insert_best = |fp: u64, key: Key| {
        let s = shard(fp);
        let mut best = order.best[s].lock();
        let p = pack_key(key);
        if best.update_if_less(fp, key, p).is_none() {
            best.insert_new(fp, key, p);
        }
        order.best_parts[s].set(order.gauge(), best.bytes());
    };

    // Offer losing + winning candidates across inline and overflow keys.
    let entries: &[(u64, Key, bool)] = &[
        (100, (6, 0), false),         // loses to (5, big_idx)
        (100, (5, big_idx), true),    // wins
        (101, (5, IDX_LIMIT), false), // loses to (4, 9)
        (101, (4, 9), true),          // wins
        (102, (5, huge_idx), true),   // wins (idx > u32::MAX)
        (103, (6, 0), true),          // wins (fast-path > (5, huge_idx))
        (104, (5, 2), true),          // wins (same parent as overflowed keys)
        (105, (POS_LIMIT, 1), true),  // wins (pos overflow)
    ];
    for (at, &(fp, key, _)) in entries.iter().enumerate() {
        insert_best(fp, key);
        cands.push(key, at as u32, fp);
    }

    cands.retain_best(&order);
    let expected_kept: Vec<Key> = entries.iter().filter(|e| e.2).map(|e| e.1).collect();
    assert_eq!(cands.len(), expected_kept.len());
    for (i, &k) in expected_kept.iter().enumerate() {
        assert_eq!(cands.key_at(i), k);
        assert_eq!(cands.pos_at(i), k.0);
    }

    // Sorting by key_at produces exact total order across mixed inline/overflow keys.
    let mut by_key: Vec<u32> = (0..cands.len() as u32).collect();
    assert!(cands.has_overflow());
    by_key.sort_unstable_by_key(|&i| cands.key_at(i as usize));
    let sorted: Vec<Key> = by_key.iter().map(|&i| cands.key_at(i as usize)).collect();
    assert_eq!(sorted, vec![(4, 9), (5, 2), (5, big_idx), (5, huge_idx), (6, 0), (POS_LIMIT, 1)]);

    // End-to-end rank_and_count_kept -> Counts::prefix_sums -> Positions::pos
    // on mixed inline/overflow keys (including idx >= 1 << 24 and idx > u32::MAX).
    let mut mixed = CandBuf::default();
    let mixed_keys = [(6, 0), (5, huge_idx), (4, 9), (5, big_idx), (5, 2)];
    for (i, &k) in mixed_keys.iter().enumerate() {
        mixed.push(k, i as u32, 200 + i as u64);
    }
    let gauge = Arc::new(Gauge::new());
    let counts = Counts::zeros(7, &gauge);
    let mut outdegree = OutdegreeHist::new();
    // Parents 4, 5, 6 are initially recorded with outdegree 0 during expansion.
    for _ in 0..3 {
        outdegree.add(0);
    }
    let scratch = Charge::default();
    let (ranks, wide_table) = rank_and_count_kept(&mixed, &counts, &mut outdegree, &gauge, &scratch);
    assert!(!wide_table);
    assert_eq!(counts.get(4), 1);
    assert_eq!(counts.get(5), 3);
    assert_eq!(counts.get(6), 1);
    let summary = outdegree.summary();
    assert_eq!((summary.min, summary.max), (1, 3));
    let mut table_entries = TableEntries::with_capacity(mixed.len(), wide_table);
    for i in 0..mixed.len() {
        table_entries.push(mixed.pos_at(i), ranks.get(i));
    }
    let (first, len) = counts.prefix_sums();
    assert_eq!(len, 5);
    let table = Arc::new(Table::new(0, table_entries, Charge::default()));
    let positions = Positions::from_parts(vec![Some(table)], first, len);
    // Expected BFS positions matching sorted order:
    // (4, 9) -> 0, (5, 2) -> 1, (5, big_idx) -> 2, (5, huge_idx) -> 3, (6, 0) -> 4
    assert_eq!(positions.pos(log_ref(0, 2)), 0);
    assert_eq!(positions.pos(log_ref(0, 4)), 1);
    assert_eq!(positions.pos(log_ref(0, 3)), 2);
    assert_eq!(positions.pos(log_ref(0, 1)), 3);
    assert_eq!(positions.pos(log_ref(0, 0)), 4);
}

#[test]
fn wide_table_ranks_and_counts_fallback() {
    // 1. Ranks widens cleanly when a rank reaches u32::MAX or above.
    let mut ranks = Ranks::new(3);
    assert_eq!(ranks.bytes(), 3 * 4);
    ranks.set(0, 7);
    ranks.set(1, u32::MAX as u64);
    assert_eq!(ranks.get(0), 7);
    assert_eq!(ranks.get(1), u32::MAX as u64);
    assert_eq!(ranks.bytes(), 3 * 4);
    ranks.set(2, (u32::MAX as u64) + 1);
    assert_eq!(ranks.get(0), 7);
    assert_eq!(ranks.get(1), u32::MAX as u64);
    assert_eq!(ranks.get(2), (u32::MAX as u64) + 1);
    assert_eq!(ranks.bytes(), 3 * 8);

    // 2. TableEntries widens dynamically on push/set and serves Positions::pos.
    let wide_rank = (u32::MAX as u64) + 99;
    let mut entries = TableEntries::with_capacity(4, false);
    assert!(!entries.is_wide());
    entries.push(0, 5);
    entries.push(1, wide_rank);
    assert!(entries.is_wide());
    assert_eq!(entries.get(0), (0, 5));
    assert_eq!(entries.get(1), (1, wide_rank));

    let gauge = Arc::new(Gauge::new());
    let table = Arc::new(Table::new(10, entries, Charge::default()));
    let positions = Positions::from_parts(vec![Some(table)], Box::new([0, 100]), 2);
    positions.account(&gauge);
    assert_eq!(positions.pos(log_ref(0, 10)), 5);
    assert_eq!(positions.pos(log_ref(0, 11)), 100 + wide_rank);
    assert!(gauge.bytes() >= 4 * 16);

    // TableEntries::set also widens cleanly when parent_pos > u32::MAX.
    let mut z = TableEntries::zeroed(2, false);
    assert!(!z.is_wide());
    z.set(1, (u32::MAX as u64) + 1, 42);
    assert!(z.is_wide());
    assert_eq!(z.get(0), (0, 0));
    assert_eq!(z.get(1), ((u32::MAX as u64) + 1, 42));

    // 3. Counts handles u32::MAX - 1 inline and >= u32::MAX via overflow map.
    let counts_gauge = Arc::new(Gauge::new());
    let counts = Counts::zeros(4, &counts_gauge);
    let base_counts_bytes = counts_gauge.bytes();
    counts.store(0, 3, &counts_gauge);
    counts.store(1, (u32::MAX - 1) as u64, &counts_gauge);
    assert_eq!(counts_gauge.bytes(), base_counts_bytes);
    counts.store(2, u32::MAX as u64, &counts_gauge);
    counts.store(3, (u32::MAX as u64) + 42, &counts_gauge);
    assert!(counts_gauge.bytes() > base_counts_bytes);

    assert_eq!(counts.get(0), 3);
    assert_eq!(counts.get(1), (u32::MAX - 1) as u64);
    assert_eq!(counts.get(2), u32::MAX as u64);
    assert_eq!(counts.get(3), (u32::MAX as u64) + 42);

    let (first, len) = counts.prefix_sums();
    let expected_first = [0u64, 3, 3 + (u32::MAX - 1) as u64, 3 + (u32::MAX - 1) as u64 + u32::MAX as u64];
    let expected_len = expected_first[3] + (u32::MAX as u64) + 42;
    assert_eq!(&*first, &expected_first);
    assert_eq!(len, expected_len);
}
