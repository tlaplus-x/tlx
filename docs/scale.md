# Scale: memory budget, fingerprint set, queues, disk tier, checkpoints

This document describes how tlx keeps large state spaces inside a memory budget: the budget and its
pressure stages, safepoints, the fingerprint set and its disk tier, the state queue, the archive for
layout-miss resume, the trace log, the liveness edge log, checkpoint/recover and the disk I/O layer.
It expands design.md §7.2 (fingerprint set), design.md §7.3 (exploration) and design.md §7.7 (memory and
disk). Flags and `TLX_*` variables are defined in [configuration.md](configuration.md); this document
only explains what they do to the design. Code lives in `crates/tlx-runtime` (`mem.rs`, `cache_mem.rs`,
`fpset/`, `queue/`, `io/`, `explore/`).

## 1. Summary

- **One budget.** `-maxmem` (default: half of physical memory) covers the fingerprint set, the state
  queue, the trace log, the archive used for layout-miss resume, the liveness edge log, evaluation
  caches and the VIEW/SYMMETRY candidate buffers. Each component counts its bytes in a `mem::Gauge`
  registered with `MemBudget`; when the total is over budget, components are written to disk in a fixed
  order (§2.3). When everything fits, no directory is created and nothing is written.
- **Safepoints** (§3) give a moment when no worker uses a shared structure; table growth, spilling and
  checkpoints run there.
- **Fingerprint set** (§4): one lock-free open-addressing table, grown in place; when it no longer fits,
  full tables are rotated into sorted runs on disk, with exact lookups.
- **State queue** (§5): blocks of encoded states, compressed and spilled under pressure, read ahead in claim order.
- **Archive, trace log, edge log** (§6-§8): append-only logs, spilled early because the success path
  rarely reads them.
- **Checkpoint/recover** (§9): a consistent cut at BFS level boundaries; the recovered run reports the same
  verdict, counts, depth and counterexample length as an uninterrupted run.
- **I/O layer** (§10): a spill directory of block stores with checksums, background writer and prefetcher.

Measurements beyond memory (tlx with a small budget and in control groups, against TLC under the same
limit) are made with the `disk` lane of [benchmarking.md](benchmarking.md) section 1, which owns the
unit (`P`, tlx's in-memory peak RSS), the two kinds of limit, and the TLC memory settings used under
them.

Disk is never used to change results: counts, depth, traces and verdicts are identical with and without
spilling (tests force the disk paths with `-spill always`, see [testing.md](testing.md)).

## 2. Unified memory budget

### 2.1 User interface

| Option | Meaning |
|---|---|
| `-maxmem X` | Soft limit for all of tlx. `X` in (0,1): fraction of physical memory; otherwise MiB, or a number with `K/M/G/T` suffix; at least 1 MiB (`mem::parse_budget`). Default 0.5. |
| `-fpmem X` | TLC-compatible: `X` in (0,1) is a fraction of physical memory, otherwise MiB. When given, the fingerprint table has this fixed size and never grows or spills; when full the run stops with a capacity message. |
| `-fpbits N` | The fingerprint set is divided into 2^N shards by the high bits (ranges of slots); growth work is split along them. |
| `-spill auto\|off\|always` | `auto`: use disk only when over budget. `off`: never write; over budget the run ends with a capacity error. `always`: use the disk paths from the start (testing). |
| `-metadir DIR`, `-maxdisk X` | Spill directory; upper bound on spill bytes (a free-space reserve of min(1 GiB, 2%) is always kept). |
| `-checkpoint MIN`, `-recover DIR` | See §9. |

"Physical memory" (the default and the fractions) is the machine's, or on Linux the memory limit of
the process's control group when that is lower (`mem::physical_bytes`: cgroup v2 `memory.max` and
`memory.high` of the group and its ancestors, v1 `memory.limit_in_bytes`), as the JVM sizes TLC's heap
in a container. Without it a run in a container whose limit is below half of the host's memory took a
budget it could not have, and the kernel killed it instead of tlx spilling to disk.

Environment aliases and test knobs (`TLX_MAXMEM`, `TLX_SPILL`, `TLX_METADIR`, `TLX_MAXDISK`,
`TLX_RETAIN_MB`, `TLX_MEMO_MB`, `TLX_SEG_BYTES`, `TLX_FP_TABLE_MIN`, `TLX_FP_SPILL_SLOTS`,
`TLX_QUEUE_COMPRESS_MB`, `TLX_CHECKPOINT_*`, `TLX_THP`) are documented in configuration.md. The default
is a fixed fraction of physical memory, not "what is free now": a limit that moves with other processes
would make the point at which a run reports "fingerprint set full" irreproducible.

### 2.2 Accounting (`MemBudget`, `mem::Gauge`)

`MemBudget` (`mem.rs`) holds the budget, the last sampled resident memory, the highest pressure stage
reached and a registry of gauges, one per `mem::Component`: archive, evaluation caches, trace logs,
liveness edge logs, frontier, representative candidates, fingerprint set. Accounting is per segment or
table (1 MiB segment allocation/release, table growth), or published by the owner every 1024 states, so
the hot path has no atomics. `accounted()` is the sum of the gauges.

Uncontrolled memory (interpreter values, the Dyn interner, the C library, the pre-run) is not estimated
separately. A monitor thread samples the process every 50 ms (macOS `ri_phys_footprint` from
`proc_pid_rusage`; Linux anonymous resident memory, `statm` resident minus shared, so code pages are not
counted) and the budget uses `max(accounted, RSS)`.

Details that matter:

- The evaluation caches (interpreter fallback memo and region memo of mixed mode, `exec/memo.rs`) get a
  quota of budget/8 split over the workers (`cache_mem.rs`); `TLX_MEMO_MB` is the total over all threads.
  Each thread's table starts at 1024 slots and doubles as it fills (up to `TLX_MEMO_SLOTS`), so a search
  that memoizes little does not touch a full table per thread. Under pressure the quota is halved and a
  thread clears its table when it exceeds it.
- Representative candidates buffered by workers for VIEW/SYMMETRY (design.md §7.3,
  `explore/order.rs`) are held until the level is resolved, i.e. a whole level of new states. With a
  state codec (compiled tier) each worker keeps them XOR-varint encoded against the previous candidate,
  as the queue's blocks are, in segments of whole records (`TLX_SEG_BYTES`) together with what only a
  kept candidate needs (parent log entry as the record's log reference, action and depth as varints),
  and decodes them in offer order when resolving; from stage 4 on, while over budget (as the queue: no more below 7/8 of it), the full
  segments go to disk and resolving
  reads them back with read-ahead. In memory stay 24 B per candidate (key, fingerprint, record index),
  the level's best-key tables and BFS positions, about 100-150 B per state of the widest level in all:
  with several workers a VIEW/SYMMETRY model whose widest level has N states needs about that much
  beyond the budget. Resolving queues the whole next level at once and offers its segments to the disk
  every 1024 states, as expanding does. The interpreter keeps the state objects. The gauge tracks reserved capacities as they grow, including candidate metadata, encoded buffers and codec scratch, the sharded best-key tables, BFS positions/counts (until their last reader releases them), and resolve indices, ranks and output tables. Clearing a buffer keeps it charged; under pressure workers shrink empty candidate buffers at level boundaries and release best-key table capacity after resolving a level. In-place unstable sorting allocates no additional sort workspace. Interpreted states' heap data is covered by RSS. (MultiPaxos_MC with 8 workers: the widest
  level, 4M states of 335 words, took about 40 GiB as objects, beyond the default budget, and about 1.1 GiB
  encoded. With `-maxmem 400M` the candidates still peaked at 1.5 GB, and a 16-worker run in a control
  group of 1.7 GiB was killed; with spilled segments, 24-byte metadata and the next level spilled while
  resolving, the candidates peak at 0.56 GB and the process at 1.1 GB instead of 2.0 GB.)
- Allocator behavior counts: the global allocator is mimalloc, which returns freed pages after a delay.
  After a pressure stage was reached the monitor calls `mem::purge` (`mi_collect(true)`) before each
  sample; default runs never call it. On Linux, transparent huge pages are disabled when `-maxmem` is
  below 512 MiB + 64 MiB per worker (`TLX_THP`), because they add several MiB per worker. Fingerprint tables
  of 1 MiB and more are anonymous `mmap`s (`madvise(MADV_HUGEPAGE)` on Linux), so unused pages stay
  non-resident and are returned to the system at once on drop. tree-sitter allocates through mimalloc too.
- During initial-state generation (before the monitor starts) `init_relieve` runs the pressure logic every
  16384 new initial states and hands queued segments and full trace-log blocks to the disk.

### 2.3 Pressure stages

`relieve` (`explore/mod.rs`) runs once at the start of the search and then every 50 ms from the monitor.
When over budget, the stages are applied in this order, at most one more stage per cycle, so that the next
RSS sample shows the effect of the previous one:

| Stage | Component | Action | Why this order |
|---|---|---|---|
| 1 | Archive (levels kept for layout-miss resume) | Spill to disk; dropped if `-spill off` or the archive holds objects (interpreter models) | Used only on a layout miss |
| 2 | Trace log | Full blocks to disk | Never read on the success path |
| 3 | Liveness edge log | Full blocks to disk | Read once, sequentially, after the search |
| 4 | Frontier, representatives' candidates | Compress new blocks and write the candidates' full segments to disk (VIEW/SYMMETRY with several workers); next cycle still over, spill queue segments (back to normal below 7/8 of budget; with `-spill off` only compress) | Sequential write, sequential read-ahead |
| 5 | Fingerprint set | Stop growing; rotate full tables into disk runs (§4.2) | Slowest, so last |

Stage 5 is decided at growth time in `grow_seen` (inside a safepoint): if the old and new table do not fit
in "budget minus other components", it first applies stages 1-4 and otherwise grows to exactly what fits
(not if that is less than 1.25x the current size) and caps the table there. After a hard stop, `-fpmem`
runs say "rerun with a larger -fpmem", others "-maxmem". Stage 1 does not credit the archive bytes until
the next sample, because spilling is done by the workers on their next tick and segments shared with
liveness edge records cannot be freed by dropping the archive.

`-stats` prints each component's current and peak bytes, the RSS peak, `budget (-maxmem)` and
`budget pressure stage`.

### 2.4 Liveness after the search

The CSR behavior graph is built after the search structures (fingerprint set, queue, archive, trace log)
have been released. Before building, the size of the CSR and the fp-to-id index is estimated from the edge
log; if resident memory plus the estimate exceeds the limit, liveness ends with
`liveness needs more memory: ...` (a resource error, exit 255, like a full fingerprint set). The product
graph, the fallback re-exploration and the VIEW/SYMMETRY path check resident memory periodically
(`mem::RssGuard`). The limit counts only what liveness adds: it first purges the allocator, takes the
resident memory then as `base` (`mem::live_base`) and allows `max(budget, base + budget/4)`
(`mem::live_limit`), plus `LIVE_RSS_SLACK` (8 MiB) for first-touch pages. Without this, small budgets
failed on process baseline memory that has nothing to do with the graph. Edge-log pattern ids are stored as
`u8`/`u16`/`u32` by the number of distinct patterns (`tlx_live::Ids`). The product is built and searched
part by part (design.md §7.4): its memory is that of the largest part, or of the parts in progress together
with several workers (over the budget together, they run one at a time); the nodes of waiting tableau states
are not built, and only edges that can lie on an accepting cycle are stored.

## 3. Safepoints

Growing, spilling and checkpointing need a moment when no worker is inside a shared structure. The level
barrier is one such moment but a level can take minutes, so there are mid-level safepoints
(`explore/safepoint.rs`).

- **Control word**: `Control` is an atomic word whose bit 0 is stop and whose other bits are pending
  safepoint requests. Workers read it once before each task; zero means go on, so the hot path costs one
  load.
- **Request and arrival**: any thread may request (a worker that reaches the table's high-water mark, the
  monitor when over budget, the checkpoint timer). A worker that sees a request calls `Safepoint::park`;
  the last active worker to arrive runs the request and may split the work over the parked workers with
  `Crew::broadcast`. Workers waiting at a level barrier or finished do not count as active (`leave`/`join`).
- **Inside an insert**: a worker that hits the table's hard limit parks as "inserting"; it holds no table
  pointer, so after resuming it re-reads the pointer. The margin between high-water and hard limit only has
  to absorb the inserts workers finish for their current task.
- **Narrow levels**: when one worker expands a narrow level alone (design.md §7.3), it performs safepoint
  work itself, with the same-sized crew of temporary threads for large rehashes.
- **Preference**: non-urgent work (checkpoints, preventive growth, run merges) waits for a level barrier.
  `Options::safepoint_every` requests no-op safepoints periodically for tests.

## 4. Fingerprint set (`fpset/`)

### 4.1 In-memory table

- One open-addressing table of `AtomicU64`, linear probing, 0 = empty (fingerprint 0 is stored as 1),
  insert = one CAS. No fingerprint bits are borrowed for flags.
- **Placement by high bits**: `home = (fp * nslots) >> 64` (fastrange). The table is monotone in the
  fingerprint, hence approximately sorted (only probe clusters are unordered), its size need not be a power
  of two (it can fill the budget exactly), and shards are contiguous ranges. Fingerprints are uniform in all
  bits.
- **No wrap-around**: `OVERFLOW` (4096) extra slots follow the table; probing into them past the end counts
  as full. Sorting and merging need no wrap-around handling.
- **Load**: high-water 0.75 requests growth, hard limit 0.9. A failed lookup at 0.9 expects about 50
  probed slots against about 8.5 at 0.75, so growth should happen before the hard limit.
- **Start and growth**: without `-fpmem` the table starts at 2^20 slots (8 MiB) (`TLX_FP_TABLE_MIN` in
  tests); at high-water, in a safepoint, a table of twice the size (or what the budget allows) is allocated
  and all workers re-insert the old table in parallel by range. When only one worker is active (narrow
  level) the same number of temporary threads does it for tables of at least 2^20 slots. Peak during growth
  is the sum of both tables.
- **Entry count** is not a shared counter (a single contended cache line more than doubled the insert cost
  at 8 threads): 64 stripes (by worker number) each flush into the shared count at 64 entries; near the
  marks the shared count is used directly, so high-water and hard limit decisions are exact.
- Fingerprints themselves: unchanged from design.md §7.2; a successful run reports TLC's
  optimistic collision estimate.

### 4.2 Disk tier

**Entry.** `grow_seen` enters the disk tier when growth no longer fits (after stages 1-4) and `-spill` is
not `off` and no `-fpmem` was given. From then on a table is rotated at every high-water mark instead of
grown. With `-spill always` the table has at most `TLX_FP_SPILL_SLOTS` slots (default 2^18) and rotates
regardless of budget.

**Structure.**

```
memory: current table (CAS inserts)   old table (read-only copy of the newest run)
        per run: block Bloom filter (512-bit blocks, 10 bits and 7 probes per fingerprint, ~1% false positives)
        per run: fence per 4 KiB page (first fingerprint + block, ~0.02 B/fingerprint)
disk:   runs: sorted, disjoint fingerprints in a BlockStore (`fpset-<n>.spill`), 8 B/fingerprint
```

**Insert** finds a free slot in the current table, then consults the old table and the runs (Bloom
negative: skip; positive: read one page, binary search). The answer is exact and synchronous, so workers,
queue, trace log, statistics, `TLCGet`, archive/resume, edge logs and VIEW/SYMMETRY representative
selection never need to know about the disk tier; "new state" means the same thing, and with one worker
the expansion order, early-stop counts and counterexamples equal the in-memory run. The alternative
(delayed duplicate detection: treat Bloom-positive states as new and resolve at the level barrier) was
rejected because it would check invariants on a second concrete state of an old VIEW/SYMMETRY class and
change early-stop counts. It also is unnecessary: with two in-memory generations most duplicates are
caught in memory.

**Rotation** (`FpSet::rotate`, in a safepoint): the current table is sorted in place (clusters are already
in order between each other, so sorting within clusters yields a valid probe layout, `Table::sorted_clusters`),
written as one run by the crew in parallel by slot range, and then kept as the read-only old table; the
previous old table is freed (its run is already on disk). The invariant is that each fingerprint is in the
current table or on disk, so the old table can be dropped at any time (`drop_old`).

**Runs.** After assembly a run's byte range is mapped read-only (`BlockStore::map`, `MAP_SHARED`,
`MADV_RANDOM`: a lookup whose page is not in the page cache reads that page, not the system's
read-around window, 128 KiB on Linux); lookups binary-search the mapping without system calls. Each page's checksum is verified the first time a lookup
reads it. If mapping fails, lookups fall back to `pread`. Mapped clean file pages are not part of the
macOS phys footprint or the Linux anonymous resident memory, so the budget sampling is unaffected; a
device read error on a mapped page ends the process with SIGBUS rather than `Outcome::Io`.
Mapping removed about half of the instructions and nearly all system time of a forced disk tier
(system time 50 s to 0.1 s at 8 workers on a 17M-state model): without it each hit cost a 4 KiB `pread`
plus a checksum and workers contended in the kernel on one file.

**Merging.** Runs are merged in size tiers (four runs of the same `log4(count)` become one) by a single
background k-way merge; the next insert that needs the disk requests a safepoint in which the result
replaces its inputs (`install_merge`). Input blocks are deleted (hole-punched) when the last reference
goes. Dropping the set cancels and joins the merge.

**Table size in disk mode.** Two tables (current + old) share what the budget leaves after other
components and the runs' Bloom filters and indexes, but never less than a quarter of the budget
(`TABLES_SHARE`): reads of the disk are avoided by the in-memory window, and a window that is too small
makes nearly every duplicate a disk read (one 64 MiB case went from 17.5 million page reads and 62 s of
system time to 0.94 million and 2.8 s with the floor). The new table takes half; if the old table does not
fit it gets what is left (at least a quarter), else it is dropped. Minimum 2^16 slots
(`ROTATE_MIN_SLOTS`), maximum the set's limit.

**Why most disk lookups hit.** Under a forced tiny table, a model whose widest level has 178k new states
read 8.1 million pages and 7.9 million of those found the fingerprint: a duplicate arrives from a
predecessor anywhere in the previous (or current) level, so it lies about one to two level widths behind
the first insertion. Once the two in-memory tables cover about two level widths (here ~200k fingerprints)
disk reads disappear. Bloom filters cannot help with such hits. More old tables (a longer window) were not
kept: under a fixed budget k tables raise the minimum window only from 0.375 to (k-1)/k x 0.75 of the
slots and add k-2 probes to each new insert.

**Capacity** (64 GB machine, 45 GB controllable): a memory-only table at load 0.375-0.75 costs 10.7-21 B
per fingerprint (1.3-2.5x10^9 fingerprints); a fixed table at load 0.9 costs 8.9 B (3x10^9); the disk tier
costs about 1.3 B per fingerprint plus two in-memory generations (about 2x10^10 with 160 GB of disk). When
Bloom filters exceed their share, new runs drop to 6 or 4 bits per fingerprint, which only costs I/O.

**Errors.** A failed rotation write (write error, `-maxdisk`, disk full) or lookup read (read error,
checksum mismatch) is recorded in `Spill`; after a failed rotation the set is unchanged (written blocks are
deleted) and further inserts fail at the hard limit; the search ends with `Outcome::Io`, exit 255.

**Statistics** in `-stats`: rotations and their time, run merges, runs and fingerprints on disk, lookups
(pages read) and hits, Bloom/index memory, load of the current table.

**Not done.** NUMA sharding and routing of successors by fingerprint (`-fpbits` shards exist but all run
under one safepoint protocol; the development machine is UMA, so there is nothing to validate against);
batched inserts with prefetch; batch duplicate detection at level end (worthwhile only for models whose
level width approaches table size); readahead of run files on Linux.

## 5. State queue (`queue/`, `explore/frontier.rs`)

### 5.1 Encoding

Compiled models implement `StateCodec` (words per state, `encode`, `decode`/`decode_into`); interpreter
models keep object blocks (`Objects`) that are never spilled; for them only the fingerprint set, trace log
and edge log spill.

- **Record**: log reference delta (varint), fingerprint (8 B), bitmap of changed words, XOR of the changed
  words against the previous record (varints). A **block** holds at most 256 records (`BLOCK`), the first
  XORed with zero so every block decodes on its own. A **segment** is 1 MiB (`TLX_SEG_BYTES`), belongs to
  one level and one worker, and is a sequence of blocks. Compressed cost is 6-52 B of state plus 8 B
  fingerprint plus about 1 B of log reference.
- **Object blocks** (`Task` values) are used while the queue is small: a raw fixed-width block was about
  4% slower and an XOR block about 5% slower on a model whose states are cheap to expand. `auto` therefore
  writes object blocks while the queue is at most min(64 MiB, budget/16) (`TLX_QUEUE_COMPRESS_MB`), XOR
  blocks above that, and returns to object blocks below half. Raw encoded blocks exist (`BlockKinds::Raw`)
  but are only selectable through `Config`.
- The encoding costs about 1-2 ns/word; for the large-state models this cuts the peak queue from hundreds
  of MiB to tens (e.g. 900 MB to 21 MB for a 287-word state).

### 5.2 Levels and claiming

A level is a set of per-worker block lists. A worker claims blocks (atomic cursor), first from its own
list (cache locality), then from others in order; this replaces the work-stealing deque (equivalent under
level synchronization, cheaper, order-preserving). At the end of a level, with several workers, a claim
takes only the tail of a block (about remaining/(2 x workers) records, guided self-scheduling); XOR blocks
are claimed whole. With one worker there is one list and the order is exactly FIFO. Segment buffers are
pooled (at most 64) to avoid page-fault and `madvise` costs. `LiveStats::queue` is unexpanded states of the
current level plus the next level.

### 5.3 Spilling and read-ahead

A segment is a shared cell with states `Mem(Arc<Segment>)`, `Pending` (handed to the writer),
`Disk(BlockRef)`, `Fetch` (being read). A claim takes the `Arc<Segment>` and uses it directly;
`Seg::spill` writes only when `Arc::get_mut` succeeds, so a segment being read never spills and no other
synchronization is needed. Memory accounting moves with the data. One `BlockStore` per queue
(`queue-<n>.spill`) and per archive, not per level or worker.

- **Who writes**: each worker hands its newly frozen segments to the writer thread every 1024 states
  (`spill_writer`), except the first window of segments of each level (they are claimed first and would be
  read straight back). The monitor and `grow_seen` write the current level's segments beyond the read-ahead
  window from the tail (`spill_tail`).
- **Read-ahead**: a window of 8 segments (default 8 MiB) split over the workers, at least 2 per list; a
  claim of block i prefetches the following window (`prefetch_ahead`), each segment once. All of this is
  active only after something has spilled.
- **Order is unchanged**: spilling changes where bytes live, not blocks, lists, claims or splits; with one
  worker the order is still exact FIFO.
- **Errors**: a failed read-back puts the block back and the worker stops the search with `Outcome::Io`; a
  failed write keeps the segment in memory and records the error in `Spill`; workers see it at the next tick.
- Cost: forcing everything to disk (`-spill always`) costs about 1% in instructions on mid-size models and
  cuts the peak footprint by half or more.

## 6. Archive and layout-miss resume

With `-compile`, a layout miss stops the search, widens the layout and resumes from the level that was
being expanded (design.md §6.5.3). To do that the visited states of the finished levels must be
kept: **when a level has been expanded its blocks are moved into the archive** (a second `queue::Queue`,
only its writers are used). XOR blocks move whole and zero-copy; object or raw blocks are encoded one by one
when retired. The archive's in-memory allowance defaults to one quarter of the memory budget (1 GiB without a
budget), with `TLX_RETAIN_MB` as an explicit override. Exceeding the allowance or reaching pressure
stage 1 sends encoded segments to disk, preserving the resume point. With disk disabled, or object
states that cannot spill, the archive is dropped. A later miss then restarts from scratch; `-stats`
reports this explicitly, counts restarts after archive loss, and counts previously expanded states
repeated by searches starting from Init. An explicit zero disables archiving.

- **Resume point** (`ResumePoint`): the archive blocks of every worker, all trace logs and statistics. A
  miss rolls back to the start of the failing level; `transcode` converts old-layout words to the new
  layout block by block in parallel (`sample` estimates the time), and `resume_phase` reads the records,
  inserts the new fingerprints into the new set, rewrites the trace log's fingerprint column
  (`TraceLog::set_fp`) and seeds the failing level. Levels before it go back into worker 0's archive, as the
  next miss needs them again.
- **The trace log is not rebuilt**: transcoding does not change state identity, so `(worker, index)` and
  parent references stay valid; only fingerprints are rewritten. This is why counterexamples equal those of
  an uninterrupted run.
- Spilled archive segments are read a whole segment at a time into a temporary cache (`SegCache`;
  contiguous blocks share a read); reading a segment still pending a write copies or waits instead of
  loading it into memory. New archives written by `transcode` spill as they are written.
- Archive cost is about 13-75 B per state (15 B typical) against about 180 B for object retention, so a
  1 GiB allowance holds roughly 7x10^7 states before spilling.
- **Liveness edges** carry old-layout fingerprints (§8.3).

## 7. Trace log (`explore/tracelog.rs`)

One log per worker, a `SpillVec<[u64; 2]>`: 16 B per distinct state, `(parent LogRef, fingerprint)`, in
1 MiB blocks (no doubling reallocation). `LogRef` is a 16-bit worker number plus a 48-bit index. Under
pressure (stage 2) full blocks go to disk at fixed offsets; memory keeps the tail block. Reading entry i is
a page read, so rebuilding a counterexample takes at most depth random reads before re-executing the model
along the fingerprint chain. Under VIEW/SYMMETRY the chain identifies classes: iterative depth-first replay follows real successors, backtracking over matching initial states and successors until the last state or step violates the reported property. Its depth is bounded by the log, independent of enumeration order, and successful searches pay no reconstruction cost. Disk blocks are not compressed (they need random access). After recover, old
workers' logs stay readable under their old numbers and new workers start at unused numbers.

## 8. Liveness edge log and graph

### 8.1 Recording edges during BFS

With temporal obligations the search records the behavior graph while it expands (design.md §7.4): for
each expanded in-model state the workers already have all successors (including duplicates and states cut
by constraints), so the action atoms, `EnabledVia` (including cut edges, as TLC evaluates ENABLED by the
spec) and the stuttering self-loop are computed in place; no second exploration exists. Each worker writes
an **edge log** (`explore/edges.rs`, columns in `SpillVec`s: source fingerprint column and metadata column,
with bit-pattern dictionaries deduplicated per worker and merged at the end). The log spills at stage 3.
With SYMMETRY/VIEW the target fingerprint is the canonical one. If the search stops early on a safety
violation, the log is discarded.

### 8.2 After the search: CSR graph

Sources are numbered by worker order and log order; a fingerprint-to-id open-addressing table
(`tlx_base::hash::FpMap`; `tlx_live::Csr`) translates targets; the CSR (`off`, `tgt`, edge pattern ids,
actions, state pattern ids, id-to-fingerprint) replaces a stored graph of states. Counterexample states are
recovered by re-executing from an initial state along the path, matching fingerprints
(design.md §7.4). This costs about 170 B per state against about 1260 B for a graph that stored
states. Both passes over the edge log read blocks from disk if they spilled, with read-ahead; the second
deletes blocks after reading.

### 8.3 Interaction with layout-miss resume

Edge-log fingerprints belong to the layout current when they were recorded. When a resumed search starts at
level L, the edges of levels before L are discarded and, after the search, the archive states of those
levels are re-expanded in parallel with the new model, recording only edges (no dedup, no queueing;
`resume::record_archived`); the blocks before the resume point are kept as a shared copy at resume time, so
dropping the archive afterwards does not matter. Printing is suppressed during re-expansion
(`Effects::replaying`) and the re-expansion runs on temporary threads so `TLCSet` registers of the search
are not touched; file-writing side effects such as `CSVWrite` repeat. If an atom evaluation fails with an
error that would interrupt the search (`Effects::interrupts`: a layout miss, including materialized
definitions) the search stops at that state and resumes; other errors stop edge recording and the first one
reaches liveness through `Report::live_error` as an evaluation error.

### 8.4 VIEW/SYMMETRY

With several concrete states per fingerprint TLC's verdict depends on which concrete state is evaluated, so
tlx replays TLC's algorithm: after the search it runs one more BFS in TLC's order with events streamed into
the products of all properties (`tlx_live::ConcreteChecker`; design.md §7.4). Memory is bounded by the
current and next level (released in blocks), the current event, 8 B per expanded concrete state (origin and
successor index; counterexample states are recovered by re-execution), the fingerprint-to-node table and the
products (about 32 B per node, 16 B per edge, interned bit sets). On one large model this cut the peak from
5.5 GB to 2.1 GB and liveness time from 9.3 s to 4.0 s.

### 8.5 Not done

An on-disk graph for state spaces whose CSR does not fit (external sort of edges, nodes in memory, edges
read on demand) is not implemented; liveness reports the memory error instead (§2.4).

## 9. Checkpoint and recover (`explore/checkpoint/`)

### 9.1 When

`-checkpoint MIN` writes a checkpoint at the first level boundary after MIN minutes; default 30 minutes as
in TLC, `-checkpoint 0` disables. A run that ends sooner writes nothing and creates no metadir. The check
at a boundary is one clock read, so default runs are unaffected. Checkpoints are taken **only at level
boundaries**: with several workers at the barrier after the leader installed the next level (when one
worker expands narrow levels alone, a due checkpoint ends that stretch so all workers meet at a barrier),
with one worker between two levels. At that moment the next level is empty, the current level is
completely queued and no worker holds a block, so the queue writes only the unclaimed blocks of the
current level. Mid-level checkpoints are deliberately not implemented: they would need per-list claim
positions, remainders of partially claimed blocks, a half-expanded state, written next-level blocks and
the VIEW/SYMMETRY candidate buffers, all to serve only a level longer than the interval; the cost of not
having them is that such a checkpoint is postponed to the end of that level.

### 9.2 Protocol and contents

At a checkpoint level boundary every worker publishes its appendable history shard to the search directory.
A barrier makes this a complete snapshot before any checkpoint file is written. Shard IDs remain stable
across recoveries; the directory also holds shards left idle when recovering with fewer workers. Trace
reconstruction and liveness graph construction consume the same directory at the end of the search.

The leader (or the single worker) decides, creates `checkpoint.tmp`, lists the shared files
as tasks (every disk run of the fingerprint set, segments of the current table of at least 2^16 slots and
at most two per worker, each queue list) and sets `now`; after the publication barrier each worker writes its assigned history
shards (trace log, edge log header and columns), including idle shards, and its own archive part
(as re-encoded blocks with depth), register snapshot and out-degree histogram and then takes shared files from the task list until none is left; after a
second barrier the last arriving worker writes the model files and the manifest and commits.

| File | Contents |
|---|---|
| `MANIFEST` | format version (3; older versions are refused), identity (key/values from the CLI), previous worker count, history shard count, level, counters (initial generated/distinct, generated including `extra_generated`, distinct, queue length, depth), out-degree histogram, flags (BFS positions present, archive complete, edges recorded), words per state, fingerprint set sections, queue files, streams and their segments, a file table with sizes, model file name, worker and main-thread snapshots, `-coverage` counters |
| `fpset-run-<id>`, `fpset-<p>` | each disk run is a section (ascending); the current table is cut into ascending sections that follow each other; the old table is a copy of the newest run and is not written |
| `queue-<l>` | unclaimed blocks of list `l` in claim order: XOR records for encoded models, `Persist` bytes otherwise; with VIEW/SYMMETRY and several workers each carries its BFS position |
| `trace-<id>.<n>`, `edges-<id>-fps.<n>`, `edges-<id>-meta.<n>`, `edges-<id>` | history shards by stable ID, independent of worker count; append-only stream segments (`.<n>` = new part of the n-th checkpoint) and the edge-log header |
| `archive-<w>.<n>` | each current worker's archive, as append-only stream segments |
| `model-strings`, `model-shapes`, `model-dyn` | string intern table; compiled mode's shapes and speculation state (per variable and materialized definition: shape, miss counts, fallbacks, attempt); Dyn interner snapshot |

Every file is framed (magic, format version, file kind, build id, per-block checksums, end marker) and the
manifest records every file's size, checked when opened. Runs of the live spill directory are not
referenced: they are hole-punched during rotation and merging, so a checkpoint needs its own copy.

**Commit protocol** (`io::durable::DirCommit`: `begin`, `commit`, `abort`, `roll_forward`): `fsync` every
file, then fsync the directory and issue one `F_FULLFSYNC` (macOS), rename `checkpoint` to
`checkpoint.old`, `checkpoint.tmp` to `checkpoint`, fsync the metadir, delete `checkpoint.old`. One device
flush covers all earlier per-file fsyncs because it flushes the whole device cache, while the order stays
the same: all data reaches the device before the publishing rename. Per-file full syncs cost about
2.4x more in total (8 checkpoints of a 3.4M-state model: 0.9 s against 0.38 s). The renames are done under
`io::durable::COMMIT`, which the signal cleanup takes first, so Ctrl-C never sees a half commit; if the
process is killed between the renames only `checkpoint.old` exists and recover accepts it. A failed write
only warns ("The checkpoint failed (the run goes on)") and removes `checkpoint.tmp`; the previous
checkpoint stays. TLC's messages 2195-2198 are printed.

**Incremental checkpoints.** After a checkpoint commits, the stream segments and run files it wrote are
recorded (`CkptRun::prev`). The next checkpoint hard-links still valid previous segments (the stream is
append-only, so an old segment remains a prefix) and run files of the same `<id>` and writes only what was
appended (`SpillVec::iter_from`); if linking fails the stream is rewritten. Edge-log columns are
append-only and the header is rewritten. For eight checkpoints of a 9.9M-state model this cut the bytes
written from 2.0 GB to 0.76 GB (1.27 GB linked) and the time from 3.3-4.3 s to 1.5-1.9 s. `-stats` reports
bytes written and linked. Parallel writing of the shared files helps less on macOS, where per-file syncs
queue.

### 9.3 Recover

`-recover DIR` takes DIR as the metadir (taking its lock first and deleting `.spill` files of the killed
process), checks the identity and refuses with a list of what differs (exit 255): the identity contains the
execution tier, checksums of all module files and the cfg, the deadlock option and `-seed`, and a build id
containing a hash of the executable, so only the same tlx binary can recover. Missing files and size
mismatches are refused on open; checksum mismatches stop at the read with `Outcome::Io`; in both cases the
checkpoint is kept (`DirHold::keep`).

- **Counts**: the recovered search takes the manifest's generated, depth and out-degree histogram as base,
  so counts, depth, verdict and counterexample length equal an uninterrupted run. TLC does not restore its
  generated count (see compat.md).
- **Worker count may differ**: old trace logs return unchanged (`LogRef` stable); extra new workers start
  with empty shards, missing ones leave read-only shards. Workers continue the trace and edge logs of
  their leased shards; every subsequent checkpoint includes the full directory. The archive goes to
  worker 0; register snapshots map by worker index and the main
  thread's registers are restored too (so `TLCSet` in Init is not repeated). With one worker the expansion
  order equals the uninterrupted run.
- **Fingerprint set**: the sections are ascending. If the current table can hold all fingerprints within
  half the budget, it is first sized to twice the total and the fingerprints inserted (insertion order does
  not change the layout; growing while inserting an ascending stream would pile everything by high bits into
  the front of a small table and create a gigantic cluster; this took 192 s against seconds when first
  tried). Otherwise, with a disk tier, each section becomes a disk run directly (`FpSet::add_run`) and the
  table starts empty, as after a rotation. Without a disk tier (`-spill off`, `-fpmem`) it reports a full
  set.
- **Queue**: encoded states go into worker 0's compressed blocks without decoding (`Local::push_words`),
  under the memory budget as they are read (`relieve` and `Local::spill` per chunk, as for the archive).
  With BFS positions and several workers they are queued in the order read and `Positions::of_places`
  gives each its recorded position (a state's position is looked up by its trace-log entry, not by its
  place in the queue); with one worker, whose order of expansion is BFS order, they are decoded and sorted
  by position first, the whole level held at once. Either way representatives are chosen in BFS order
  whatever the worker count.
- **Liveness** uses the recorded edges, no re-exploration; a checkpoint written by the same binary always
  contains them when there are temporal properties and no VIEW/SYMMETRY.
- **Compiled mode**: the CLI restores the string table before parsing; the driver restores the Dyn interner
  and the speculation state, skips the pre-run and continues from the checkpoint's attempt. The generated C is
  identical so the cache hits. A later layout miss resumes from the (restored) archive when it is
  complete, otherwise restarts from scratch.
- **Side effects**: the run re-expands from the checkpoint's level, so `Print` output and file writes after
  it happen again (a killed process's earlier output cannot be deduplicated); registers come from the
  snapshot (compat.md).
- **Metadir lifecycle**: on normal exit the checkpoint and the directory (and an empty `states`) are
  removed. On SIGINT/SIGTERM a committed checkpoint is kept (only spill files, lock and `checkpoint.tmp`
  go) and `-recover DIR` is suggested.

Test knobs: `TLX_CHECKPOINT_SECS`, `TLX_CHECKPOINT_STATES`, `TLX_CHECKPOINT_ABORT=n` (exit 134 right after
the n-th commit without cleanup, as if killed). Rough cost: about 1 GB/s of writes during which workers
wait at a barrier, 24 B per distinct state (fingerprint plus trace log), plus archive (10-40 B) and edge
log (about 100 B on a liveness model); recovering 10M states takes well under a second.

## 10. Disk layout and I/O layer (`io/`)

```
<metadir>/                 default <spec dir>/states/<yy-MM-dd-HH-mm-ss> (as TLC); created on first use
  LOCK                     flock(LOCK_EX|LOCK_NB): a second process on the same directory is refused
  fpset-<n>.spill          runs of the fingerprint set (§4.2)
  queue-<n>.spill, archive-<n>.spill, trace-<n>.spill, edges-fps-<n>.spill, edges-meta-<n>.spill   block stores (§5-§8)
  checkpoint/              committed checkpoint (§9); checkpoint.tmp, checkpoint.old during commit
```

**Directory** (`io::Spill`, one per run, created by the CLI and shared by all searches, restarts and
liveness): `-metadir` if given (created if needed, removed afterwards, only own files and `LOCK` deleted);
otherwise `<spec dir>/states/<time>` (suffix `.1`, `.2` on a clash), falling back to the system temp
directory `tlx-states/<time>-<pid>` if the spec directory is not writable. It is created lazily on the first
`Spill::store`; the last `BlockStore` released removes it, so cleanup does not depend on destructors
(the CLI exits with `process::exit`). `-cleanup` is accepted and ignored. A killed process leaves the
directory behind.

**Block store** (`BlockStore`, one file `<name>-<n>.spill`):

- `append` reserves an offset with `fetch_add` and `pwrite`s; many threads append concurrently. A
  `BlockRef` is (offset, length, one 32-bit checksum per 4 KiB page, kept in memory, ~0.1% of the data).
- `read`/`read_into` verify all pages; `read_range` reads and verifies only the pages touched (a 16 B
  trace-log read is one page). A mismatch reports "the spill file X is corrupt: checksum mismatch at
  offset N".
- `delete` returns accounting and punches holes for whole pages (`F_PUNCHHOLE` on macOS, `fallocate` on Linux).
- macOS files use `F_NOCACHE` (so "freeing memory" is not just moving data into the file cache), except
  fingerprint set runs (`Spill::store_cached`), which are read randomly and then mapped. Linux spill
  files go through the page cache. Dropping their pages on Linux was measured and rejected (16 workers on
  a 30 GiB cloud machine with a ~140 MB/s disk): for all spill files (write behind with
  `sync_file_range` and `POSIX_FADV_DONTNEED`) MultiPaxos_MC with `-maxmem 685M` read back 6.6 GB of
  queue and candidate segments the page cache had served before and took twice as long; for the
  archive and logs only, cf1s_folklore_N5 took 3-8% longer, since the writer then waits for the disk
  where the page cache absorbed writes (some to files deleted before write-back), while the page-cache
  reads it saved in a control group of 3.3 GiB (0.18 GB) bought no time back.
- Asynchronous: `Spill::write_async` (bounded queue of 16 blocks: producers faster than the disk wait;
  data stays readable until written via `Pending::with_data`; a failed write keeps it in memory) and
  `Spill::prefetch` (background reader). Both threads start on first use.

**`SpillVec<T>`** is a chunked append-only sequence of fixed-size values (chunks of 1 MiB by default,
`TLX_SEG_BYTES`; the first grows on demand). Chunk states `Mem | Pending | Disk`; `spill` hands full chunks to
the writer, `poll` turns finished writes into `Disk` and frees memory, `get`/`set`/`iter`/`drain`/`iter_from`
read back (sequential reads prefetch the next chunk; `drain` deletes chunks after reading). The trace log
and edge logs are `SpillVec`s.

**Space and errors.** Before each `append` the `-maxdisk` total (decreased on delete) and the filesystem's
free space (`statvfs`) are checked. Every I/O failure (write failure, no space, `-maxdisk`, read failure,
checksum mismatch) is recorded in `Spill` (the first wins) and the search ends with `Outcome::Io`: workers
check `Spill::failed` (one atomic read) at the 1024-state tick, `explore` checks once more at the end, and a
read failure while rebuilding a counterexample also becomes `Outcome::Io`. The CLI prints
`Error: The search stopped: <message>` and exits 255 (a resource error, like a full fingerprint set), with
the file or directory, the cause and a hint (`-maxdisk`, `-maxmem`, `-metadir`). `SpillConfig::fail_after`
(unit tests only) fails writes after N bytes.

**Pressure interplay.** Stages 2 and 3 are set by flags the workers poll (`spill_logs`, `spill_edges`):
workers write full trace-log and edge-log blocks at their next tick and every new full block after that.
With `-spill always` both flags are set from the start and the unfilled last block is written when a worker
ends, so counterexamples and liveness graphs are always read back from disk.

**Tests.** `io/tests.rs` (round trips, checksum detection, `-maxdisk`, injected write errors, concurrent
`append`, async write and prefetch, directory naming and locking), `fpset/tests.rs`, `queue/tests.rs`,
`crates/tlx-runtime/tests/{spill,queue,fpset_disk,checkpoint}.rs`, and spec tests that run under
`TLX_SPILL=always TLX_SEG_BYTES=4096` (see [testing.md](testing.md)).
