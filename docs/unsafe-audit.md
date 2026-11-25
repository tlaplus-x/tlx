# Inventory of `unsafe` code

This is the audit of every `unsafe` block, `unsafe fn`, `unsafe trait`, `unsafe impl`, raw pointer,
`transmute`, unchecked index and lifetime-erasing thread-local in `crates/`, plus the FFI boundary
to generated C and the address-keyed caches that would misbehave if an address were reused. Keep
it current: new `unsafe` needs a relevant local safety argument and a reviewed file
entry below. `python3 scripts/unsafe_inventory.py` reconciles the register with source;
`doccheck.py` runs the same check.

**Summary.** The workspace has no `static mut` and no `ManuallyDrop`. `unsafe` falls into six
areas: the lock-free fingerprint set and its exclusive-access operations (`tlx-runtime`); the FFI
boundary to generated C and the JIT (`tlx-native`, `tlx-compile`); the append-only string interner
(`tlx-value`); I/O and OS calls (`libc`: `mmap`, `fcntl`, `statvfs`, signals, `sysconf`); byte
reinterpretation of plain-old-data; and lifetime erasure for scoped job and statistics callbacks.
Where an `unsafe fn` or `unsafe trait` is declared, the caller contract is a `# Safety` doc
section; `unsafe` blocks and `unsafe impl`s carry a `// SAFETY:` comment directly above them.
Tool results in [Miri](#miri) and [Tools](#tools) are historical reports, not
current-revision certification. File coverage and local contract review do not establish
absence of undefined behavior or execute those tools.

Status values: **doc** = invariant documented as `SAFETY`/`# Safety` and checked at the call paths;
**assert** = a runtime check or `debug_assert` backs it; **test** = a test exercises the contract;
**removed** = the `unsafe` that used to be here is gone.

## 1. Inventory

Locations name files and functions (line numbers drift).

### tlx-value, tlx-layout

| # | Location | What | Invariant relied on | Status |
|---|---|---|---|---|
| 1 | `tlx-value/src/intern.rs`: `write_entry`, `entry`, `Sym::from_id` | append-only segmented table, read without a lock | an entry is initialized once under its shard lock before publishing a `Sym`; `unsafe Sym::from_id` requires an existing published symbol; safe `Sym::try_from_id` locks every shard before checking NEXT, so it waits for allocated but unwritten ids; segment pointers use Release/Acquire | Safety contracts; concurrent interning and checked-publication tests |
| 2 | `tlx-layout/src/dynval.rs`: `lookup_unchecked`; `layout.rs`: `decode_unchecked`, `Layout::decode_state_unchecked`; `layout_tree.rs`: `LayoutNode::decode_unchecked`, `transcode_unchecked`; `permute.rs`: `apply_unchecked` | trusted raw words become `Value`/`Sym` | active Dyn handles originate in this process's `intern`, or tables restored in symbol-then-Dyn order, and are published through synchronization; unchecked recursive decoding preserves this contract for active child slots | unsafe raw entry points with Safety contracts; safe lookup/decode/permute/transcode reject invalid handles before materializing a value; `raw_handles` tests and Miri |

### tlx-runtime

| # | Location | What | Invariant relied on | Status |
|---|---|---|---|---|
| 3 | `fpset/table.rs`: `MappedBuf` (`zeroed`, `discard_bytes`, `Drop`, `unsafe impl Send/Sync`); `fpset/overflow.rs`: `alloc_demand_zero`, `free_demand_zero`, `page_size`, `Overflow` (`try_push`, `get`, `Drop`, `fixed_resident_bytes`, `unsafe impl Send/Sync`) | backing storage for open-addressing fingerprint tables (anonymous `mmap` with `MADV_HUGEPAGE` on Linux for `>= 1 MiB`, `alloc_zeroed` otherwise; `madvise` page reclamation on rehashed units; freed with `munmap`/`dealloc`) and lock-free demand-zero overflow storage (single demand-zero mapping for fixed caps, demand-zero segments for growing tables) | `MappedBuf` and `Overflow` uniquely own their allocations and expose shared access only through zero-valid atomics; `discard_bytes` is called only on completed rehash units that no thread touches again, rounded inward to OS page boundaries; `Overflow` publishes demand-zero segments via `AcqRel`/`Acquire` CAS, unmaps losing candidates untouched, and frees exclusively on drop | `# Safety` on `discard_bytes`, `discard_slot_range`, and `free_demand_zero`; doc on each block and impl |
| 4 | `fpset/table.rs`: `Raw64::slot`, `Compact::line`, `Table::fault_pages` and `Table::resident_bytes` (tests) | unchecked slot and 64-byte cache-line `Line` pointer arithmetic on the hot path; `mincore` page-residency query in tests | callers keep `i < n + OVERFLOW = len` and `g < lines = len.div_ceil(SLOTS_48)`: `home = fp * n >> 64 < n`, probes never wrap and stop at `len`, and inserts are refused (`Full`) at 90% load, far below `OVERFLOW`; `mincore` queries a page-aligned prefix of a live `mmap` with a matching output vector | `debug_assert`; doc |
| 5 | `fpset/mod.rs`: `UnsafeCell<Table>`, `UnsafeCell<Option<Box<Disk>>>`, `unsafe impl Sync for FpSet`, and the `unsafe fn`s `disk_mut`, `insert_exclusive`, `make_room`, `grow`, `grow_to`, `rotate`, `install_merge`, `drop_old`, `for_each_in_table_part`, `reserve`, `add_run` | `&self` methods read or replace the table and the disk tier | slots are atomics and runs are immutable `Arc`s, so shared use is read-only; replacing or changing the table or disk tier happens only under the **exclusive-access contract**: no other thread uses the set (except atomic counters like `len` and `old_bytes`) | `# Safety` on each `unsafe fn`; SAFETY on each `UnsafeCell` access and the `impl Sync`. High consequence if violated (use after free of a replaced table); no violating path known |
| 6 | `fpset/disk.rs`: page lookup | `slice::from_raw_parts` over a mapped page of fingerprints | the page holds `n` fingerprints, 8-byte aligned (`map_run`), within the live mapping | doc |
| 7 | `explore/mod.rs` (`install_merge`, `grow_to`, `rotate`, `drop_old` calls); `explore/checkpoint/write.rs` (`for_each_in_table_part`, `_exit` on a configured abort); `explore/checkpoint/recover.rs` (`reserve`, `add_run`) | calls into `FpSet`'s exclusive-access operations | every active worker is parked (or none runs) and the others hold no reference into the set; checkpoint and recover calls run before the workers start or at a level barrier | doc at every call site |
| 8 | `explore/safepoint.rs`: `JobFn` (`unsafe impl Send`), `Crew::broadcast` (`transmute` erasing a lifetime), `run_part` (raw deref) | scoped jobs on a worker crew | the pointee is `Sync`; the pointer is dereferenced only while the broadcast that owns it waits for its parts (each counted in `running`), so the closure is alive at every call; a panic in a part is caught and re-raised by the executor | doc |
| 9 | `live.rs`: `SOURCE` thread-local, `current`, `with_source` | `transmute` erasing the lifetime of `&dyn Source`; deref in `current()` | the pointer is installed only for the dynamic extent of `with_source(src, f)` and restored on return and on unwind (a guard-returning API that could be leaked or dropped out of order was replaced by this one) | doc; tests for nesting and panics |
| 10 | `io/mod.rs`: `unsafe trait Plain` (impls for `u8`, `u32`, `u64`, `[u64; 2]`), `as_bytes`, `as_bytes_mut` | reinterprets `[T]` as bytes | `T: Plain` has no padding and every bit pattern is a valid `T` | `# Safety` contract on the trait; SAFETY on each block |
| 11 | `io/mod.rs`: `localtime_r`, `statvfs` | libc calls on zeroed `tm` / `statvfs` | an all-zero value is valid; the path is a NUL-terminated C string; the calls write only the struct they are given | doc |
| 12 | `io/store.rs`: `F_NOCACHE`, hole punching (`punch_hole`), `BlockStore::map` (`mmap`), `Mapping` (`unsafe impl Send/Sync`, `bytes`, `Drop` with `munmap`), `sysconf` | OS calls on files the store opened; read-only mappings | descriptors come from files the store opened; hole-punch offsets and lengths are page-aligned; the mapping is read-only, only unmapped on drop, and `Mapping::bytes` asserts the range lies inside it | doc; `assert` |
| 13 | `io/durable.rs`: `sync_file` (macOS `fsync`) | `libc::fsync` on a valid descriptor | the descriptor is the open file's (the lock file uses std `File::try_lock`, the drive-cache flush std `sync_all`) | doc |
| 14 | `io/spillvec.rs`: `Iter::next`, `next_block` | `*self.ptr` and `*self.ptr.add(self.pos)` through a raw pointer into the current block | `ptr`/`len` point to the values of `cur` (a borrowed or owned block) and are refreshed only when the next block is loaded, so they stay valid while `pos < len` | doc on both derefs |
| 15 | `queue/codec.rs`: `put_raw`, `get_raw`, `put_xor`; `queue/reader.rs`: `Reader::next` | reinterprets `[u64]` as little-endian bytes (`from_raw_parts`), `copy_nonoverlapping`, `Vec::set_len` over reserved spare capacity; calls the `unsafe` `StateCodec::decode_trusted`/`decode_into_trusted` | little-endian targets only (the big-endian path is safe); the destination has exactly the words' bytes and does not overlap the source; exactly the bytes counted by `at` were written before `set_len`; a decoded record comes from the codec's encoder, or from a spilled segment whose bytes were verified against the checksums retained when the encoding was written (encoded-state contract below) | doc |
| 16 | `mem.rs`: `rss_bytes`, `physical_bytes` | `proc_pid_rusage` on a zeroed `rusage_info_v2` (macOS), `sysconf` | the flavor fills exactly that struct and writes only it; `sysconf` has no preconditions | doc |

### tlx-native, tlx-compile (generated code)

Contract, written on the module `tlx-native/src/native.rs`: loading native code is an
explicit unsafe trust boundary. `NativeLib::load` and `load_with` require the caller to
trust the code, dependencies, initializers, compiler, cache and path resolution.
`build::build` accepts arbitrary C; its content hash and atomic rename provide cache
reuse/publication, not authentication or an ABI proof. `dlopen` can execute initializers
before any metadata check, and calling `tlx_info` already requires its correct signature.
The loader reads only its version prefix before accepting the full metadata layout;
matching ABI/region/refop hashes detect incompatibility, not malicious code or invalid
pointers. Metadata and its string arrays must be immutable, readable and live with the
library. Entry points must obey state spans, callback signatures, call-scoped context
lifetimes and concurrency requirements. `NativeLib` owns the `Library` with the pointers.

All direct path-loader callers are reviewed in these files (rerun
`rg -n 'NativeLib::load|Self::load_with' crates`):

- `tlx-compile/src/enc/native.rs`: staged C builds consume only `CGen` output from verified
  IR and the corresponding region/refop tables; the VIEW build uses verified VIEW IR and
  its refop table. Both rely on the configured compiler/cache being trusted.
- `tlx-testkit/src/diff.rs`: the differential harness builds `CGen` output from verified
  IR with the same refop table and no regions, using a trusted test compiler/cache.
- `tlx-native/tests/native.rs`, `tests/bench_native.rs`: reviewed `COUNTERS` fixture with
  static metadata, two-word state buffers and no callbacks requiring tables. Refop
  rejection variants change only well-formed metadata and are never executed.
- `tlx-native/tests/mixed.rs`: reviewed `LIB` fixture's argument/result buffers match
  `table()`; version/count/hash rejection variants retain readable metadata. Its `saved`
  handle is touched only by the one single-threaded ended-call test; other entry points
  do not access it. Stale handles are checked by the host, never dereferenced by C.
- `tlx-compile/tests/mixed_cgen.rs`, `tests/jit_mixed.rs`: `CGen` output from verified IR,
  with the exact region table used by emission and host callbacks.
- `tlx-compile/tests/mixed_regions.rs`: reviewed hand-written `LIB` with `WORDS`-sized
  state buffers and argument/result slots matching `table()`.
- `tlx-compile/tests/exec_region.rs`: reviewed probe with two-word states and a single
  scalar input/output matching its host signature.

Every call has a local safety argument. Compile-fail doctests forbid safe path loading;
ABI, region and refop rejection tests use well-formed fixtures, without malicious-library
or UB probes. `loaded_library_keeps_code_and_metadata_alive` removes backing files and
build inputs, moves the sole library owner to another thread, then exercises Init, Next,
invariant and copied metadata. It proves positive keepalive behavior without invoking
pointers after their owner is dropped.

| # | Location | What | Invariant relied on | Status |
|---|---|---|---|---|
| 17 | `native.rs`: `NativeLib::{load, load_with}`, `strings`; caller files listed above | `dlopen`, `tlx_info` and symbol lookups, C strings | unsafe caller establishes trusted code and valid metadata before any version check; table checks reject incompatibility; owned `Library` keeps code/data alive | `# Safety`, local caller proofs, compile-fail and keepalive/rejection tests |
| 18 | `native.rs`: `check_len`, `NativeLib::{next_into, successors, invariant_*, action_property_raw, fingerprint, ...}` (`unsafe fn call`/`call_mixed`) | passes `s.as_ptr()` to C, which reads `words` words | `s.len() == words`, enforced by `check_len` with an `assert!` in release builds too (one compare next to an FFI call) | assert; test `short_state_is_refused` |
| 19 | `native.rs`: callbacks `emit_cb`, `error_cb`, `miss_cb`, `eval_cb`, `elems_cb`, `mark_cb`, `release_cb`; `mixed.rs`: `unsafe fn Args::new`, `Args::get` | `*mut c_void` to `&mut CallCtx`; `slice::from_raw_parts(state, words)`; reads of `tlx_arg` slots and encodings of the sizes in the region signature; result written to `out` | `cx` is the `CallCtx` of the current call; `state` has `words` words (or is NULL where allowed); the library was generated for the region table whose `(n_regions, regions_hash)` it reports (checked at load and on every call), so `args`/`out` match the signatures; mixed-mode handles carry an epoch checked against their arena slot (stale, released or forged handle: panic) | doc; a panic in a callback is caught (`catch_unwind`), the C call is stopped, and the panic is resumed after the C function returns (a panic unwinding into `extern "C"` aborts the process); tests `panic_in_emit_propagates` and `tlx-native/tests/mixed.rs` |
| 20 | `native.rs`: `NativeLib::from_entry_points` (`unsafe fn`) | builds a library from in-memory entry points (the JIT) | the entry points implement the ABI for these sizes and live as long as the keep-alive object | `# Safety` |
| 21 | `tlx-compile/src/jit/rt.rs`: all out-of-line helpers (`words`, `words_mut`, `memmove`, `memzero`, `eq_words`, `divn`, `pow`, `gcd`, `sorted_member`, `sorted_insert`, `sorted_add`, `sorted_op`, `subsets_init`, `subsets_next`, `order_indices`, `order_bit_indices`) | `unsafe fn`s and blocks dereferencing `i64` pointer arguments from Cranelift-generated code | same contract as the C `runtime.h` helpers: called only by JIT code, with pointers and sizes matching the encodings (states of `words` words, `tlx_arg` slots as the call site's signature describes them, `it` a `SubsetsIter` slot, `out` valid for the result) | module/per-helper span, initialization, alias and panic contracts; fresh-output and overlapping-input regression tests |
| 22 | `tlx-compile/src/jit/mod.rs`: `Keep` (`unsafe impl Send/Sync`, `Drop` with `free_memory`), entry-point `transmute`s, `fingerprint_fn`, the `from_entry_points` call | owns the JIT module and casts finalized function addresses to the ABI types | after `finalize_definitions` the module is used only to free its memory on drop (together with the library that holds the pointers); each finalized function has the signature of its ABI entry point; constants (`Statics`) are immutable | doc on each; JIT tests (`TLX_JIT=1 TLX_JIT_VERIFY=1`) |

`tlx-compile/src/encoded_order.rs` shares insertion sorting between initialized
host buffers and fresh JIT buffers. Its `indices_uninit` / `bit_indices_uninit`
accept `MaybeUninit<u64>` output: each iteration reads only the prefix written
by earlier iterations, and shifts copy initialized words. Initialized wrappers
preserve the exclusive borrow and equal `u64` / `MaybeUninit<u64>` layouts;
every write is initialized, including when malformed input causes a panic.
JIT adapters provide a disjoint output allocation of cardinality / universe
slots, without forming a `u64` reference before initialization. Fresh-output
ordering tests cover these paths under targeted Miri.

Trusted host decoding is additionally audited in `tlx-compile/src/exec/fast/`,
`enc/{model,mixed}.rs`, `enc/model/{checks,fingerprint,view,symmetry}.rs`, and `tlx-testkit/src/diff.rs`:
unsafe calls use the matching layout/program and encoder-produced state,
constant or region words, synchronized when crossing threads. Generated projection orbits
use a tuple layout with exactly the VIEW encoding's component shapes and offsets; the
existing permutation routine receives only words produced by that matching VIEW encoder.
Public raw
closure-executor entry points carry this obligation in their Safety contracts.
Runtime `queue/reader.rs` and `explore/order.rs` call trusted codec methods only for
encoder-produced records (or validated recovered records), as described above.

### tlx-front, tlx-cli, tlx-base

| # | Location | What | Invariant relied on | Status |
|---|---|---|---|---|
| 23 | `tlx-front/src/parse.rs`: `unsafe fn set_allocator`; call in `tlx-cli/src/process.rs` `init` | installs the program's allocator (mimalloc) as tree-sitter's | the four functions are one allocator's `malloc`/`calloc`/`realloc`/`free`, never null for non-zero sizes, aligned as `malloc`; called once before any parse and before the threads that parse exist | `# Safety`; SAFETY at the call |
| 24 | `tlx-cli/src/process.rs`: `mi_collect`, `mi_option_set` (the `extern "C"` block), `prctl(PR_SET_THP_DISABLE)`, `signal(SIGPIPE, SIG_DFL)` | mimalloc FFI and process flags | no preconditions (a plain integer option, a process flag) | doc on each |
| 25 | `tlx-cli/src/process.rs`: `block_termination_signals`, `spawn_signal_thread` (`pthread_sigmask`, `sigwait`, `_exit`) | block SIGINT/SIGTERM, then wait for them on a dedicated thread, clean up and `_exit(128 + sig)` | the signals are blocked before any other thread exists, so every thread inherits the mask and they are delivered only to the `sigwait`; `_exit` is called after the cleanup | doc |
| 26 | `tlx-cli/src/out.rs`: `now`; `tlx-cli/src/stats.rs`: `peak_rss`; `tlx-base/src/time.rs`: `process_cpu` | `localtime_r` on a zeroed `tm`; `getrusage`; `clock_gettime` | zeroed `tm`/`rusage`/`timespec` are valid; each call writes only its own live struct; `localtime_r` is thread-safe | doc |
| 27 | `tlx-base/src/stack.rs`: `bounds` | `pthread_self` with `pthread_get_stackaddr_np`/`pthread_get_stacksize_np` (macOS) or `pthread_getattr_np`/`pthread_attr_getstack`/`pthread_attr_destroy` (Linux) | plain queries about the calling thread; the zeroed `pthread_attr_t` is initialized by `pthread_getattr_np`, read only after success, and destroyed afterwards | doc on both platforms |
| 28 | tests: `tlx-cli/tests/signals.rs`, `tlx-cli/tests/checkpoint.rs`; `tlx-runtime/src/fpset/tests.rs`; `tlx-base/src/bytes.rs` unit test; `tlx-compile/src/jit/mod.rs` tests | `Command::pre_exec` restoring default signal dispositions, `libc::kill` to the child; calls of exclusive-access `FpSet` operations single-threaded; `MaybeUninit::assume_init` after full initialization; calls of JIT functions | async-signal-safe calls between fork and exec; the child is alive when signalled; no concurrent access in the test; the array is fully initialized first | doc |

### Additional OS, evaluator and store boundaries

| # | Location | What | Invariant relied on | Status |
|---|---|---|---|---|
| 29 | `tlx-base/src/stack/overflow.rs`; `tlx-base/tests/stack_overflow.rs` | alternate-stack mapping, signal registration, siginfo reads, fatal reporting | registration owns the mapping on its creating thread; restore the old stack before unmapping; failed restore retains memory; Release/Acquire publishes permanent atomic records; kernel siginfo is live for the handler; only async-signal-safe syscalls run there | local contracts; registration reuse and eight isolated fatal-child modes; the unrelated-fault fixture intentionally violates writable-address requirements in its child and is not Miri-safe |
| 30 | `tlx-eval/src/code.rs`: `try_arc_slice` | `MaybeUninit<Value>` tuple arguments | only the initialized prefix is dropped on evaluation error; successful construction reads each of the initialized `n` slots once; remaining storage is `MaybeUninit` | local contracts; tuple-key evaluation tests |
| 31 | `tlx-eval/src/builtins.rs`: named-register enumeration | raw symbol id to `Sym` | ids originate in interned symbols stored under the register mutex; synchronized publication precedes lookup | local contract; named-register tests |
| 32 | `tlx-compile/src/exec/refops.rs`: `RefOpTable::run`, `FromEnc`; `tlx-native/src/native.rs`: `ref_op_cb`, `ref_elems_cb` | argument/encoding slices and mutable output, store element pointers | verified-program table fixes arity, encoding shape and output span; inputs stay readable, aligned and initialized for the call; mutable output does not alias input and is initialized before borrowing; scalar results use raw writes; store elements stay live with the store; native callbacks catch panic before crossing C | local span/alias contracts; refop/mixed tests; checked store boundary below |
| 33 | `tlx-testkit/src/cli.rs`; `tlx-native/src/build.rs` (`terminate`, tests); `tlx-cli/tests/output.rs` | process-group cancellation (`kill(-pgid, SIGKILL)`, liveness probe `kill(pid, 0)`), pipe flags/ownership, waitpid, closed stdout | only fixture-owned children/groups/descriptors are touched: `build.rs` spawns the compiler shell with `process_group(0)`, signals `-pgid` only while its own leader is unreaped (the group ID cannot be reused meanwhile), and probes only PIDs recorded by its own fixture; pre-exec calls are async-signal-safe; two fresh pipe descriptors each acquire exactly one owner | local contracts; process cancellation/reaping and broken-pipe tests; `a_cancelled_build_kills_the_compiler_group_and_removes_its_files` |

The value-store implementation under `tlx-layout/src/store/` now forbids unsafe code;
it needs no unsafe-file row. Its checked API and symbol publication obligations
remain part of the [raw handle boundary](#raw-encoded-handle-boundary) review.

### Not `unsafe`, but audited for the same hazard (address-keyed state)

| Location | What | Why it is sound |
|---|---|---|
| `tlx-eval/src/interp/mod.rs`: `REGISTERS` thread-local; `tlx-eval/src/interp/local.rs`: `LOCAL` thread-local; `tlx-eval/src/memo.rs`: `TABLE` thread-local | per-thread `TLCSet` registers, per-thread constant copies and constant-level operator memo | keyed by `Interp::uid` (monotonic, never reused), not by the interpreter's address, so a later `Interp` allocated at a dropped one's address cannot inherit stale state |
| `tlx-eval/src/interp/local.rs`: `SymTable` | cache keyed by `Arc<str>` address | the keys are strings owned by the program, which the interpreter owns: no other live allocation can share the address |
| `tlx-compile/src/lower/analysis.rs`: `const_cache` | cache keyed by `Arc<ExprKind>` address | the value holds a clone of the `Arc`, so the address is not reused while it is a key |
| `tlx-eval/src/model/mod.rs`: `MEMOS` thread-local | state-definition memo keyed by (interpreter uid, state `Arc<[Value]>`) | the state `Arc` is kept in the entry, so its address cannot be reused while cached |
| `tlx-eval/src/model/liveness.rs`: `STEPS` thread-local | enumerated `<<A>>_v` action-atom steps from one source state | keyed by `(Arc<()>, Arc<()>)` generation tokens cloned from `LiveSpec` (mutations and clones allocate fresh tokens), a `Weak<Interp>` whose live `Arc` allocation prevents `Interp` address reuse without keeping a finished model alive, `level` and full `src` values |
| `tlx-eval/src/model/symmetry.rs`: `BagCache` (in `LEAST_BUF` thread-local) | candidate symmetry permutations for record-keyed function bags | keyed by monotonic `Group::id` and `Arc::ptr_eq` on `Arc<[(Value, Value)]>`; `BagEntry` retains a clone of the bag `Arc`, so the slice address is not reused while cached |
| `tlx-compile/src/exec/mod.rs`: `DEF_MEMOS` thread-local | state-definition memos for encoded current and next states | keyed by `Interp::uid`, `Arc::ptr_eq` on `Arc<Layout>` (cloned into `DefMemo` so the layout address cannot be reused) and the state's exact words |
| `tlx-compile/src/exec/memo.rs`: `MEMO` thread-local | pure `Interp` fallback and mixed-mode host-region memo keyed by IR node address and exact encoded inputs | scoped to `MemoScope::id` (monotonic `SCOPE_IDS`, owned by the model that owns the IR); `Memo::enter` clears `nodes` and `slots` whenever the scope id changes |
| `Binding::Name(ExprId, Env)` (`tlx-sema` arena, `tlx-eval`) | name bindings referencing HIR | no `unsafe`: see section 2 |
| other thread-locals (`tlx-value/src/fmt.rs` `EXPANDING`, `tlx-value/src/intern.rs` `Sym::new` `CACHE` verified against the append-only interner, `tlx-layout/src/store/mod.rs` `SYMBOLS`/`THAWED`/`ROOTS` keyed by `Sym` id or monotonic `Store::uid`, `tlx-layout/src/permute.rs` `DYN_MEMO` keyed by monotonic plan id, `enc/model/symmetry.rs` `ORBIT_BUF`, `enc/model/fingerprint.rs` `VIEW_BUF`, `live.rs` `ACTION`/`GENERATE`/`HAS_STATES`) | plain `Cell`/`RefCell` scratch buffers or monotonic-id caches | no reusable raw addresses |

### Checking the inventory

The marked table is the machine-readable file register. Each path is explicit,
relative to the repository root, and must contain a Rust `unsafe` keyword token.
The checker scans **all** `crates/**/*.rs`, including tests, build scripts,
untracked new files and inactive platform/feature branches. It rejects missing,
duplicate and stale entries, wildcard paths and missing review/exclusion reasons.
Run `python3 scripts/unsafe_inventory.py`; `python3 scripts/doccheck.py` includes
that check. The summary counts scanned files, unsafe-containing files, reviewed
entries and excluded entries separately (not unsafe blocks or executed tests).

The lexer skips nested comments, ordinary/raw/byte/C strings, character literals
and raw identifiers. Macro-body tokens count even if a macro is not expanded.
This is source-file coverage, not Rust expansion, type checking, a local-comment
linter or a proof that a safety argument is correct. Generated C, generated
OUT_DIR files and third-party dependencies are outside this Rust-source register.
The native trust-boundary review above covers generated C separately.

`reviewed` identifies a file whose contracts are covered by the indicated audit
area. `excluded` requires an exact file and a concrete reviewed reason; it stays
visible in the counts and becomes stale when its unsafe tokens disappear. There
are currently no exclusions. A new boundary within an already registered file
still requires local contract and audit-row review; file equality cannot detect it.

<!-- unsafe-inventory:start -->
| File | Disposition | Review / exclusion reason |
|---|---|---|
| `crates/tlx-base/src/bytes.rs` | reviewed | Initialized byte arrays or calling-thread stack queries (rows 27-28). |
| `crates/tlx-base/src/stack/overflow.rs` | reviewed | Alternate-stack and fatal-signal contracts (row 29). |
| `crates/tlx-base/src/stack.rs` | reviewed | Initialized byte arrays or calling-thread stack queries (rows 27-28). |
| `crates/tlx-base/src/time.rs` | reviewed | Process clock output struct (row 26). |
| `crates/tlx-base/tests/stack_overflow.rs` | reviewed | Alternate-stack and fatal-signal contracts (row 29). |
| `crates/tlx-cli/src/out.rs` | reviewed | Allocator, OS structs or isolated child signal operations (rows 23-28). |
| `crates/tlx-cli/src/process.rs` | reviewed | Allocator, OS structs or isolated child signal operations (rows 23-28). |
| `crates/tlx-cli/src/stats.rs` | reviewed | Allocator, OS structs or isolated child signal operations (rows 23-28). |
| `crates/tlx-cli/tests/checkpoint.rs` | reviewed | Allocator, OS structs or isolated child signal operations (rows 23-28). |
| `crates/tlx-cli/tests/output.rs` | reviewed | Pipe descriptor output span and unique ownership (row 33). |
| `crates/tlx-cli/tests/signals.rs` | reviewed | Allocator, OS structs or isolated child signal operations (rows 23-28). |
| `crates/tlx-native/src/build.rs` | reviewed | Fixture-owned child wait/reaping, and the process-group signal of a cancelled build that `start` spawned with `process_group(0)` (row 33). |
| `crates/tlx-native/src/mixed.rs` | reviewed | Native ABI, callback spans, lifetime and panic boundary (rows 17-20). |
| `crates/tlx-native/src/native.rs` | reviewed | Native ABI, callback spans, lifetime and panic boundary (rows 17-20). |
| `crates/tlx-native/tests/bench_native.rs` | reviewed | Native ABI, callback spans, lifetime and panic boundary (rows 17-20). |
| `crates/tlx-native/tests/mixed.rs` | reviewed | Native ABI, callback spans, lifetime and panic boundary (rows 17-20). |
| `crates/tlx-native/tests/native.rs` | reviewed | Native ABI, callback spans, lifetime and panic boundary (rows 17-20). |
| `crates/tlx-compile/src/enc/mixed.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/enc/model/checks.rs` | reviewed | Paranoid decoding of encoder-produced states, preserving published Dyn handle and matching layout contracts. |
| `crates/tlx-compile/src/enc/model/fingerprint.rs` | reviewed | Trusted decoding and permutation of encoded states for VIEW and SYMMETRY fingerprints (rows 17-22). |
| `crates/tlx-compile/src/enc/model/codec.rs` | reviewed | Trusted encoded state decoding, widening transcode and validated queue codec boundaries (encoded-state contract below). |
| `crates/tlx-compile/src/enc/model/symmetry.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/enc/model/view.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/enc/model.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/enc/native.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/encoded_order.rs` | reviewed | MaybeUninit insertion sorting reads only its initialized prefix; equal-layout initialized wrappers preserve exclusivity (generated-code audit). |
| `crates/tlx-compile/src/exec/fast/expr/interp.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/exec/fast/expr/interp_tests.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/exec/fast/expr/mod.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/exec/fast/mod.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/exec/fast/stmt.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/exec/refops.rs` | reviewed | Verified refop argument/result spans and alias rules (row 32). |
| `crates/tlx-compile/src/jit/mod.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/src/jit/rt.rs` | reviewed | JIT pointer spans, fresh-output initialization, alias rules and iterator initialization (row 21). |
| `crates/tlx-compile/tests/exec_errors.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/tests/exec_memo.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/tests/exec_region.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/tests/interp_capture.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/tests/jit_mixed.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/tests/mixed_cgen.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/tests/mixed_regions.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-compile/tests/regions.rs` | reviewed | Trusted encoded state, native/JIT entry points and reviewed fixtures (rows 17-22). |
| `crates/tlx-eval/src/builtins.rs` | reviewed | Initialized tuple prefix or published named-register symbols (rows 30-31). |
| `crates/tlx-eval/src/code.rs` | reviewed | Initialized tuple prefix or published named-register symbols (rows 30-31). |
| `crates/tlx-front/src/parse.rs` | reviewed | One compatible allocator installed before parsing (row 23). |
| `crates/tlx-layout/src/dynval.rs` | reviewed | Trusted active-handle provenance and checked alternatives (row 2). |
| `crates/tlx-layout/src/layout.rs` | reviewed | Trusted active-handle provenance and checked alternatives (row 2). |
| `crates/tlx-layout/src/layout_tree.rs` | reviewed | Trusted active-handle provenance and checked alternatives (row 2). |
| `crates/tlx-layout/src/permute.rs` | reviewed | Trusted active-handle provenance and checked alternatives (row 2). |
| `crates/tlx-runtime/src/explore/checkpoint/recover.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/explore/checkpoint/write.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/explore/mod.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/explore/order.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/explore/safepoint.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/fpset/disk.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/fpset/mod.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/fpset/overflow.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/fpset/table.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/fpset/tests.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/io/durable.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/io/mod.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/io/spillvec.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/io/store.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/live.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/mem.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/queue/codec.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/queue/mod.rs` | reviewed | Exclusive fpset access, scoped callbacks, mapped I/O and codecs (rows 3-16). |
| `crates/tlx-runtime/src/queue/reader.rs` | reviewed | Trusted decoding of encoder-produced queue records, checked against the checksums retained for spilled segments (encoded-state contract below; rows 3-16). |
| `crates/tlx-testkit/src/cli.rs` | reviewed | Owned process groups and descriptor flags (row 33). |
| `crates/tlx-testkit/src/diff.rs` | reviewed | Verified generated-code loader and trusted state fixture (rows 17-22). |
| `crates/tlx-value/src/intern.rs` | reviewed | Append-only symbol publication (row 1). |
<!-- unsafe-inventory:end -->

## 2. Notes on the larger designs

### Name bindings and the HIR arena (no `unsafe`)

An earlier design held `Binding::Name` as a raw pointer to a HIR expression; that type, its
`unsafe impl Send/Sync`, its constructor and dereference are gone. After name resolution, INSTANCE
substitution and level checking, `tlx-sema` gives each HIR expression an `ExprId` (`NonZeroU32`) in
the `Program`'s private arena (every `Apply`/`Builtin` and its arguments, LET definitions,
function bounds and bodies, ASSUME). Reading a `Name` binding requires `&Program` and uses checked
Rust indexing, so the result's lifetime is bounded by the `Program` and the binding. Creating or
copying a `Name` does not touch a shared reference count (avoiding cache-line contention between
workers); lazy values keep the program alive through their `Arc<Interp>`. `Expr::new` has no index:
expressions whose kind or span was rewritten after the copy, or that come from another `Program`,
fall back to an owning `Thunk` (`memo: None`, re-evaluating by name). `Program::expr_id` checks the
index range, `Arc` identity and span; the three creation paths (action parameters, plain deferred
errors, memoized-call deferred errors) all go through `bind_by_name`. Regression tests cover:
arguments adding no shared reference count, synthetic/rewritten/cross-program fallback, deferred
errors not being cached, using captured arguments after the synthesized `Apply` and the caller's
`Interp` are dropped, and complete indexing of nested HIR. The temporary de-duplication table used
while building the arena holds the old `Arc`s, so an address key cannot be confused by allocator
reuse; it plays no part in evaluation.

### Fingerprint set

Lock-free open addressing with linear probing over `AtomicU64` (`< 2^20` slots) and quotiented
64-byte cache-line `Line<AtomicU16, 10>` / `Line<AtomicU8, 12>` slots (`>= 2^20` / `>= 2^28` slots,
with a lock-free segmented `Overflow` store for displacements exceeding inline tag bits). The home
slot is `fp * n >> 64` (no wrap-around; `OVERFLOW` slots follow the `n` home slots), so slot and
line indexing is unchecked on the hot path (row 4). Inserts are refused at 90% load, so probe loops
terminate. During parallel growth, completed page-aligned chunks of the old `mmap` are reclaimed via
`madvise` once read (row 3). Replacing the table (growth, rotation to the disk tier, checkpoint) is
the exclusive-access contract of row 5; the explorer meets it by parking every worker at a safepoint
(rows 7 and 8). The load limits, quotienting and probing are described in `tlx-runtime/src/fpset/mod.rs`
and `tlx-runtime/src/fpset/table.rs`.

### Statistics source

`TLCGet("stats")` reads a `&dyn Source` from a thread-local whose lifetime is erased with
`transmute`. The scoped API `with_source(src, f)` installs the pointer only for the dynamic extent
of `f` and restores the previous one on return or unwind; safe code cannot leak or reorder it.

### Generated C libraries

The generated code is called with state pointers of `words` words; the length check is an
`assert!` in all builds. A panic in the host's emit closure cannot unwind through the C frames: the
callback catches it, returns `STOP`, and the caller resumes the panic after C returns. The
`unsafe impl Send/Sync for NativeLib` were redundant (all fields are already `Send + Sync`) and
were removed; the thread-safety contract is documented on the module.

### String interner

An append-only id-to-text table in power-of-two segments, read without locks. Writes happen under
the map's write lock, once per id, in id order, before the id is published. A reader holding a
`Sym` therefore always sees an initialized entry (happens-before through the map lock, or through
whatever synchronization carried the `Sym`, or its id inside a state word, to the reader's thread).
`dynval::lookup_unchecked` and the interpreter's named-register lookup call
`Sym::from_id`. The latter obtains ids from mutex-protected registers. Safe raw
symbol construction uses `Sym::try_from_id`; merely checking NEXT is insufficient
because an id is reserved before its entry is written.

### Raw encoded handle boundary

Safe `dynval::try_lookup` returns `None` for an invalid raw handle, including an
unpublished symbol id, unknown tag or noncanonical Boolean payload. `lookup`
panics on the same inputs. Safe shape/tree/state decoding validates active Dyn
slots first; sequence/set padding and absent map slots are not handles. The
Shape-based decoder and the precomputed tree decoder remain independent value
decoders. Safe permutation and transcode paths use checked lookup whenever they
materialize a Dyn value. Merely copying an invalid raw word does not create a
symbol, and subsequent safe decoding rejects it.

The value store applies the same checked boundary to `thaw`, `thaw_slot`,
`digest`, selection and comparisons. `try_thaw` returns `None`, infallible value
readers panic, and fallible operations reject invalid words. Only `thaw_slot`
accepts zero as the unassigned-slot sentinel. Node lookup checks the store id,
index and publication; store ids are never reused and exhaustion panics before
their 16-bit encoding wraps. Every node constructor validates child handles
before publication, so recursive readers cannot encounter a hidden forged child.
Store symbol conversion contains no `unsafe`: a thread-local cache retains only
`Sym` values obtained through `try_from_id`, keyed by the full, width-checked id.
The entire store module forbids unsafe code, including its child modules.
Its fast path therefore uses a validated type instead of an unchecked raw-symbol
contract. `raw_handles` covers malformed words only through checked APIs,
including publication races, foreign stores and valid scalar/composite round trips.

Trusted variants are explicitly unsafe and retain the original symbol decoding
path: no additional per-word checks or symbol-table locks. Their callers must
prove that active handles were produced by the encoder/generated code or a
restored table and reached the reader through synchronization. The closure
executor's public raw-state/region functions are unsafe for the same reason.
`EState.words` is inaccessible outside the crate; immutable inspection is safe,
while constructing from raw words requires `unsafe EState::from_words`.

`StateCodec::decode`/`decode_into` on `EncModel` (in
`tlx-compile/src/enc/model/codec.rs`) validate external handles.
The runtime uses unsafe `decode_trusted`/`decode_into_trusted` for in-memory
queue/candidate records produced by that codec's encoder. Spilled segments are
checked against the checksums retained with the original in-memory `BlockRef`
before trusted decoding (`corrupt_segment_fails_its_claim` tests refusal).
Checkpoint queue/archive words undergo the codec's `validate` at recovery before
entering a trusted queue/archive, after the symbol and Dyn tables are restored.
Resume archive decoding retains the safe codec path. A checksum stored alongside
external checkpoint content is not a substitute for handle validation.

**Residual model provenance assumption.** An `EState` must be used only with the
`EncModel` whose layout produced it. Mixing states across models is a logic error
that safe Rust types do not fully exclude: a valid scalar word in one layout can
be interpreted as an invalid Dyn handle in another. Debug builds attach a model
id and check safe model/codec entry points. Release builds omit both that field
and those checks, by design, to retain state size and hot-path instruction cost.
The checked raw boundary therefore closes arbitrary input for the intended
model, but does not establish a fully sound public cross-model state abstraction.
A future generative brand/lifetime shared by model and state could encode model
identity without release fields or comparisons; it would require restructuring
the runtime's generic state ownership and public model construction APIs.

## Miri

Miri (nightly, with the `miri` and `rust-src` components) was run over the pure-Rust crates that
contain `unsafe`: `tlx-value`, `tlx-live` and `tlx-runtime`. No undefined behavior was reported;
the only diagnostic is a benign "integer-to-pointer cast" warning inside the `parking_lot_core`
dependency, not tlx code. Commands (default isolation, no `MIRIFLAGS`):

```sh
cargo +nightly miri test -p tlx-value
cargo +nightly miri test -p tlx-live
cargo +nightly miri test -p tlx-runtime --lib -- --skip <the tests listed below>
```

A run of the three crates reported no undefined behavior. Miri runs roughly 1000 times slower
than native and cannot emulate `mmap`, `flock`, `proc_pid_rusage`, a panic crossing a pthread, or
platform pthread stack queries and alternate signal stacks, so the `tlx-runtime` run skips (`--skip`)
the tests below (the stack-guard module `stack.rs` and its `deep_recursion_reports_low_stack` test
moved from `tlx-runtime` to `tlx-base/src/stack.rs`, where native `cargo test -p tlx-base --lib`
runs them and Miri requires `--skip deep_recursion_reports_low_stack --skip borrowed_work_and_panics_cross_the_stack_thread`);
a skip is a limit of Miri, not a verdict about the code.

- tests using files, disk or FFI: `mem::tests` (this substring also filters `cache_mem::tests`,
  which has no `unsafe`), `io::tests`,
  `rotating_to_disk_matches_a_hash_set`, `sections_rebuild_the_set`, `rotating_without_the_old_table`,
  `a_large_table_written_in_ranges`, `a_failed_rotation_leaves_the_set_full`,
  `concurrent_inserts_while_rotating`, `concurrent_inserts_while_growing`,
  `spilled_records_give_the_same_graph`, `spilled_levels_read_back_in_order`,
  `concurrent_claims_of_spilled_segments`, `failed_writes_keep_segments`,
  `corrupt_segment_fails_its_claim`;
- tests too slow in memory (large fills, quadratic under Miri): `write_install_read_in_order`,
  `concurrent_claims`, `xor_blocks_compress`.

Heavy loops are reduced under `cfg!(miri)` (same code paths, smaller scale) in `tlx-value`
(`intern`, `arith_fp_fmt`, `order`, `ser`), `tlx-live` (`random`, `scale`), `explore::edges`,
`fpset::bloom` and the `fpset` table tests. Where reducing the scale would defeat the test, it is
`#[cfg_attr(miri, ignore)]` with a comment: `random::agrees_with_brute_force` (exponential brute
force), `tlx-base::frame::frame_round_trip_and_checks` and
`tlx-base::frame::frame_refuses_other_build` (`frame::build_id` hashes the executable; the tests
moved with the framing code out of `tlx-value`'s `ser` into `tlx-base`, alongside
`tlx-base/src/stack.rs`, which the three-crate run above does not cover), and `fpset::tests::watermarks` (filling to the 90%
watermark takes thousands of probe-heavy inserts). `grow_serially_up_to_the_limit` and
`grow_with_helper_threads` still exercise the rehash-and-swap path and the helper threads, growing
explicitly at low load.

Not covered by Miri (it cannot run them; audited by hand above): `io/` (`mmap`, files, `flock`),
`mem.rs`, `explore/checkpoint/` (files), `tlx-base/src/stack.rs` and `tlx-base/src/stack/overflow.rs`
(pthread stack-bounds queries, evaluation-stack threads and alternate-stack signal handling), and the
queue's disk and spill paths. `tlx-value` and `tlx-live` are covered in full. Miri did exercise the string
interner's append-only table (single-threaded and concurrent), the fingerprint table's
insert/probe/grow paths including concurrent inserts, the safepoint spin/park protocol, and the
`transmute` plus raw-pointer deref in `live.rs`.

## Tools

- **Miri**: see above.
- **Rust-side ASan** (`-Zsanitizer=address`): not run; Miri covers the pure-Rust crates and the
  generated C is covered by the build below.
- **ASan + UBSan on generated C**: `TLX_CC_SANITIZE=1` with `-compile`, 2-3 workers and the native
  code built synchronously (`TLX_NATIVE_SYNC=1`); command in [testing.md](testing.md) section 11.
  Run over the `tests/specs` models, also with `TLX_PARANOID=1`, and over corpus models with
  records as unlike each other as Bakery, Paxos, MultiPaxos, Disruptor and the sliding puzzles: no
  sanitizer report, and state counts equal to `corpus/out/tlx-compile.json` (except runs that stop
  at a violation, which depend on worker timing, and MCDieHardest, whose ASSUME requires one
  worker).
