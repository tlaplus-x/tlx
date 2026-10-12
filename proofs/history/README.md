# History feedback certificate example

`Feedback.tla` appends either `R` or `W` forever. `Seen` asks whether an `R`
occurred before any `W`; the retained variable `witnessed` receives that predicate
from the previous state. Once established, that witness stays valid even after
appending a `W`. Recomputing it from the final element set would be incorrect.

```sh
cargo build -p tlx-cli --release
./target/release/tlx check proofs/history/Feedback.tla -interp -optimize -noautosymmetry
```

The unbounded model completes with six reduced states. Adding `Safe` to the
configured invariants produces the genuine `<<"R", "W">>` counterexample.
A separate retained four-transition budget gives 31 concrete states versus 15
reduced states; this finite diagnostic does not constrain the history predicate.

Verify the actual standalone output path printed by checking:

```sh
python3 proofs/check_generated.py --lean /path/to/lean --negative /path/to/Optimization.lean
```

The five theorem audits cover the certificate, safety, safety with stuttering,
counterexample lifting and deadlocks. Four negative checks break accumulated
prefix results, guard feedback, transfer feedback and reduced observations.

Supported history predicates also work in guards, conditional resets and event
values. Their exact Boolean results are passed into otherwise history-free HIR
consumers. The proof equates indexed concrete predicates with summary predicates
before constructing successors; it does not assume their preservation.

Source/HIR lowering, semantic leaf interpretation, domain/totality analysis and
runtime execution remain trusted. Branch bounds and initialization must remain
history-independent. Next-state history reads, dependent binders, exact length
observations and unsupported prefix/index patterns still refuse the reduction.
