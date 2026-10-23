> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Root reentry generic anchor reflections

**Neither tested implication has a nonvacuous antecedent in this domain.** All 1,536 even-tail shadows are nonloss, so there is no reflection counterexample and no losing-shadow reflection instance. This is bounded evidence only; it establishes neither a uniform reflection nor uniform anchor nonloss.

The tests are exactly:

- A: every `T⊆[8,18]`, `U={2,3,4}∪T`, even `sum(T)`: query `V(U,7)` and, when it is LOSS, test `V(U,3)≠LOSS`.
- B: every `T⊆[9,18]`, `U={2,3,4,7}∪T`, even `sum(T)`: query `V(U,8)` and, when it is LOSS, test both `V(U,2)≠LOSS` and `V(U.erase(2),4)≠LOSS`.

All values use the active player's deficit perspective directly. The erased-2 target is a separate state; it is not treated as the result of playing 2 from deficit 2. All counter magnitudes are retained. The unmodified frozen `seven_pairs/slots.hpp` handles at most14 supplied labels; its initial deficit is7 for A and8 for B, including empty-tail controls. No interval table was built.

| Family | All tails | Even tails queried | Odd tails skipped | Shadow LOSS | Shadow DRAW | Shadow WIN |
|---|---:|---:|---:|---:|---:|---:|
| A | 2,048 | 1,024 | 1,024 | 0 | 561 | 463 |
| B | 1,024 | 512 | 512 | 0 | 234 | 278 |

Every one of the 3,072 tail indices and its parity is independently audited. The largest support actually queried has13 counters, because each full14-counter tail has odd sum and is skipped. Targets outside the controls below were not queried, since their LOSS antecedent is false. The complete JSON distinguishes unqueried targets with `null`; it does not assert their nonloss.

Every contiguous prefix `T=[8,N]` for A or `[9,N]` for B with even tail sum was also queried directly at every target, including empty tails. These parity-eligible endpoints are exactly those with even triangular N. No additional root eligibility condition was assumed.

| Family | Endpoint N | Shadow | First target | Erased-2 target |
|---|---:|---|---|---|
| A | 7 | WIN | DRAW | — |
| A | 8 | WIN | DRAW | — |
| A | 11 | DRAW | DRAW | — |
| A | 12 | WIN | DRAW | — |
| A | 15 | DRAW | DRAW | — |
| A | 16 | DRAW | DRAW | — |
| B | 8 | WIN | DRAW | WIN |
| B | 11 | DRAW | DRAW | DRAW |
| B | 12 | WIN | DRAW | DRAW |
| B | 15 | DRAW | DRAW | DRAW |
| B | 16 | DRAW | DRAW | DRAW |

All11 contiguous controls, with all27 shadow/target queries, received independent literal-score replay through `verify.absolute`. All passed. This literal replay scope does not include every generic tail shadow. No failing target exists, so there is no failing-target first-move set or witness reply replay to retain.

`root_reentry_reflection_results.json` retains all1,536 even cases and all1,536 odd skipped tails, family counts, every contiguous control, and27 literal replay records. Source, logs, exact command arrays, command/output hashes and resources are retained under the same prefix; `root_reentry_reflection_manifest.json` verifies all artifacts and the frozen solver/literal source hashes.

External jobs: compile0.547s, probe1.093s (internal query timer0.144s;5,033,738 explicit-slot states visited), literal replay0.390s. Peak compiler RSS135,610,368 bytes, probe2,375,680 bytes, literal32,784,384 bytes. All jobs stayed below30s/512MiB. No N/tail expansion or edits outside the new prefix occurred. No claim about a counterexample to actual contiguous root Q_N or conjecture C follows from these generic finite tests.
