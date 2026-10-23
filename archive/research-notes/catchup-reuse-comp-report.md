> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Generic source composition and partial-program halting

Composition now has both a successful-result contract and a separate,
continuation-sensitive halting contract. All code reuses the preserved Cases
interpreter directly: **no new opcode, dispatcher or interpreter control state**.
The new support is three Lean files, rather than another copy of the interpreter.

For arbitrary partial source codes f and g, source membership is exactly
`result ∈ (comp f g).eval source ↔ ∃ middle ∈ g.eval source, result ∈ f.eval middle`.
The analogous domain theorem and the undefined-inner/undefined-outer corollaries
make no totality assumption. The literal pinned Mathlib `Code.eval` is used.

A `Layout` records the actual push/call instructions. Both complete target and
continuation words are generated at runtime. The first call runs g, returns to
the second literal pair, then the second call runs f on g's resulting list.
Calls may share a physical call instruction. `compose_run` proves the exact
summed transition count for arbitrary source/intermediate/output lists, arbitrary
address widths and arbitrary earlier frames. Both internal saved continuations
are popped by the real return routine; the earlier frames remain unchanged.

`ResultContract` quantifies over every successful source result and every frame
list. `comp_result_contract` lifts two such callee contracts through composition.
It is a forward simulation and is named separately from the halting contract.

`HaltingContract` says that actual machine halting at a callee entry is equivalent
to a source result followed by machine halting at its return boundary, with the
same frames. This is continuation-sensitive, not an assertion that a callee must
halt independently of its caller. `invoke_halts_iff` and `comp_halts_iff` prove
both directions. `comp_halting_contract` gives the modular constructor rule.
`embedding_respects` and `initialized_halts_iff` connect the already-paid binary
initializer to body execution in both directions. Finally `comp_blank_iff`
proves blank-tape machine halting iff partial source composition terminates,
conditional on the two actual callee HaltingContracts and a final halt label.
No source totality, arbitrary-callee correctness axiom or finite timeout is used.
This rules out unintended divergence for convergent source compositions under
those contracts, and unintended halting for divergent ones.

The concrete tail and zero-prime routines satisfy **both** contracts by their
existing arbitrary-list/frame transition proofs. `example_contract` and
`example_halting_contract` consume those premises for a returning composition.
`example_blank_iff` instantiates the initialized equivalence for the halting
example. These are concrete uses, not merely uninstantiated interfaces.

## Initialized binary example

Source `comp zero' tail` sends `[3,0,2]` to `[0,0,2]`. Reversing composition order
would return `[3,0,2]`, so this example detects that mistake. The instruction list
is `[push7 1,push3 2,call,push6 4,push5 2,halt,push0 8,tail,ret]`.
Changing the final halt to ret supplies the reusable callee example. Both calls
share instruction 2. Only the reversed source list and bank markers are written
by initialization; all four call operands are subsequently generated.

`M : Machine 67400 2` has **67,352 body states +48 initializer states =67,400**.
The kernel proves its complete **6,336-transition** blank-tape execution, with
source output `[0,0,2]`, empty frames and head home at halt. Empty input produces
`[0]` in **3,494 transitions**, using **67,356 states**. For every source list,
initialization plus the exact body run is proved, not just these examples.

The unchanged formula is `11292+4638L+462P+4D`, where L is instruction count,
P counts every literal-pool cell, and D is the initial data encoding length.
Here L=9, P=31 and D=11. Initialization, all runtime return storage, lookup,
unused allocated controls and every literal cell are counted. Table-generator
equality is kernel checked using the existing generic finite-row theorem;
native export and serialized table bytes are separate diagnostics.

## Reproduction and assurance

Run `python3 -B research/catchup-reuse/comp/verify.py --full` from the workspace.
It strictly replays all three sources and both auxiliary Lean modules, checks
all 39 theorem dependencies against only `propext`, `Classical.choice` and
`Quot.sound`, and preserves twelve previous snapshots (591 manifest records).
The old complete cryptid equivalence is preserved, with its existing axiom audit.
No unfinished upstream conjecture theorem, custom axiom, sorry or native-only
proof is introduced. The target remains downstream and no upstream file changes.

Lean remains 4.35.0-rc4, compiler c29b6dda4f7c20e3eeaa717c4e565663c5cfa364;
Mathlib 1f414401f69059aa7eead47b53ee40bd38455eeb; Cryptids source blobs
8fed07fa2981ecd96141303b0d8982116106f6eb. Original game Lean4.27.0/Mathlib
a3a10db0e9d66acbebf76c5e6a135066525ac900 remain separate. Pinned ordinary
imported objects are reused, not a full dependency rebuild or cross-version theorem.

Bounded diagnostics compare all 134,800 exported sample cells (129,030 present,
5,770 missing) to the preserved integer-key numeric transition reconstruction.
All **577 routine cases /81,638,860 transitions**, including **56 nested cases**,
and **seven blank-tape examples** pass, checking whole tapes, heads and states.
Tests include empty input, order-sensitive data, relocated addresses through
1,032, source word1,024, source length129 and earlier frame depth128.
All **fourteen** corruptions are rejected: initializer write/motion, target and
continuation generation, shared calls, both callees, return, premature halt,
and selected save/lookup/return transition deletions. The initial oversized
batch timed out at 120 seconds without a result; its receipt/log are retained
as Physical.first-attempt files. The reduced batch retains boundary coverage.
No timeout supplies any theorem premise or mathematical outcome.

Final strict Lean replay took **14.305s**, physical checking **102.454s**; peak
recorded Lean child RSS **3,814,227,968 bytes**, macOS26.6.2 arm64, sixteen logical
CPUs. Three core sources total **23,573 bytes /39 theorem declarations**, compiled
objects749,488 bytes; auxiliary objects91,904 bytes; helpers/table1,309,615 bytes;
artifacts1,701,004 bytes. The extension records29files and preserves591earlier
manifest records across twelve snapshots. Bounds are 120s/child, Lean-M8192 allocator (not an OS RSS cap),
16MiB Lean/1MiB physical output. Interactive proof/code-generation cost was not
instrumented and is excluded from reported checking times. All new supporting
source/object/helper/artifact bytes are recorded. No minimality claim is made.

The referee correctly distinguished the two interfaces: HaltingContract does
not logically imply ResultContract. Its initial wording was corrected; no theorem
or transition changed. All five Lean modules were replayed afterward, and the
Export.log/Audit.log bytes and physical evidence are identical. The superseded
candidate manifest is retained as benchmark.reviewed-v1.json; final records
refer to the corrected candidate, without another unnecessary numeric run.

Frozen benchmark SHA256:
`bbdac8698e8e8413b18ebfcf4bf9af4854200703a02af916c01621cb04068561`.

Fresh independent review **accepted** the corrected component. All five fresh
objects/logs match the final producer and all39axiom audits pass. The independent
model matches every134,800samplecell and the exact serialized table;173whole-tape
cases/12,232,462transitions, including34nested cases and six blank examples, pass.
All fourteen independent corruptions are rejected. It also independently checks
the source DAG inventory and the conditional literal-pool budget below.
All29current and591prior records, twelve snapshots and pins match. See
REVIEW.md (`REVIEW.md` in the historical layout), archived evidence (`review-evidence/README.md` in the historical layout) and
finalization.json (`finalization.json` in the historical layout). Natural-language referee acceptance is
criticism separate from the encoded kernel-checked claims and bounded diagnostics.

## Effect on the complete Catch-Up machine

The complete cryptid remains **388,819,712 states**, with its preserved
`Halts M ↔ ¬C`. The 67,400-state example is not a complete Catch-Up search.
No game outcome or counterexample was investigated in this constructor milestone;
C remains unresolved in this project.

The pinned complete source DAG has 204 nodes (kernel-checked row count). A syntax
inventory gives 77 comp, 92 cons, 23 branch, nine fix and one each zero/tail/succ.
This composition theorem therefore closes a heavily used constructor, and adds
a reusable reverse-halting proof interface. It does not yet instantiate all nodes.

There is no defensible date or session count for the main reduction yet. Remaining
substantial integration blocks are input preservation/copying and cons; literal
source succ (which projects to a singleton, unlike stack increment); fixpoint
simulation; and the full finite-DAG compiler/assembly and halting equivalence.
The existing case dispatch also needs its continuation-sensitive halting lift.
The complete compiler's actual L/P count is still unknown, so a reduction is not
yet established even as a numerical full-program candidate. Unary address literals
have a real control-storage cost: for example, a 1,000-instruction empty-input
program must have P≤831537 to beat the preserved baseline under this formula.
That is a conditional budget calculation, not a compiled-program state claim.

The highest-value next action is a **costed lowering of the actual 204-node DAG**,
with explicit implementation requirements for cons/copying and the remaining
constructors. Establish the complete L/P budget before investing in more isolated
demonstrations, then close the first missing constructor on that integration path.
A complete reduction is accepted only with the new end-to-end equivalence and
kernel-checked count; none of the component counts substitutes for it.
