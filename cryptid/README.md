# The Catch-Up cryptid

The best fully verified construction in this snapshot has **388,819,712 states**, including blank-tape initialization. Its deterministic binary transition function is [CatchUp.Machine.RestoreShare.M](CatchUp/Machine/RestoreShare/Cryptid.lean).

The theorem `CatchUp.Machine.RestoreShare.halts_iff_not_conjecture` proves:

```text
Halts M ↔ ¬ CatchUp.Search.Conjecture
```

`Conjecture` quantifies over every relevant initial interval, including the empty game. The machine uses a two-way infinite binary tape, the all-zero starting tape and the initial state specified by the bundled machine definitions. Whether it halts remains open.

## Check it

This directory is a separate Lake package pinned to **Lean 4.35.0-rc4** (Lean commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`) and Mathlib `1f414401f69059aa7eead47b53ee40bd38455eeb`:

```sh
cd cryptid
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

The baseline and component roots are checked in separate Lean environments because they reuse some declaration names; the checking script handles both. Do not import the two roots into one file.

The source dependency closure is included. No unpublished local checkout, preloaded program tape, external solver result, or upstream conjecture proof is needed. The reused [Cryptids](https://github.com/google-deepmind/cryptids) and Chess compiler files are vendored under `Cryptids/`, retaining their original headers. This explains the presence of Chess modules: the Catch-Up machine reuses that verified interpreter and graph backend.

## Where the states go

| Component | States / data |
| --- | ---: |
| Shared template graph | 38,875,007 nodes |
| Post-lowering machine | 194,375,041 states |
| Binary body | 388,750,082 states |
| Initialization | 69,630 states |
| **Complete binary machine** | **388,819,712 states** |
| Program written during initialization | 34,815 bits |

These figures count the entire specified finite control, including nominal and unreachable states. `generated_states` and the type of `M` establish the total in Lean. `initializes` proves the 69,630-step initialization run. The transition function is a total finite generator; this repository does not serialize hundreds of millions of individual rows.

The proof composes the exact evaluator, counterexample search, source program, interpreter simulation, finite control, binary lowering and initializer. Both halting directions are required. [AxiomAudit.lean](AxiomAudit.lean) audits the final theorem, initialization, state count and the principal sharing lemmas.

## Smaller candidate

A **211,100,482-state design**, including four initialization states, has checked component contracts, including 92 switch/save/finish relocations and a successor relocation. It is **not a certified replacement**. Inherited-core preservation, full partial-program DAG simulation and the final end-to-end halting equivalence remain open. The public package also includes the checked component dependency closure through [CandidateComponents.lean](CandidateComponents.lean). The default build checks both the complete baseline and these local contracts; it does not assert a candidate halting equivalence. Earlier exploratory prototypes outside that closure are omitted.

A state count measures program size. The equivalence proof and any eventual halting or nonhalting proof must also be accounted for when discussing proof size. No minimum-state claim is made.

## Checked candidate components

The concrete contracts cover arbitrary valid data and caller frames, including the documented empty-input cases. They execute the actual copied routines and resume the specified continuations.

| Routine | Actual copies | Contract / relocation |
| --- | ---: | --- |
| Switch | 92 | [Relocation](CatchUp/Machine/Lowering/Relocation.lean) |
| Save input | 92 | [Save.Relocation](CatchUp/Machine/Lowering/Save/Relocation.lean) |
| Finish | 92 | [Finish.Relocation](CatchUp/Machine/Lowering/Finish/Relocation.lean) |
| Normalize successor input | 1 | [SourceSucc.Relocation](CatchUp/Machine/Lowering/SourceSucc/Relocation.lean) |

The successor-input contract hands off to a shared arithmetic increment instruction; it does not prove that redirected core's execution. The remaining integration obligations are substantive: preserve inherited core operations under hook redirection; compose all bank and core contracts into a full partial-program simulation; then prove both halting directions and connect them to the search.

The [machine-design notebook](../archive/research-notes/README.md#machine-design) retains earlier optimization, shared-decoder, interpreter, stack, word, dispatch and lowering reports, including unsuccessful proof approaches. Their component and historical machine counts have their stated scopes; the current complete-machine count remains the one at the top of this page.
