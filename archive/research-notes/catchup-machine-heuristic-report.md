> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Our proof-guided heuristic-search pilot

Implemented and run a restricted heuristic loop using the existing verified
Catch-Up compiler. The selected policy fuses a branch and its two jumps into one
conditional jump. The resulting `CatchUp.Machine.BranchCryptid.M` has exactly
**1,319,242,705,832 states**, including initialization, with a kernel-checked
blank-tape theorem `Halts M ↔ ¬ Search.Conjecture`. The original, shared, and
direct-continuation machines remain unchanged. This is a reduction of
58,334,248,960 states (about 4.23%) from the preceding direct machine.

This is our own small design, not Winger's undisclosed code. It is a working
grammar-based search with a formal acceptance gate. It does not yet invent new
operators, call an LLM, invoke Aleph, maintain an evolutionary population, or
implement a compact tape-program interpreter. The machine remains enormous;
C remains unresolved.

## Executable loop

`search.py` generates policies, scores them, refines the candidate set using
counterexamples, and submits surviving candidates to Lean. Its 16 policies vary
four Boolean choices: read the actual head, keep the actual store, fuse the
branch, and swap its targets. The first three cheap candidates are rejected by
concrete truth-table witnesses. Policy `1110` survives and receives a fresh
`decide +kernel` certificate. The initial incumbent is also kernel-certified.

The objective during search is the syntax-node cost of a 13-bit branch routine:
155645 for the baseline, 139261 for the selected rule. `branch_nodes` proves
the connection between this cost and actual compiler syntax. That local metric
is distinct from the separately proved complete-machine count above. Neither
metric measures runtime speed or formal-proof size.

Every counterexample, generated certificate source, Lean diagnostic, source
hash, selected policy, and proof status is retained. Checkpoints pin the source
and compiled dependency closure. The checker is built before searching; hashes
are checked after a configured proposer and before/after candidate certification.
Resume validates history and freshly kernel-checks the incumbent. Prior
unverified proposals are retried; a proof failure or timeout is never accepted
as correctness or certified exhaustion.

Default limits are 16 proposals and 120 seconds per invocation, 30 seconds per
child process, and 64 KiB of captured output per child. Incremental pipe reads
enforce the output cap. Processes are killed as groups on a cap. These are wall
time and captured-output controls, not a child RSS sandbox. The explicit local
proposer executable and installed Lean toolchain are trusted; its JSON reply is
untrusted and must match four Boolean fields exactly. No response can inject
Lean source or shell syntax.

The optional `--proposer-command-json` accepts an explicit argv list. That
command receives the incumbent, feasible policies, costs, counterexamples, and
recent feedback as JSON on stdin and returns `{"policy": {...}}`. It can wrap
an LLM, but this project has made no external model/API calls. The supplied
`proposer_example.py` tests the protocol locally. A general LLM proof generator
is outside this pilot.

## Why the certificate is sufficient

`BranchPolicy.check` evaluates all 16 Boolean predicates on both heads and both
stores (64 cases per policy). `check_iff` proves that passing forces the actual
head, actual store, and original polarity to be retained. This structural
classification is then used by `branch_correct` to prove equality of the whole
TM1 configuration for arbitrary alphabets, stores, predicates, destinations,
bit widths, and binary tapes. The lift is not an inference from finite sampling
over an arbitrary alphabet.

`BranchCompile` preserves support and proves global equality of TM1 step
functions. Its evaluator equality includes nontermination. The existing finite
numbering, Boolean conversion, alphabet simulation, sharing, and blank
initializer give both directions of source-to-machine halting equivalence.
`BranchSearch` connects the selected policy to the existing exact Catch-Up
counterexample search, including N=0. `BranchCount.state_count_eq` counts every
listed state, including duplicates, unreachable entries, stores, defaults,
initialization, and both physical phases. `scalar_count` replays the final
numeral in the kernel. `BranchCryptid` transports the finite type along that
equality and proves equivalence with the preserved direct and original machines.

The full 2,638,485,411,664-entry table has a total symbolic generator and a
roundtrip theorem. It is not fully serialized. The finite test machines have
534 and 498 states; their halting and looping behaviors and counts are proved,
and their complete tables are independently replayed in Python.

## Reproduce

From `research/catchup`, with the existing pinned Lean 4.27.0 / Mathlib package:

```sh
python3 machine/heuristic/verify.py
python3 machine/heuristic/search.py --output /tmp/catchup-policy-run
python3 machine/heuristic/search.py --output /tmp/catchup-policy-run --resume
```

Use a fresh output directory for a new run. Checkpoint contracts intentionally
reject changed sources or compiled modules. The verifier checks the default
strict build, fresh source replays, transitive axiom closures, source pins,
33 preserved source hashes, Python tests, a new search, resume, a deliberately
invalid kernel certificate, all 1024 exported policy observations, and complete
tiny tables plus a corrupted initializer. `HEURISTIC_SEARCH_PASS` is the success
marker. REVIEW.md (`REVIEW.md` in the historical layout) records independent criticism and gate closure.

benchmark.json (`benchmark.json` in the historical layout) records actual timings, memory scope, all new
supporting mathematics and code, inherited sources, compiled artifacts, and
hashes. Search generation, native calculations, table export and kernel checking
are separate costs. Interactive design was not comprehensively timed. The
initial successful kernel build is also retained in `kernel-build.json`/`.txt`.
No proof budget or dependency was upgraded. The inherited source-checked model
port and root Lean 4.35 integration boundary remain as before.

The completed production run returned `HEURISTIC_SEARCH_PASS`: all 18 recorded
commands exited 0, all seven runner tests passed, and all 32 requested axiom
closures used only the standard allowed trio. All 33 preserved-source hashes
matched. The deliberately invalid policy failed in Lean with exit 1 and was
rejected. The positive tiny machine halted after 69 transitions with the
expected final tape/head; the empty-input and corrupted-initializer instances
repeat full configurations with period 44. All 1024 policy observations matched
the independent Python implementation.

The search took 10.456s, resume with fresh certification 6.319s, and the fresh
full-count kernel replay 55.241s. Recorded command times sum to 148.300s;
the separate negative control and initial 62.978s kernel build are retained
separately. Peak individual-child RSS in the final replay was 23546101760 bytes
on macOS 26.6.2 arm64, 16 logical CPUs. The six new Lean modules contain 27524
UTF-8 bytes and 45 theorems, with 226622 reused local source bytes and 2085728
new compiled-module bytes. Auxiliary runner and exporter sources are separately
hashed and measured in the benchmark. These are upper-bound artifact sizes;
there is no demonstrated reduction in mathematical proof size or checking cost.

## Literature and next experiment

This design borrows evaluator cascades and feedback from
[AlphaEvolve v1](https://arxiv.org/html/2506.13131v1), cost-guided candidate search
from [STOKE](https://www.microsoft.com/en-us/research/publication/stochastic-superoptimization/),
and counterexample refinement from
[Solar-Lezama's synthesis lecture](https://people.csail.mit.edu/asolar/SynthesisCourse2020/Lecture10.htm).
Our grammar, checker, integration and proposer protocol were designed here.
Winger's [public reply](https://github.com/google-deepmind/cryptids/pull/7#issuecomment-6299490039)
reports a heuristic loop and formal feedback; it does not establish that he used
these libraries or this architecture. No OpenEvolve dependency was installed.

The next useful experiment is a richer candidate language for shared decoding
or tape layouts, with a similarly explicit correctness contract. The present
grammar shows that the loop and formal acceptance gate work on a real compiler
improvement. It does not demonstrate autonomous discovery of a new search
representation, a small Cryptid, a shorter mathematical proof, or a solution of C.
