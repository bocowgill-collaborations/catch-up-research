> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Dense tape layout: verified search result

`CatchUp.Machine.DenseCryptid.M` has exactly **313,357,716,212 states** and
kernel-checked blank-tape equivalences `Halts M ↔ ¬ Search.Conjecture` and
`Halts M ↔ Halts BranchCryptid.M`. Initialization is included. The saving from
the preserved 1,319,242,705,832-state branch-fusion machine is
1,005,884,989,620 states, about 76.25%. All four previous machines are preserved.
The resulting machine remains enormous. C is unresolved; this work proves no
new outcome of an original Catch-Up game.

## Mechanism and proof

The compiler's simulated alphabet consists of one Boolean marker and four
register symbols, each with five possible values (empty or one of four tokens).
There are 2*5^4 = 1,250 symbols. The preceding encoding used three bits per
register plus a marker: 13 bits. The new encoding uses the natural number

`marker + 2*(main + b*(rev + b*(aux + b*stack)))`,

where each register digit is in 0..4. Bits are stored least significant first.
`DenseAlphabet.decode_encode` proves the roundtrip for **every** radix b≥5 and
width n with 2*b^4≤2^n. Its proof uses division, remainders and induction on n;
it is not an extrapolation from finite tests. The selected layout b=5,n=11
satisfies the hypotheses. `encode_default` proves that blank symbols encode
as all zero bits, for arbitrary radix and width.

`DenseSearch` instantiates the existing generic `BranchCompile` compiler with
that layout. The existing step/evaluator simulation, support, numbering,
physical two-phase binary execution and initializer proofs provide both
directions of halting preservation. It then uses the exact, already verified
Catch-Up search. The target C includes N=0 and retains the literal reference
definitions; the unfinished upstream theorem is not a premise.

`DenseCount` proves the connection between a scalar cost calculation and the
complete actual finite enumeration. It accounts for the new 11-bit read trees,
11-step moves, 34-node write auxiliaries, all 1,250 possible writes, five stores,
repeated and unreachable support entries, defaults, both physical phases, and
the changed initializer. The final numeral is established with `decide +kernel`.
`DenseCryptid` reindexes the machine to that exact numeral and proves the
halting equivalences. Its total transition-table generator has a roundtrip
theorem; the full 626,715,432,424-entry table is not materialized.

## Search and failures

The new runner reuses the preceding bounded process/serialization runtime.
Its deliberately restricted language has 16 layouts: radices 4,5,6,8 and widths
10..13. The baseline incumbent is a valid 13-bit radix-eight layout. Local
branch syntax cost is the search objective, with a proved bridge to compiler
syntax. The complete machine count is a separate theorem. The objective falls
from 139,261 to 30,717 syntax nodes. This is neither a runtime benchmark nor a
measure of proof size.

The run retains three proposals and two diagnostic counterexamples:

* Radix four, width ten: marker/register tuple (0,0,0,0,4) encodes as 512 and
  decodes as (0,0,0,0,0). Digit four cannot fit in radix four.
* Radix five, width ten: (0,0,0,1,4) has raw code 1,050, truncated to 26, and
  decodes as (0,3,2,0,0). Ten bits lose high information.
* Radix five, width eleven passes and receives a fresh kernel certificate.

Counterexample refinement eliminates further refuted candidates. Exhaustion
is only of improving candidates in this specified finite language, not of
machine designs or encodings generally. An unsuccessful proof or timeout is
unverified, not acceptance or a mathematical outcome. Checkpoints pin sources
and compiled checker modules, validate witnesses/history, and freshly certify
the incumbent on resume. An optional explicit local argv proposer receives
JSON feedback and must return exactly typed radix/width data. No LLM/API call,
OpenEvolve installation, or use of Winger's private implementation occurred.
This is a small cost-guided synthesis loop with formal acceptance, not a claim
to reproduce his search method exactly.

## Reproduce and assurance

From `research/catchup`, with the pinned Lean 4.27.0/Mathlib dependencies:

```sh
python3 -B machine/layout/verify.py
python3 -B machine/layout/search.py --output /tmp/catchup-layout-run
python3 -B machine/layout/search.py --output /tmp/catchup-layout-run --resume
```

Use a fresh output directory for each new run. No dependencies or toolchains
were upgraded. The source-checked Cryptids model port remains as before;
integration into the root Lean 4.35 toolchain is a separate obligation.

`verify.py` checks source pins and all 39 inherited local sources, performs the
strict default build and fresh replays of all six new Lean modules, audits the
transitive axiom closures, runs runner tests, searches afresh, resumes, and
bypasses the cheap filter with two invalid kernel-certificate controls. It
compares both encoding and roundtrip observations on every one of the 1,250
symbols for every layout (20,000 cases), plus decoding of all 2,048 eleven-bit
words, with independent Python arithmetic.

The small test uses a five-symbol alphabet encoded in three bits. Its source
branches on symbol four, overwrites it with zero, moves right and halts; other
inputs loop. Lean proves positive and empty-input behavior and the exact
576/540-state counts. Complete tables are exported and independently simulated
on an all-zero, two-way tape. The positive machine halts after 63 transitions,
head at three, retaining one-bits at positions three and four. The blank-input
instance repeats a full configuration with period 16. Corrupting the first
one-bit initialization write also yields a repeated configuration with period
16. These finite executions are regressions, not formal proof premises.

Search invocations default to 16 proposals and 120 seconds, with 30 seconds and
64 KiB captured output per child. Verification commands have a 120-second cap
and 1 MiB output cap. A timeout never denotes a game value. No RSS sandbox is
claimed. An initial `/usr/bin/time -l` wrapper returned exit one because the
sandbox denies its clock-rate query, after the Lean build itself succeeded;
that attempt is retained in `timing-wrapper.*`. Final verification runs Lean
directly and records child RSS using Python's resource API.

`benchmark.json` records actual generation/checking times, hardware, memory
scope, every new helper and inherited dependency, source/compiled sizes and
artifact hashes. `REVIEW.md` records independent criticism. These are artifact
size upper bounds; neither shorter proofs nor cheaper checking follows from
the smaller machine.

The completed verifier returned `LAYOUT_SEARCH_PASS`. All 18 recorded commands
exited zero, all six runner tests passed, and all 35 axiom audits used only
`propext`, `Classical.choice` and `Quot.sound`. All 39 preserved source hashes
matched. Both deliberately invalid kernel certificates exited one and were
rejected without timing out. All 20,000 symbol/layout observations and 2,048
word decodings matched; both finite tables and the corrupt-initializer control
behaved as stated above.

On macOS 26.6.2 arm64 with 16 logical CPUs, search took 10.492 s, fresh resume
6.510 s, and the complete-count kernel replay 55.857 s. The 18 command times
sum to 124.464 s, excluding the two separately recorded negative controls
(3.934 and 3.899 s), interactive design, and the initial timing-wrapper attempt.
The maximum individual-child high-water RSS observed was 23,527,800,832 bytes;
this is not an aggregate process-tree peak. The six new Lean modules contain
25,593 UTF-8 source bytes and 57 theorems; their compiled files occupy 2,114,888
bytes. The transitive local support contains 36 reused source files totaling
244,349 bytes, with Mathlib/compiler sources listed separately. The source and
compiled sizes account for all new supporting mathematics, including the
counting proofs. Auxiliary Python/exporter sources are separately hashed.

Historical checkpoint receipt files are provenance records, not an authenticated
proof archive: resume does not independently authenticate every old proof log.
It checks the exact roundtrip property for past accepted layouts and freshly
kernel-certifies the current incumbent, so forged historical status cannot
establish correctness. The final verifier independently checks the accepted
certificate's source/log hashes as well. The trusted local Lean installation
and explicit proposer executable remain part of the software trust boundary;
the JSON proposal data is untrusted.

The next useful experiment is to share the decoder across control locations,
using an explicit continuation representation. First prove and measure this
on one tape-dependent routine, including the cost of storing and restoring
the continuation. Repeating a full binary read tree at each control location
still dominates the present construction. This is a bounded next compiler
experiment; it does not assert that the representation will improve the total
state count or solve C.
