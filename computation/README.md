# Computation and evidence

The Lean executable evaluator is in [Executable.lean](../CatchUp/Executable.lean). Its correspondence to the reference is proved; experiments are not substituted for that theorem.

For state bounds, parity-based storage and the scope of historical reproduction, see [what exact computation can reuse](../docs/exact-computation.md). The [opening guide](../docs/openings.md) distinguishes a drawn root from every opening drawing and links to the existing pair-neutrality theorem.

[Retained observation files](observations/) preserve earlier bounded runs, including failed policies, unprocessed cases and all recorded alternatives. Read the [experimental findings](../results/experimental-findings.md) for their scope. These are not fresh numerical replays or Lean certificates.

The [runnable experiment bundles](experiments/) now include the original shared C++ solver, pair/orphan drivers, seed generators and frozen inputs, plus the [packed exact interval solver](solvers/packed/) recovered from the other local repository. Start with `python3 computation/experiments/check.py` or `python3 computation/experiments/run.py consecutive`. These require a C++ compiler but no Lean installation. Defaults use small cases; larger historical batches are explicit options and are not run by CI. Provenance and the still-unported experiment closures are recorded separately.

## Explore a position without Lean

```sh
python3 computation/explore.py --initial 4
python3 computation/explore.py --remaining 2 4 7 --deficit 3
python3 scripts/check_collection.py
```

The explorer reports every legal first pick, same-player continuations and perspective swaps. It uses bitsets, exact integers and memoized ternary outcomes. Default limits: 10 seconds, 200,000 newly examined states, at most 20 counters. A limit reports `incomplete`, no outcome, and exit code 2. No memo entry for an unfinished node is treated as a draw.

This small implementation reuses the existing normalized research recurrence; it is not the optimized large-N solver and does not produce a Lean certificate. `check_collection.py` compares it with the separately implemented absolute-score recurrence on 893 noninitial cases and 13 roots, checks every reported first reply, and exercises sign, invalid-input and resource-limit controls. It also checks catalog coverage, source fidelity and documentation links.

### Small reproduced interval outcomes

Values are for P1 under optimal play. These [stored examples](examples.json) are independently checked exact computations, not new Lean certificate declarations.

| N | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Outcome | Draw | Win | Win | Draw | Draw | Win | Win | Draw | Draw | Loss | Loss | Draw | Draw |

Odd-total games can favor either player: N=5 and N=9 already illustrate this. The even-total conjecture is a separate universal statement.

## Small independent comparison

From the repository root after `lake build`:

```sh
python3 computation/check_semantics.py
```

This compares Lean with an independent absolute-score recurrence on all 64 subsets of `{1,…,6}`, at deficits `0,…,12` (832 noninitial states), plus initial intervals `N=0,…,9`. It also checks common-score translation and boundary cases. The script stops after 180 seconds if Lean evaluation does not finish; an incomplete run is a failure, never a draw.

## Recovered Lean certificate checker

[CertificateChecker](../CatchUp/Earlier/CertificateChecker.lean) has a compiled [soundness theorem](../CatchUp/Earlier/CertificateSoundness.lean) for fixed-player nonloss. [Partial certificates](../CatchUp/Earlier/PartialCertificateSoundness.lean) additionally require a theorem establishing each target leaf's safety. The [literal full/compressed fixtures](../CatchUp/Earlier/CertificateComplexityFixtures.lean) cover both players from the actual roots at N=3,4,7.

After `lake build`, execute the recovered solver/extractor/checker and malformed-certificate controls through N=8:

```sh
lake env lean --run computation/CheckEarlier.lean
```

This checker takes the Lean `StrategyDAG` format. It does not automatically accept the different JSON search-witness format below or turn explorer output into a proof certificate.

## Certified strategy examples

The public Lean library includes the finite certificates directly as proof terms, with small terminal evaluations replayed by the kernel. See the [obstruction results](../results/) and [retained certificate artifacts](certificates/). Search can be untrusted: the final formal proof covers every adversarial branch. The Python comparison here is not a general certificate checker and is not a premise of those proofs.

## Other public computations

| Source | Reported cases | Status in this collection |
| --- | --- | --- |
| [von Stengel, LSE seminar, 22 February 2019](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf#page=5) | Optimal-play computations through N=34 consistent with the even-total conjecture | Earlier institutional report; no source/certificate archive located and no independent replay here |
| [catchup-exact](https://github.com/t1merickson/catchup-exact) | Exact draws at `N=23,24,27,28` | External report; not independently audited here |
| [c5-k4](https://github.com/Kuberwastaken/c5-k4/blob/e2cee93231eefb91c41e35450f7eeb19fd9c8c75/results/expansion/live-search-2026-08-14/catchup-n24-parity-packed-development/result.md) | Computations for `N=23,24` | External report; later development reports should be checked as well |
| [Original authors' code](https://github.com/aisaksen/catch-up) | Original game implementation and experiments | Historical source |

No counterexample at `N=39` or `N=40` is certified in this collection. Neither an incomplete search nor a heuristic result establishes a counterexample. A claimed initial-game win needs its exact rules, winner, full opening obligations and an independently checked certificate.

Finite computation, however extensive, does not establish the conjecture for all `N`. See the [reading guide](../docs/sources.md) for stable snapshots and historical attribution; the 2026 projects are not the earliest reported computations through N=28.
