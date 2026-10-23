# Computation and evidence

The Lean executable evaluator is in [Executable.lean](../CatchUp/Executable.lean). Its correspondence to the reference is proved; experiments are not substituted for that theorem.

## Small independent comparison

From the repository root after `lake build`:

```sh
python3 computation/check_semantics.py
```

This compares Lean with an independent absolute-score recurrence on all 64 subsets of `{1,…,6}`, at deficits `0,…,12` (832 noninitial states), plus initial intervals `N=0,…,9`. It also checks common-score translation and boundary cases. The script stops after 180 seconds if Lean evaluation does not finish; an incomplete run is a failure, never a draw.

## Certified strategy examples

The public Lean library includes the finite certificates directly as proof terms, with small terminal evaluations replayed by the kernel. See the [obstruction results](../results/) and [retained certificate artifacts](certificates/). Search can be untrusted: the final formal proof covers every adversarial branch. The Python comparison here is not a general certificate checker and is not a premise of those proofs.

## Other public computations

| Source | Reported cases | Status in this collection |
| --- | --- | --- |
| [catchup-exact](https://github.com/t1merickson/catchup-exact) | Exact draws at `N=23,24,27,28` | External report; not independently audited here |
| [c5-k4](https://github.com/Kuberwastaken/c5-k4/blob/main/results/expansion/catchup_n23_n24_report.md) | Computations for `N=23,24` | External report; later development reports should be checked as well |
| [Original authors' code](https://github.com/aisaksen/catch-up) | Original game implementation and experiments | Historical source |

No counterexample at `N=39` or `N=40` is certified in this collection. Neither an incomplete search nor a heuristic result establishes a counterexample. A claimed initial-game win needs its exact rules, winner, full opening obligations and an independently checked certificate.

Finite computation, however extensive, does not establish the conjecture for all `N`.
