> **Historical run record — August 7, 2026.** Run times, state counts, checksums and results below are retained observations, not freshly reproduced measurements. The original novelty claim is corrected. The large tables were not recovered. The C++ solver is available at `computation/solvers/packed/`; its present small reproduction checks are documented there.

# Catch-Up counterexample search

Status date: 2026-08-07.

This directory contains an exact counterexample search for the Catch-Up conjecture. No
counterexample was found. The historical run independently reproduced six eligible values:

| `N` | `T_N` | Exact value | All opening values |
|---:|---:|:---:|:---:|
| 23 | 276 | draw | draw |
| 24 | 300 | draw | draw |
| 27 | 378 | draw | draw |
| 28 | 406 | draw | draw |
| 31 | 496 | draw | draw |
| 32 | 528 | draw | draw |

The first four agree with the exact frontier announced in Bernhard von Stengel's
[CGTC III abstract](https://ludicum.org/en/cgtc-iii/). The `N = 31, 32` results exceed the range in that abstract, but do not extend the known frontier: von Stengel had already reported larger cases. See the finding ledger for attribution. Finite verification does not prove the universal conjecture.

## Semantic audit

The source of truth in the repository is
`FormalConjectures/Paper/CatchUpConjecture.lean`.

`CatchUp.valueAux remaining s_me s_opp isFirstMove` implements one selection at a time.

* An empty position compares the two scores directly.
* If `s_me + remaining.sum < s_opp`, it returns loss. The rules say that the mover receives all
  remaining counters; because the inequality is strict, allocating them explicitly has the same
  outcome.
* `isFirstMove = true` forces one selection and then swaps players, independently of the scores.
* On every later selection, the mover continues precisely when the updated score is strictly less
  than the opponent's score. Equality or overshoot swaps players immediately.
* At a tied nonempty ordinary turn, every available counter is positive for the interval games, so
  exactly one selection ends the turn.
* The public conjecture uses `Finset.Icc 1 N`, so zero counters cannot create a semantic exception.

`CatchUp.Position.value` discards the absolute scores after the opening and retains the remaining
set and nonnegative deficit. The Lean theorem `CatchUp.Position.value_eq_value_aux` proves that this
normalization agrees with the score-based evaluator whenever the mover is tied or behind.

The formal and intended interval-game semantics therefore agree. The original evaluator is useful
as a specification but its noncomputable `Finset` recursion is not practical for the new frontier.

## Completed-turn recurrence

At a turn boundary let `(R, d)` mean that the current player is behind by `d >= 0`.

If `d = 0`, positivity makes every legal completed turn a singleton. Suppose `d > 0`. An ordered
turn with selected set `A` and final counter `z` is legal exactly when

```
sum (A \ {z}) < d <= sum A.
```

Necessity follows because all earlier selections must leave the mover strictly behind and the last
one must catch up. Conversely, if the inequality holds, select the elements of `A \ {z}` in any
order. Positivity ensures that every proper running sum is at most `sum (A \ {z}) < d`; selecting
`z` last then ends the turn. Thus a set is legal if and only if

```
d <= sum A  and  sum A - max A < d,
```

and `max A` is a deterministic final-pick witness. The new mover is the old opponent, behind by
`sum A - d`, so the child is `(R \ A, sum A - d)` and its value is negated. If `sum R < d`, taking
everything cannot catch up and is an immediate loss. Empty states draw at deficit zero and lose at
positive deficit. These observations prove the stated turn-boundary recurrence and its equivalence
to atomic selection.

## Implementations and validation

`catch_up_search.cpp` (`./catch_up_search.cpp`; historical path) deliberately contains separate implementations.

1. `AbsoluteAtomicSolver` keeps the remaining mask, both absolute scores, and the special-opening
   flag. It follows the source rules one counter at a time.
2. `TurnBoundarySolver` enumerates completed-turn subsets, retains `max A` as a final-pick witness,
   and applies the recurrence above.
3. `PackedExactTable` and `WideExactTable` evaluate the normalized one-pick recurrence bottom-up.
   All deficits for one mask are packed into one machine word. This factors completed-turn
   enumeration into atomic transitions and makes `N = 32` feasible.
4. `verifyScalar` independently recomputes every table label with scalar ternary negamax. It does
   not use the packed reflection formulas.
5. `MonteCarloSearch` is a separate, explicitly non-certifying reconnaissance mode.

The deterministic self-test checks:

* terminal losses/draws, exact catches, overshoots, tied starts, and the take-all rule;
* every completed-turn subset against exhaustive ordered selection for all states on counters
  `1, ..., 7`;
* all three exact solvers on every internally consistent state through `N = 10`;
* 40 fixed-seed internally consistent states at `N = 12`;
* both packed-word widths;
* the complete 2015 table through `N = 20`:

```
N:      3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
value:  D D W W D D L  L  D  D  W  L  D  D  W  L  D  D
```

The original paper states this table explicitly and describes `N = 23, 24, 27, 28` only as Monte
Carlo investigations: [Isaksen–Ismail–Brams–Nealen (2015), section 3.1 and table 2](https://www.nealen.net/papers/catch-up-a-game-in-which-the-lead-alternates-2015.pdf).

## Reproduction

Build and run the deterministic validation suite:

```bash
clang++ -std=c++20 -O3 -DNDEBUG -Wall -Wextra -Werror \
  scripts/catch_up_search/catch_up_search.cpp -o HISTORICAL_TMP/catch_up_search
HISTORICAL_TMP/catch_up_search --self-test
```

Run and independently verify an exact table:

```bash
HISTORICAL_TMP/catch_up_search --solve 31 --verify --threads 16
HISTORICAL_TMP/catch_up_search --solve 32 --verify --threads 16
```

Tables through `N = 31` can be serialized in a deterministic little-endian format:

```bash
HISTORICAL_TMP/catch_up_search --solve 24 --save HISTORICAL_TMP/catchup-n24-v1.bin --verify --threads 8
HISTORICAL_TMP/catch_up_search --verify-table HISTORICAL_TMP/catchup-n24-v1.bin --threads 8
shasum -a 256 HISTORICAL_TMP/catchup-n24-v1.bin
```

The format is magic `CATCHUP1`, 32-bit version `1`, 32-bit `N`, 64-bit mask count, then one
32-bit win word and one 32-bit draw word per mask. Saving the 68 GiB `N = 32` table is intentionally
disabled; it is verified in memory.

Run non-certifying reconnaissance:

```bash
HISTORICAL_TMP/catch_up_search --mcts 35 2000000 1
HISTORICAL_TMP/catch_up_search --mcts 36 2000000 1
```

## Exact run log

`states` counts every stored `(mask, deficit)` label, including terminal labels. `moves` counts
every atomic edge examined at a nonterminal label. The bottom-up implementation has no cache hits.

| `N` | Value | States | Moves | Packed time | Scalar verification | Peak memory |
|---:|:---:|---:|---:|---:|---:|---:|
| 23 | D | 201,326,592 | 2,315,247,628 | 0.197 s | 0.731 s | 81.5 MiB |
| 24 | D | 419,430,400 | 5,033,154,544 | 0.460 s | 1.559 s | 161.5 MiB |
| 27 | D | 3,758,096,384 | 50,734,281,613 | 4.685 s | 15.668 s | 1,281.5 MiB |
| 28 | D | 7,784,628,224 | 108,984,771,093 | 9.082 s | 36.029 s | 2,561.5 MiB |
| 31 | D | 68,719,476,736 | 1,065,151,845,930 | 87.637 s | 268.326 s | 20,481.5 MiB |
| 32 | D | 141,733,920,768 | 2,267,742,679,717 | 211.333 s | 659.797 s | 73,728.8 MiB |

Complete saved tables and SHA-256 checksums (temporary paths from the recorded run):

| `N` | Path | SHA-256 |
|---:|---|---|
| 23 | `HISTORICAL_TMP/catchup-n23-v1.bin` | `9acf91922b27b8fbc2fd504779a67f7df80a84ba394ddca663611ef63459904e` |
| 24 | `HISTORICAL_TMP/catchup-n24-v1.bin` | `a8d8580316777b372b0e585a182340653e19cb20d01211c8a19bacd455628443` |
| 27 | `HISTORICAL_TMP/catchup-n27-v1.bin` | `88ccc20388d36d14f3045c2f77aa1059a03dc5218b60bf9b57ead7bfaf1515c8` |
| 28 | `HISTORICAL_TMP/catchup-n28-v1.bin` | `75f984ed1cd0152ae835e74b2b6f236e51dd125933a3dfdef75ed746c587506e` |

## Heuristic reconnaissance and transfer obstructions

Three two-million-simulation MCTS runs were made for each next eligible value. Root empirical
means for seeds `1, 2, 3` were:

| `N` | Seed 1 | Seed 2 | Seed 3 |
|---:|---:|---:|---:|
| 35 | 0.000272 | -0.000317 | 0.000378 |
| 36 | 0.000680 | 0.000669 | -0.000525 |

Favored openings changed across seeds. This gives no stable counterexample signal and is not an
exact result.

The existing `scripts/catch_up_compare.lean` also falsifies a strong statewise `N -> N + 4` lift:

* at `N = 11`, `(remaining = [1, 2, 8], deficit = 11)` is a draw, while adjoining counters
  `12, 13, 14, 15` makes it a win;
* at `N = 12`, `(remaining = [6, 12], deficit = 6)` is a draw, while adjoining
  `13, 14, 15, 16` makes it a win.

These are exact counterexamples to the strong auxiliary lift, not to the root Catch-Up conjecture.

## Remaining bottleneck

The completed-turn solver has worst-case `3^N` mask/action incidence and is used only for semantic
validation. The packed exact solver uses `O(N 2^N)` word transitions and `O(2^N)` storage. At
`N = 32`, storage already reaches 72 GiB. The next exact pair, `N = 35, 36`, needs a layer-ranked or
disk-backed representation, symmetry/strategy compression, or a certificate-directed AND/OR
search. The most concrete next improvement is to retain only adjacent cardinality layers using
combinatorial ranking, then verify each layer before discarding its predecessor.

No Lean counterexample theorem was added because no counterexample was found. The existing Lean
normalization theorem supplies the proof-level bridge for a future certified non-draw result; a
future table or strategy checker would still need a soundness proof before `native_decide` could be
used.
