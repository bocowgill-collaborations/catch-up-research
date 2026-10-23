> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DeficitTwo](../../CatchUp/DeficitTwo.lean).

The arbitrary-length claim `Position (Icc 4 N) 2 ≠ win` for eligible `N ≥ 7`
remains open. This milestone proves outcome theorems for infinite parameterized
families, rather than another evaluator normal form.

In `CatchUp/DeficitTwo.lean`, for all `4 ≤ a`, `a+2 ≤ b`, and `b+2 ≤ c`,

```
Position ({a,a+1,b,b+1,c,c+1},3) = win  ↔  (a,b,c) = (4,7,14).
```

The old notes already contained this exceptional winning position. The new result
classifies every three-pair strict win at deficit three under these hypotheses.
The theorem is about the acting player's optimal outcome, not a particular play.

For any four sorted disjoint adjacent pairs with minimum at least four,

```
Position ({a,a+1,b,b+1,c,c+1,e,e+1},2) ≠ win.
```

There is no parity or gap upper bound. After any first pick, answering with its
mate normally leaves three pairs at deficit one or three. The deficit-one lemma
is reused from the pinned research branch. The new classification resolves
deficit three except when deletion exposes starts `4,7,14`. If the missing pair
starts at `f`, disjointness forces `9 ≤ f ≤ 12` or `f ≥ 16`. The four small
cases are kernel-replayed. In the unbounded case, the defender takes `4`, then
`7`, continuing the same turn, then `f+1`. This leaves the opponent the fixed
drawn state `({5,8,14,15},14)`. All eight possible first picks are quantified
over in Lean. The three-pair proof likewise covers all six picks, including
its continuing-turn repairs and exhaustive small exceptional leaves.

Consequently `Position (Icc a (a+7)) 2 ≠ win` for every `a ≥ 4`, including the
requested `N=11` case. This is a fixed-width interval theorem, not induction on
interval length. The file also proves that the general deficit-two nonwin
claim implies nonloss for `Position (Icc 3 N) 1`, by choosing `3`, and that the
deficit-two family is actually reachable after opening and picks `1,2,3` with
Player 2 next. The opposite nonloss direction and other pair-deletion obligations
needed for the original conjecture remain separate.

Two stronger reply rules are formally refuted in `DeficitTwoRegression.lean`.
At `N=7`, after the first pick `6`, replying with the exact deficit `4` loses.
In the four-pair support `{4,5,7,8,9,10,14,15}`, after `9`, the mate reply `10`
loses; replying `5` is safe. Neither is a counterexample to the requested claim
or the original Catch-Up conjecture.

`check_pairs.py` tested all 969 disjoint three-pair shapes with starts in `4..24`
and all 1,820 four-pair shapes with starts in `4..22`. It covered all 20,368
opponent first picks in the nonwinning shapes, including 42 adaptive repairs,
and made 8,457 comparisons with the independent absolute-score recurrence.
Every continuation value uses exact minimax over all legal moves. The test is
bounded evidence; the symbolic Lean theorems supply the unbounded guarantee.

The archived C++ solver was reused, with its original source preserved and
hashed. A size-26 table and its scalar recurrence check cover 1,811,939,328
entries. Queries find draws for `N=7,8,11,12,15,16,19,20,23,24`, with a nonlosing
response to every first pick. These C++ outcomes are not Lean certificates.
The stochastic and unfinished `N=39/40` leads are not used as premises.

Reproduce from the downstream package directory:

```sh
python3 deficit_two/verify.py
```

This checks pinned source transformations, builds with warnings treated as
failures, replays the new proof source, audits thirteen transitive theorem
dependencies, runs the bounded adversarial tests, and rebuilds/replays the
existing exact solver. Each subprocess has a 120-second limit. `SOURCES.json`
pins the reused research commit and source blobs; the parent pins Lean 4.27.0
and Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`. `benchmark.json` counts
all new supporting proof source and reused support separately, with checking
times and scoped peak memory. The serialization is UTF-8 Lean source; no
external solver result is a proof premise. Only `propext`, `Classical.choice`,
and `Quot.sound` occur in the audited axiom closures.

Independent read-only review accepted the statement fidelity, all-pick coverage,
perspective changes, exceptional repairs, and stated scope. It also independently
re-elaborated the source and queried the headline axiom closures. This review
supplements the Lean checks; it is not itself a formal certificate.

The next useful proof obligation is the five-pair reserve family at deficits
one and three, covering every pair deletion from six consecutive pairs. That
would advance the deficit-two argument to `N=15`; merely adjoining a pair and
always taking its mate is already refuted. No binary Turing machine or new
machine equivalence is supplied by this milestone. The previously proved
high-level search equivalence is unchanged.
