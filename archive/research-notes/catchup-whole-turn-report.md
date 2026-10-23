> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.WholeTurn](../../CatchUp/WholeTurn.lean).

# Whole turns, score quotas, and pair count

## Mathematical result

The partial response rule takes a legal completed-turn subset with total
`s=(T+d)/2`, where `T` is the current remaining sum and `d` the current deficit.
The endpoint then has remaining sum equal to its deficit, so it draws under
every continuation. The mover therefore has a non-losing strategy. This does
**not** prove the mover's optimal value is draw: another turn could win.

`CatchUp/WholeTurn.lean` proves this using the existing `TurnSet`, endpoint,
and strategy API. The new arbitrary-cardinality construction is as follows.
Let `B` be even pair starts, `U⊆B`, and `H` a reserve disjoint from the pairs.
Let orphan counter `z` be distinct from both. Write `L=sum B`, `t=|U|`, and
`d+e=z`. Take one counter from every pair, choosing its upper exactly on `U`,
then take `z` last. If

```
sum H + |B| = e + 2*t,       L+t < d,
```

this is a legal whole turn, its endpoint draws, and its mover can avoid loss.
All preparatory picks together total less than the deficit; positivity ensures
every proper preparatory prefix stays below it. The existing completed-turn
theorem supplies the legal trace, including nonterminality and turn ownership.
The invariant is arithmetic, not defined by the evaluator's answer.

The relevant singleton-five specialization is: after a large lower opponent
pick `r`, remaining set `{5} ∪ pairs(B) ∪ {r+1}`, deficit `r-8`, where B
has even starts at least 6, with

```
|B|=4+2*t,       sum B+t+8 < r.
```

Choosing any `t` uppers works. An existence corollary needs no supplied `U`.
Thus four intact pairs require zero uppers; six require one; eight require two.
These conditions are sufficient, not necessary. They do not cover small orphans.
The generic theorem also permits the empty reserve and upper-orphan cases.

## A certified nine-pair diagnostic

For six remaining pairs with starts `(6,10,12,20,40,80)`, orphan `181`,
and deficit `172`, the response

```
6,10,12,20,40,80,181
```

is one legal turn. It leaves `( {5,7,11,13,21,41,81}, 177 )`, whose remaining
sum is 179. The new mover can take all remaining counters in one turn and
strictly win. Both turn legality and this win are proved in Lean, without
a new exhaustive outcome computation. The corrected response

```
7,10,12,20,40,80,181
```

leaves `( {5,6,11,13,21,41,81}, 178 )`, which draws. Its responder's non-loss
is a formal instance of the uniform theorem.

This position occurs in the experimental nine-pair support
`(4,6,10,12,20,40,80,180,182)` after opponent `182`, response `4,183` on
the same turn, and opponent `180`. No original-interval reachability or root
optimal outcome is asserted. This is a failed response, not a conjecture counterexample.

## The obstruction to a complete strategy

For positive deficit and counters at most `M`, a legal turn has total less
than `d+M`. Consequently a balanced completed turn requires `T<d+2*M`.
At the old mate obstruction, `T=174,d=4,M=41`; the target is 89, whereas any
legal turn totals less than 45. Lean proves that **no** balanced turn exists,
not merely that this particular pair-based construction fails.

More generally, if every counter of an initial support is at most M and its
total is at least `4*M`, every positive
opening counter `x≤M` rules out a balanced reply in Player 2's first turn.
For the original interval `[1,N]`, this holds for every `N≥7`, by a symbolic
Lean induction on the interval sum. `interval_no_one_turn_balance` covers all
openings and all turn subsets, without assuming the Catch-Up conjecture.

This refutes a shortcut strategy class. It does not refute the conjecture or
rule out defenses carrying the draw quota across several turns. The highest
value next step is to seek an explicit multi-turn reserve invariant that
survives the small-orphan branches, starting at the certified `(T,d,M)=(174,4,41)`
obstruction; another immediate-balance patch cannot cover that branch.
Concretely, taking 5 there leaves
`({6,7,10,11,13,20,21,40,41},1)`, which the independent literal evaluator
finds drawn. The next test should retain all nine opponent choices from that
state and seek a return rule preserving a reserve. This draw is experimental,
not a new formal theorem.

## Bounded experiments and their scope

`python3 whole_turn/verify.py` replays the complete record with subprocess
limits of 120 seconds and in-script discovery/check limits of 60 seconds.
No timeout is a game outcome. The input sets include dense combinations,
sparse held-out examples, and the previous obstruction. All supports have
even starts, minimum 4, and omit 8; they are normalized midgames, not
initial interval positions.

| Test | Seven pairs | Nine pairs |
|---|---:|---:|
| Full pair supports | 31 | 48 |
| All opponent root turns | 434 | 864 |
| Distinct singleton-five residual supports | 23 | 38 |
| All ordered opponent residual turns | 766 | 1844 |
| Residual turns containing a continuation | 570 | 1372 |
| Residual turns with a balanced reply | 8 | 8 |
| Of these, explicit one-per-pair construction | 4 | 4 |
| Residual turns left uncovered | 758 | 1836 |
| Root turns with balanced reply | 2 | 2 |

All opponent picks are retained, including all second picks after 5, 6, or 7.
Different legal orderings of the same subset are retained too. These are
**one-round coverage tests of a partial rule**, not full strategy certificates.
Uncovered means no immediate balanced turn exists; it means neither draw nor loss.
No optimal root values are claimed by this test.

An independent absolute-score implementation replays every one of the 3908
opponent turns and independently checks the existence/nonexistence of a
balanced reply by selecting the last counter and solving exact subset sum
for the preparation. It checks 30 resulting endpoint values with the prior
literal-score minimax implementation. Separately, all 882 upper-selection
subsets over the specified four-, six-, and eight-pair supports are tested,
using ascending and descending preparation orders. The equality-boundary
test rejects a planned pick after the preparation has already caught up.

The Lean proofs are the basis for mathematical claims; the Python evidence
is a separate bounded audit of the stated rule and coverage. The original
conjecture remains open. The existing high-level halting equivalence is
unchanged; no binary Turing machine is built in this workstream.

## Verification and proof-size record

See `benchmark.json` for pinned source commits, Lean/Mathlib versions,
commands, timings, peak individual-child memory, source sizes including reused
support, compiled sizes, and artifact hashes. The proof contains 19 newly
introduced theorems, including two private helpers; 17 public transitive
axiom reports must contain only `propext`, `Classical.choice`, and `Quot.sound`.
No native computation, external answer axiom, heartbeat increase, or unfinished
conjecture is used. Source size is an upper bound, not a minimality claim.
