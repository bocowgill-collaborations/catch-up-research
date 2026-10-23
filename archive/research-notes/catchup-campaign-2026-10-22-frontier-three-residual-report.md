> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseThreeResidual](../../CatchUp/DenseThreeResidual.lean).

# Dense gap closure for at most three residual counters

`CatchUp/DenseThreeResidual.lean` extends the finished two-residual result
to residual cardinality at most three. It also proves a stronger entry
statement for the nonterminal three-residual branch. No earlier proof
source was edited.

## Exact uniform results

The setup is arbitrary N,d,b,w,S,B. The hypotheses are exactly those of
`DenseTwoResidual.small_residual_successor_nonloss`, except that the
residual cardinality bound increases from two to three:

* S is contained in [1,N], with actual hole count h and 2h+1<=d<=N.
* sum(S)+d is even; B is a subset of S of sum d; b belongs to B.
* Every member of **every** exact-d subset of original S is at most b.
* w belongs to S minus B and b<w<d.
* No subset of original S has sum d-w.
* The actual residual opening `afterOpening (S minus B) w` has value LOSS.
* C=(S minus B).erase w has at most three counters.

`small_residual_successor_nonloss` concludes that the continuing
successor (S.erase w,d-w) is NONLOSS. No original-parent-loss hypothesis,
even-N restriction, target-missing substitute, externally supplied game
value, or assumption that all residual counters exceed w is used.

`three_residual_safe_block_entry` assumes instead card(C)=3 and
sum(C)>=w. It concludes that there is x in B with d-w<=x and
`moveOutcome x != LOSS` at the continuing successor. Thus a safe first
pick can be made in the exact block and ends the turn immediately,
including the equality case. The move outcome is the full minimax
outcome, so it quantifies over optimal opposing play rather than a
selected reply. This entry result is restricted to the nonterminal
three-counter branch. The finished N=11 four-residual diagnostic shows
that the entry conclusion does not extend unchanged to size four.

## Analytic reduction and faithful reconstruction

The existing large-exact-member theorem and global maximality give
b>=d-h. The new imported `DenseGapMass.small_gap_block_bound` uses the
true original-S subsum gap to strengthen the small-residual mass bound:
card(B)<=3 and N<=2*card(C)+7. In particular the three-counter branch
has N<=13. Its source hash is pinned in `source-check.json`.

For A=B.erase b, the partition and density lemmas give
card(A)<=2 and sum(A)<=card(A)+4. The positive tails therefore lie in
the displayed twelve-element list. The main proof derives this
classification from the arbitrary input. It extracts an ordered triple
u<v<z for C, proves C is disjoint from insert w B, reconstructs
S=insert w B union C and d=b+sum(A), and proves the numeric prefix
2N+1<=d+2(card(A)+5). Its tail-only gap prefix follows from A subset B
subset S. These prefixes reduce computation; they add no hypotheses
to either uniform theorem.

The main proof also proves the decoded residual is exactly the actual
`afterOpening (S minus B) w`, and that the decoded successor is exactly
(S.erase w,d-w). No reachability or value conclusion is inferred from
a mere match of scalar summaries.

## Finite proof support

The classifier uses a small `Seed` record containing b, A, w and the
three ordered residual counters. Its block, residual, and successor
definitions only decode these parameters. This is a finite certificate
representation, not new game semantics.

`bounded_classification` proves pure arithmetic coverage by the 142
listed static seeds across N=9..13; the other ambient sizes through
13 have empty lists. Five separate kernel declarations cover the
ambient slices at default budgets. `residual_filter` then checks the
actual residual values and proves coverage by nineteen live seeds.
The lists are **covering lists**: the public implications establish
completeness, without claiming converse classification or formal
counts of satisfying configurations.

`live_safe_entries` proves each of the nineteen concrete live seeds
has a catching block pick with child value not WIN, using the existing
executable evaluator. The general entry proof transfers this through
`Position.eval_eq_value` and `Position.moveOutcome`; negation at a
catching pick gives the required move outcome not LOSS. The final
nonloss theorem composes this with the unchanged terminal and
at-most-two-counter results, using the existing exact best-move API.

The proposed lists were transcribed from the retained independent
`search/three_residual_arithmetic.json` and
`search/three_residual_results.json`. Neither JSON is imported by Lean.
Kernel proofs verify the covering implications and all game predicates;
the search outputs supply candidates, not premises. The parent owns
independent source review and literal-score replay evidence.

## Verification and scope

The source has 454 lines, 18,641 bytes, six public and six private
theorems, eight definitions, one parameter record, and two explicit
decidability instances. SHA-256:
`29561377f8370ed48137060fd887714208f3089689d7effff69084d47961d798`.
There is no `sorry`, native evaluation, custom axiom, unsafe definition,
or raised heartbeat/recursion budget. The initial monolithic attempt
hit default resource limits; `iteration-notes.md` records the move to
separate arithmetic and closed value checks. The successful combined
LeanProbe check of the finite stages took 71.076 seconds, and the
headline/composition check took 4.993 seconds on a warm environment.

Production build and public transitive axiom audit are retained in
`build.log`, `axioms.log`, and their statistics files, with explicit
120-second subprocess limits. The warning-strict build passed in
82.282 seconds wall time (80 seconds for the module), and all six public
theorem audits passed in 4.632 seconds. Every transitive axiom list is
restricted to `propext`, `Classical.choice`, and `Quot.sound`. Darwin
child-process maximum RSS was 11,495,473,152 bytes for the build and
5,293,113,344 bytes for the audit. `source-check.json` records source
metrics, dependency hash, and unchanged hashes of ten finished modules.
The uniform statements are proved; unrestricted residual size, general
F, H, and C remain open.
