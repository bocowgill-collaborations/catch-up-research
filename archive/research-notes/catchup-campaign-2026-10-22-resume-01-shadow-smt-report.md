> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Eight-shadow finite-arity SMT diagnostic

Completed the requested bounded round for tail cardinalities 0 through 4.
Every query returned UNSAT, including the stronger control asking for a
deficit-eight loss alone. Thus the tested conditional exclusion is vacuous:
no losing eight-shadow exists in this encoded finite-arity range, regardless
of the two-anchor core outcome. This suggests examining direct eight-shadow
nonloss before trying to transfer its hypothetical loss to the core.

These are independently reviewed SMT experiments, **not Lean theorems**.
No general-cardinality assertion, interval conjecture, or minimum-counterexample
claim is established. All tail labels were unbounded integers, rather than
labels restricted by a finite maximum; tail cardinality was bounded.

## Frozen target and semantics

For exactly k sorted, distinct labels T, all at least 9, with even sum, let
C={2,3,4,7} union T and E={4,7} union T. The main query asserts both C at deficit8
LOSS and E at deficit1 LOSS. The separate control asserts only C8 LOSS.

The acyclic encoding has a state for each pair of disjoint ownership masks
and each actual mover. Fixed player1 scores sum(A); fixed player2 scores
8+sum(B), or 1+sum(B) for the other root. Every remaining pick is covered.
Player1 maximizes and player2 minimizes the ternary terminal payoff. A move
switches players exactly on reaching or exceeding the opponent's score;
otherwise the same player continues. Empty states compare final scores.
Every transition removes one counter. The reference impossible-catching
shortcut has the same result as completing all compulsory picks. These roots
are post-opening positions; no initial-game opening is encoded.

## Validation and results

`validation.json` records 16 independent literal-score root values, their
score-shift checks, and 16 explicit mover2 fixed-player sign checks. The solver
accepts all correct values and rejects any mismatch. It also rejects an
injected wrong WIN/LOSS assertion. An intentionally broken always-alternating
recurrence is detected on a continuation example. All controls PASS.

Independent recurrence and generated-code review is in `review.md`.
Exact SMT2, solver output/statistics, exit status, timeout, timing, memory and
hash metadata are retained separately for all ten search queries. All final
query exit codes are zero; no timeout occurred. The largest query has 14,580
ownership states and 37,908 choice edges across its two roots. Its joint-loss
run took 13.65 seconds with 923 MB peak child RSS; C8-alone took 15.64 seconds
with 887 MB. Hardware and software identification are in `summary.json`.

An initial k0 run incorrectly requested a model after UNSAT, producing the
expected model-unavailable error. It was preserved under
`initial-model-request-error/`. Model extraction now occurs only after SAT;
the clean final k0 query was rerun. This reporting repair does not change the
game recurrence. No SAT witness was found and no native result was imported
into Lean. No independently checked SMT UNSAT proof object is claimed.

## Reproduction

From the workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/shadow-smt/search.py validate
python3 research/catchup/campaign_2026_10_22/resume_01/shadow-smt/search.py search --k 4
python3 research/catchup/campaign_2026_10_22/resume_01/shadow-smt/search.py search --k 4 --shadow-only
```

Replace 4 by 0,1,2,3 for the other completed cardinalities. Each solver query
has an internal 120-second cap and external 125-second cap. An unknown or
timeout is recorded as such, never interpreted as an outcome. Every saved
`.smt2` can also be rerun directly with the identified Z3 binary.

The round is stopped with no active process or background job. No k>=5 query
was attempted. Next mathematical decision belongs to the parent: seek a
uniform explanation for direct C8 nonloss, or authorize a separately bounded
discriminating extension. Do not turn the completed finite-arity evidence
into an unrestricted theorem.
