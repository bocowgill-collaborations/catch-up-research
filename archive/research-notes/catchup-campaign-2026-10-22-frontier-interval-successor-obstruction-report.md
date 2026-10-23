> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.IntervalSuccessorReplyObstruction](../../CatchUp/IntervalSuccessorReplyObstruction.lean).

# Immediate-successor reply fails at a drawn actual interval endpoint

The production module `CatchUp/IntervalSuccessorReplyObstruction.lean` certifies
one fixed N=15 diagnostic, with reference minimax semantics and all subsequent
opponent replies included. No new search was run.

    S = {7,9,10,12,13,14,15}, deficit 8: DRAW.

The complete first-pick map from the current mover's perspective is:

| Pick | Outcome |
| --- | --- |
| 7 | DRAW |
| 9 | DRAW |
| 10 | DRAW |
| 12 | LOSS |
| 13 | DRAW |
| 14 | LOSS |
| 15 | DRAW |

The proposed immediate successor of opponent counter eleven is twelve.
It catches and leaves the opponent

    ({7,9,10,13,14,15}, 4),

whose value is WIN: the opponent can force a strict win. Thus immediate-
successor reply fails even at this actually drawn endpoint. Seven is one
certified drawing alternative; the complete map above gives the other ones.

## Literal context and player identity

Starting at E={4,7} union [9,15], deficit one, with player p1 moving, the
module proves both legal nonterminal Steps and the exact GamePosition identity

    (coreGame.afterPick 4).afterPick 11 = (S,8,p1).

Core pick four catches to deficit three and swaps to p2. Opponent eleven
catches to deficit eight and swaps back to the original mover p1. The literal
reserve formula ((insert7 [9,15]).erase11,11-3) is separately proved equal
to the endpoint. This matches IntervalReserveDepth.start15 11's normalized
position without importing that concurrently authored module.

Observed depth source SHA256:
`0c779ee454ce512f99779e651beed08b86f5907ea8b89ed7a7ca3f14935b60dd`.
This is an explicit semantic cross-reference, not a Lean import dependency.
No value for the full E15 root is certified here; neither an actual interval
C counterexample nor a general defense is inferred from this diagnostic.

## Verification and cost

Seven shared child-value certificates use eval_eq_value followed by
`decide +kernel`, with at most six counters in any evaluated child. The full
move map reuses them. The seven-counter endpoint DRAW is derived from the
map via exact minimax, and the after-twelve WIN also reuses its child lemma.
The full E15 root is never evaluated. Literal finite set/context identities
use kernel decision only.

All final commands passed from `research/catchup`, with default Lean budgets
and each subprocess bounded at 120 seconds:

- `lake --wfail build CatchUp.IntervalSuccessorReplyObstruction`
- `lake env lean -DwarningAsError=true CatchUp/IntervalSuccessorReplyObstruction.lean`
- `lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/interval-successor-obstruction/audit.lean`

Final build 9.213s; fresh source
8.112s; all nine public transitive axiom audits
5.497s. Every audited theorem uses only propext,
Classical.choice, and Quot.sound. Independent source review passed; its
requested win-description correction was applied. Earlier passing receipts
before that wording correction are retained. Total recorded verification
including that repeat: 45.521s.

Lean (version 4.27.0, arm64-apple-darwin24.6.0, commit db93fe1608548721853390a10cd40580fe7d22ae, Release)

New source: 4643 bytes / 101 lines /
9 public theorems. SHA256
`ec6ae08978e854ca841b8ed0cba16f661df93a7b0268c7238112b040e16afb6a`. Serialized local .olean:
198032 bytes. Local import closure:
5 files / 85698
source bytes, excluding pinned Mathlib. These are artifact and source counts,
not proof-size minimality or complete transitive certificate size. Per-command
cumulative child peak RSS and platform are in checks.json; no isolated
per-theorem memory claim is made. Frozen sources and completed manifests
were not modified. Only this new module and its new evidence directory were
written for the diagnostic.
