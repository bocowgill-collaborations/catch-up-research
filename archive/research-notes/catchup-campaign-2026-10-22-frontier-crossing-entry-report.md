> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DeficitCrossingEntry](../../CatchUp/DeficitCrossingEntry.lean).

# Uniform crossing entry contract

The new source `CatchUp/DeficitCrossingEntry.lean` proves an unbounded entry
restriction on arbitrary finite natural supports. Assume a belongs to S,
every remaining counter is at least l, and V(S,l+2a)=LOSS. Then every low first
pick x distinct from a and l+a has move outcome LOSS at (S,l). The equality
counter l+a remains an explicit exception. If it is absent from S, then

    V(S,l) != LOSS  iff  V(S.erase(a),a-l) != WIN.

Deleting a below the higher deficit leaves the losing shadow (S.erase(a),l+a).
The existing reserved-counter theorem then gives a winning reply a after each
low singleton turn x except the equality case. Thus the opponent endpoint
wins and x loses. The only degenerate case a=l=0 is handled directly from the
high parent's all-moves-loss property. The proof includes actual endpoint
catchability and does not execute a move at a terminal shadow.

For anchor B, the specialization needs only 3 in S, all labels at least 2,
5 absent, and V(S,8)=LOSS. Every first pick at (S,2) except 3 loses, and

    V(S,2) != LOSS  iff  V(S.erase(3),1) != WIN.

Consequently for S={2,3,4,7} union T with min(T)>=9 this identifies the exact
remaining safe-entry obligation. No evenness, tail-size bound or interval
assumption is used by the contract. It does not prove that the forced entry
is safe, either B reflection, root reentry, H, or C. The separate erased-2
reflection endpoint is not resolved by this module.

## Verification

All commands below passed from `research/catchup`, with raw logs and timing
receipts beside this report:

- `lake --wfail build CatchUp.DeficitCrossingEntry`
- `lake env lean -DwarningAsError=true CatchUp/DeficitCrossingEntry.lean`
- `lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/crossing-entry/audit.lean`

Build 6.862s; fresh source 6.300s;
four public transitive axiom audits 5.978s.
Every audited theorem depends only on propext, Classical.choice, and Quot.sound.
Independent source review PASS is recorded in REVIEW.md. No sorry, native-only
computation, custom axiom or solver premise occurs in the finished module.

Lean (version 4.27.0, arm64-apple-darwin24.6.0, commit db93fe1608548721853390a10cd40580fe7d22ae, Release)

New source: 4381 bytes, 90 lines,
4 public theorems; SHA256 `594e1cb1d141ca7a1789c6dc9e1094b27ef472622bde2e9b0f340565354bf2a9`.
Serialized local .olean: 217872 bytes. Local import closure:
9 source files / 113108
bytes, excluding pinned Mathlib. These are source and local artifact accounting,
not proof-size minimality or complete transitive certificate size.
Per-command cumulative child peak RSS and platform are in checks.json; no
isolated per-theorem memory claim is made. Toolchain and dependencies were
unchanged. Only this new source and this evidence directory were written.
