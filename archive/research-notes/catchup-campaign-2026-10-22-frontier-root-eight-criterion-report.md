> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.RootUpperEightCriterion](../../CatchUp/RootUpperEightCriterion.lean).

# Exact criterion for the eight-shadow reserve endpoint

The production module `CatchUp/RootUpperEightCriterion.lean` proves the
following necessary-and-sufficient contracts for arbitrary finite C. Assume
2,3 belong to C, every counter is at least two, five is absent, and the actual
shadow has V(C,8)=LOSS. Put E=C\{2,3}. Then

    V(C,2)=LOSS  iff  V(E,1)=LOSS.

If six and eight are also absent, then

    V(insert5 C,3)=WIN  iff  V(E,1)=LOSS,

and equivalently

    V(insert5 C,3)!=WIN  iff  V(E,1)!=LOSS.

The high-LOSS premise is retained in every statement. No tail-size, parity,
interval, or density hypothesis is needed for these generic contracts.
The missing-five hypothesis is explicit: under the high-loss premise, a
present five would be a winning low-two entry, because high pick five
continues to deficit-three LOSS while low pick five catches to that same
LOSS. The stronger first statement without absent five was not adopted.

## Proof mechanism

The forward low-two implication was already proved in RootUpperEightFrontier.
For the reverse, core-one LOSS makes (C.erase3,1) WIN by taking two. Thus first
three at (C,2) loses. Every other first counter loses by DeficitCrossingEntry,
with the equality counter five absent. The exact nonterminal all-moves-loss
recurrence now proves low-two LOSS. The reverse reserve implication takes
five as a legal catching singleton, leaving precisely that low-two LOSS.
Its forward direction consumes the existing all-opponent-turn frontier:
a winning reserve state must expose one of the two reserve-taking losses,
either of which forces core-one LOSS. Hence the iff genuinely covers every
opponent reply through the proved prior universal theorem.

## Actual interval specialization

For N>=11 and literal actual shadow

    V([2,N]\{5,6,8},8)=LOSS,

the module proves

    V([2,N]\{6,8},3)!=WIN
        iff V({4,7} union [9,N],1)!=LOSS.

The left position is the genuine endpoint after pick eight from
Q_N=([2,N]\{6},5). The criterion itself does not require parent LOSS;
when a caller retains parent LOSS, that premise separately forces the left
endpoint to WIN. The theorem does not assert core nonloss, exclude the
simultaneous shadow/core loss, establish general density preservation, or
settle B/H/C.

## Verification and accounting

All commands passed from `research/catchup`, with each subprocess bounded
at 120 seconds and no raised Lean budgets:

- `lake --wfail build CatchUp.RootUpperEightCriterion`
- `lake env lean -DwarningAsError=true CatchUp/RootUpperEightCriterion.lean`
- `lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/root-eight-criterion/audit.lean`

Strict target build 6.529s; fresh warning-strict
source 5.725s; four public transitive axiom audits
5.299s. Every audited theorem uses only propext,
Classical.choice, and Quot.sound. No sorry, custom axiom, native-only outcome
computation, table or solver premise occurs. Independent source review PASS
is recorded in REVIEW.md.

Lean (version 4.27.0, arm64-apple-darwin24.6.0, commit db93fe1608548721853390a10cd40580fe7d22ae, Release)

New source: 5352 bytes / 114 lines /
4 public theorems. SHA256
`ca4c0b33b07c7e295e24b3b0c7653d871d191db9e69c3f7c1844678b331e789b`. Serialized local .olean:
426080 bytes. Local import closure:
13 files / 138019
source bytes, excluding pinned Mathlib. These are local artifact and source
accounting, not proof-size minimality or complete transitive certificate size.
Per-command cumulative child peak RSS and platform are in checks.json; no
isolated per-theorem memory claim is made. Frozen sources and completed
manifests were not modified; only the new criterion source and this new
evidence directory were written for this implementation.
