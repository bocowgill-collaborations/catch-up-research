> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.RootUpperEightFrontier](../../CatchUp/RootUpperEightFrontier.lean).

# Actual interval upper frontier at eight

The new uniform theorem `interval_parent_loss_frontier` proves, for every
N>=11, that a hypothetical loss at

    Q_N = ([2,N] \ {6}, 5)

has one of two consequences:

1. A genuine winning opening w>=9 of the tied residual [2,N] \ {5,6}.
   Its literal post-opening position has value LOSS.
2. With C={2,3,4,7} union [9,N] and E={4,7} union [9,N], all three
   statements hold: V(C,8)=LOSS, V(E,1)=LOSS, and V(E,3)=LOSS.

The result preserves the full parent LOSS and genuine residual-opening
premises. No parity assumption is needed. It does not rule out the second
alternative, prove density preservation, close general F/H, or establish C.
The actual interval connection is the legal history 1;6;5;8: after the first
two picks, Q_N is the normalized parent; exact catch five then opening eight
produces the displayed eight-shadow. The preexisting RootUpperReentry result
has already excluded genuine opening seven; the new disjunction consumes it.

## Every opponent turn is covered

For arbitrary finite C with 2,3 present, minimum at least two, and 5,6,8 absent,
a parent loss at (insert5(insert8 C),5) and shadow loss at (C,8) imply
V(C\{2,3},1)=LOSS and V(C\{2,3},3)=LOSS. There is no cardinality,
interval or evenness restriction in this support theorem.

After parent pick eight, the opponent state (insert5 C,3) is WIN. At deficit
three every legal TurnSet is a singleton, or preparation two followed by one
final counter. A total of eight would require absent counter eight or absent
counter six; hence the shadow reply theorem handles every turn avoiding five.
A winning opponent state must therefore have a reserve-taking losing endpoint.
The only such turns are {5} and {2,5}, leaving (C,2) or (C.erase2,4).

The latter loss continues by three to the core at deficit one. In the former
case, low pick three from a loss gives full WIN at D=(C.erase3,1), while the
eight-shadow continues by three to LOSS at (C.erase3,5). The existing forced-
entry theorem at l=1,a=2 excludes every winning first move of D except two
(the equality counter three is absent). Exact minimax extracts that actual
winning pick two and therefore a core deficit-one LOSS. Finally, the original
eight-shadow continues below its deficit through {2,3}, forcing the same
core to lose at deficit three.

## Verification and accounting

All commands passed from `research/catchup`:

- `lake --wfail build CatchUp.RootUpperEightFrontier`
- `lake env lean -DwarningAsError=true CatchUp/RootUpperEightFrontier.lean`
- `lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/root-reentry-eight/audit.lean`

Strict target build 7.118s; fresh warning-strict
source 5.352s; six public transitive axiom audits
5.015s. Every audited theorem uses only propext,
Classical.choice, and Quot.sound. No sorry, custom axiom, native-only outcome
computation, bounded table, or solver premise occurs in the finished module.
Independent source review PASS is recorded in REVIEW.md.

Lean (version 4.27.0, arm64-apple-darwin24.6.0, commit db93fe1608548721853390a10cd40580fe7d22ae, Release)

New source: 11552 bytes / 249 lines /
6 public and 3 private theorems.
SHA256 `62495a2df401a306a71f7d04b1fd23c95042883d11cca310b87cac6938dff5ab`. Serialized local .olean:
656712 bytes. Local import closure:
12 files / 132667
source bytes, excluding pinned Mathlib. These are local artifact and source
accounting, not proof-size minimality or complete transitive certificate size.
Per-command cumulative child peak RSS and platform are in checks.json; no
isolated per-theorem memory claim is made. The three existing sources were
not edited; only this new source and this evidence directory were written.
