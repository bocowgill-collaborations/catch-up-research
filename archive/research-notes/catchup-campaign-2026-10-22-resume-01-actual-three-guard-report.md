> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Actual three-anchor endpoint diagnostic

The tested candidate is: for T with every label at least9 and even sum,
Position({2,3,4} union T,1) is not LOSS. This is the endpoint after pick7
in the actual C8 family. The finite batch neither proves nor refutes that
uniform statement. It contains sparse supports, not consecutive tails.

The direct replacement7→3 in the new minimum-two obstruction produced
R={2,3,4,13,15,19,35,36,50,57,60,99}. This state is DRAW computationally;
its safe first picks are2,3,4,13,15,35. The replacement was tested directly:
no preservation theorem was assumed.

All129 predeclared supports completed:121 DRAW,8 WIN,0 LOSS. The batch
comprised that direct state plus128 distinct valid mutations changing one
nonanchor label by±2 or two by±1. The initial support, every support, exact
order, mutation provenance and rejected duplicate/boundary cases were saved
before the run. All12 first-pick outcomes were evaluated for every support
(1548 first choices). The native recurrence recursively optimizes every
legal opponent response; its early WIN cutoff is exact but does not print
all internal choices. No principal-variation approximation was used.

Independent literal-score evaluation checked the root and all12 first
choices for predetermined cases1,65,129, totaling36 first choices. The
normalized and literal calculations agree. These remain computational
results; no new Lean certificate is included here.

A useful diagnostic survives the lack of LOSS: case129 is
R={2,3,4,14,16,19,35,36,50,57,60,99}, deficit1, DRAW. Its ONLY safe first
picks are14 and16; picks2,3,4 all lose. Thus a strategy that always spends
one of the three anchors on its first turn cannot establish this broader
endpoint claim. Any uniform defense must adapt to tail labels or use a
stronger actual-interval hypothesis. This diagnostic is independent-literal
checked but not yet kernel certified.

No endpoint LOSS was found, so the conditional secondary C8/E1/E3 replay
was not triggered. No further mutation, larger search, or unrequested table
was started. There are no unprocessed planned inputs and no active jobs.
Runtime was0.992 seconds including compilation and literal
checks. Native CPU was0.031139 seconds; the
15-second CPU and30-second wall caps were not approached. Peak child RSS
high-water was104693760 bytes on this macOS host.

Reproduce from workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/actual-three-guard/run.py
```

The next discriminating obligation is a mathematical defense that accounts
for tail-dependent safe choices; merely declaring the anchors safe is
already contradicted by case129. An alternative is to retain the actual
consecutive-tail geometry rather than assert this arbitrary-tail invariant.
This batch does not justify selecting another larger mutation population.
