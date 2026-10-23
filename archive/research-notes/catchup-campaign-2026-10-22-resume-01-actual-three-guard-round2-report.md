> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Second prescribed three-anchor endpoint test

This is the one additional batch authorized by the parent. It tests the
same unproved arbitrary-tail endpoint claim Position({2,3,4} union T,1)
!= LOSS, where all tail labels are at least9 and sumT is even.

Seed: {2,3,4,14,16,19,35,36,50,57,60,99}, deficit1, whose only safe choices
in the first batch were14 and16. The132 distinct new supports came from all
valid one-tail-label±2 and two-tail-label±1 edits, plus±4 edits of14 or16.
The unchanged seed and invalid duplicates were excluded. All inputs and
exact provenance were saved before execution; modifications of both former
safe labels were prioritized, then one, then neither. This was a fixed
finite batch, with no adaptation to its outcomes.

Results:132/132 completed,106 DRAW,26 WIN,0 LOSS. All1584 first-choice
outcomes were retained. Of these supports,39 have no safe choice among the
anchors2,3,4; 24 have exactly one safe choice. These are exact normalized
recurrence calculations, not samples or estimates, but remain untrusted
computational evidence pending a kernel certificate.

Independent literal-score evaluation matched all three predetermined
controls1,67,132 and their36 first choices. The middle control is a useful
contrast with the seed:

  {2,3,4,14,16,19,35,36,50,59,60,99}, deficit1, DRAW.

Here ONLY2,3,4 are safe; both formerly safe tail choices14 and16 lose.
Consequently, neither always choosing an anchor nor always preserving the
seed's tail choice is a uniform policy. This is evidence about candidate
strategies, not a counterexample to the endpoint claim or Catch-Up.

No endpoint LOSS was found, so the requested conditional C8/E1/E3 checks
were not triggered. No further round was launched. All planned cases
completed; no active jobs or unprocessed inputs remain.

Total runtime including compilation and literal checks: 1.240s.
Native CPU: 0.027237s. Peak child RSS high-water:
104759296 bytes. CPU/wall caps were15s/30s.

Reproduce from workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/actual-three-guard/round2/run.py
```

No generalized safe-choice rule has emerged from these controls. The next
useful step should explain the alternating anchor/tail defenses, or narrow
to the consecutive-tail geometry that the actual interval reduction gives.
A third mutation round is not authorized by this checkpoint.
