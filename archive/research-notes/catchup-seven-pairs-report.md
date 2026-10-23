> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.SevenPairTest](../../CatchUp/SevenPairTest.lean).

# Seven-pair generalization test: the proposed recursive closure fails

The test produced a **Lean-certified diagnostic counterexample to the proposed
recursive strategy/invariant**. It does not refute the Catch-Up conjecture or
canonical seven-pair nonwinning. The prior five-pair theorems remain intact.

The response clauses and exact attempted lift are in `CANDIDATE.md`. They were
extracted from the existing proof: prepare with four, catch with the missing
upper mate, then pair subsequent opposing choices with their mates, retaining
the old low-counter and sparse repairs. The recursive auxiliary family consists
of singleton five and an even number of intact canonical pairs at deficit nine,
with even starts at least six and start eight absent. The existing proof covers
two intact pairs. The attempted extension to arbitrary even pair count is false.

## Mathematical obstruction

The old theorem proves nonwinning of

```
({5,6,7,10,11},9).
```

Adding the pairs `{20,21}` and `{40,41}` instead gives

```
({5,6,7,10,11,20,21,40,41},9) = win.
```

Taking five strictly continues the SAME player's turn and leaves
`({6,7,10,11,20,21,40,41},4)`. The earlier exact four-pair classification already
proves that position winning. Thus the new proof uses a known structural
obstruction, not a large new outcome computation. `adding_two_pairs_breaks_nine`
proves the before/after contrast, and `not_uniform_nine` formally refutes the
quantified candidate for all even pair counts. The support predicate is purely
geometric; it is not defined using the game value.

This obstruction occurs in a legal seven-pair counterplay. For **every even
q>=42**, use starts `(4,6,10,12,20,40,q)` at normalized deficit three. These are
seven disjoint positive canonical pairs, with counter eight absent. The picks are:

| Player | Pick(s) | Next player and deficit |
|---|---|---|
| Player1 | q | Player2, q-3 |
| Player2 | 4, then q+1 in the same turn | Player1, 8 |
| Player1 | 12 | Player2, 4 |
| Player2 | proposed mate13 | Player1, 9 |
| Player1 | 5, continuing the turn | Player1, 4, winning four-pair state |

`candidate_counterplay_legal` proves the prefix is a genuine nonterminal
`GamePosition.PickTrace`. Available catcher witnesses rule out accidental early
termination. `uniform_bad_mate` proves that thirteen has move outcome LOSS for
the defender at the reached decision node, for every q>=42. At the critical
endpoint, `critical_defender_cannot_avoid_loss` proves Player2 has no nonlosing
continuation, even with unrestricted future choices. `lifted_nine_reference_win`
also connects the obstruction directly to the literal absolute-score evaluator.

The constructed start is a normalized test state, not an original interval
root. Initial-interval reachability is not asserted. A policy counterexample
needs one legal adversarial prefix followed by a forced win; the existing exact
value theorem supplies the adversarial continuation guarantee. We do not claim
that Player2 lacked a different safe earlier response. For example, the q80
root and the node before mate13 are drawn in the independent exact experiments;
these draw values are not new formal theorems. No least-counterexample claim is
made, even though42 is the lower bound of this explicit family.

## What the experiments actually checked

The small exact solver was extended from ten supplied counter slots to fourteen.
It retains actual magnitudes, uses a distinct missing-cache marker, and negates
only when a pick catches. Its recurrence was compared with the prior solver on
all141312 common `(mask,deficit)` cases in three supports. The solver remains
untrusted experimental code; no external answer is a proof premise.

The seven-pair test completed594 supports:593 omit eight and one includes it as
a control. There are462 exhaustive dense supports, plus128 held-out sparse
samples (seed20261025), and the saved diagnostic inputs, deduplicated. Every one
of the14 opposing first picks was checked:8316 opening choices. All selected
first responses had nonlosing optimal continuation values. The scalar root
values were557 draws and37 losses, with no win. These are bounded midgame
outcomes, not results for initial interval N.

That first-round success did not establish the recursive strategy. The next
response round checked84 previously supported three-pair residuals and58
five-pair residuals. It expanded **all3114 complete opponent turns**, including
2160 instances with a below-deficit first pick and a second pick by that same
opponent. The smaller84 cases had zero failures; the larger cases had two:

- Remaining starts `(6,10,12,20,40)`: opponent12, proposed reply13 loses.
- Remaining starts `(6,10,20,40,80)`: opponent80, proposed reply81 loses.

Both expose the same winning nine-counter deficit-nine residual. Positive
response values permit some future defense; they are not certificates that the
same candidate can safely repeat forever. A negative value is sufficient to
refute that response. No branch was omitted after finding a failure.

Independent literal-score replay checked14 full seven-pair supports,210
root/opening values,273 selected response values, and all3260 residual-root/
response values in the round tests. The complete diagnostic trace was replayed
with actual score ownership. A separate strictly winning policy below the
critical state expanded223 states,179 opponent edges,141 same-player
continuations, and45 strictly winning terminals. Every visited value was
compared independently. `critical_policy.json` is experimental; the Lean proof
uses the prior certified four-pair theorem, not this JSON file.

## Verification and trust

Reproduce from `research/catchup`:

```
python3 seven_pairs/verify.py
```

The verifier checks pinned sources and all earlier proof hashes, builds with
warnings treated as errors, freshly elaborates the proof source, audits thirteen
headline/dependency theorems transitively, recompiles the bounded experiments,
and reruns the independent score replay. Permitted axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. Audits include evaluator correspondence,
classifier soundness, the reused exact classification, all new headline claims,
and the unchanged high-level search halting equivalence. There is no unfinished
conjecture dependence, custom result axiom, `sorry`, or native-only computation.

An independent fresh-context read-only mathematical reviewer accepted statement
fidelity, all turn changes, legal support, and exact scope. It made no edits or
builds and did not audit the experiments. Its docstring caveat about hypotheses
on the pair-support constructor was fixed before final replay. See `review.md`.

Each final verification subprocess group has a120-second cap; C++ experimental
loops have20-second caps and flush completed rows. The independent Python replay
has60-second guards. A timeout is an incomplete run, never a game outcome. Lean
remains4.27.0 with the pinned Mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Complete source/experiment hashes,
reference pins, new and reused proof sizes, compiled sizes, and command timings
are in `benchmark.json`. Discovery cost is separate and was not timed. No
heartbeat limit was raised, no dependency upgraded, and no public action taken.

## Completed checking and proof-size record

The reproducible verifier completed successfully. All thirteen transitive axiom
reports contain only the standard axioms named above. New supporting Lean source
is9382 UTF-8 bytes across13 theorem declarations, including the legal trace and
audit file. Reused local import support is274644 bytes. The two new compiled
modules total3201032 bytes. These are explicit upper bounds with every new
supporting declaration counted, not claims of minimality or a short proof of C.
The experimental policy JSON is not counted as a formal certificate.

Fresh source replay and axiom audit took11.55 seconds; all recorded verification
subprocess times sum to33.70 seconds. The root experiment took2.03 seconds,
residual-round experiment0.16 seconds, and independent replay14.24 seconds.
Maximum individual child RSS was5496930304 bytes, not aggregate memory, on the
recorded16-logical-CPU arm64 macOS26.6.2 host. Interactive generation cost was
not timed. No binary machine or machine state count is produced by this test.

## Research decision

The unchanged pair-count lift and unqualified recursive mate continuation are
rejected. Their first-round success conceals a later strategic failure. We
should not treat completion of more five-pair cases as evidence that this
particular induction will close. The result leaves open stronger pairing
strategies, modified invariants, and the original conjecture.

The next mathematical requirement is a new response principle that accounts
for the low singleton and the number of intact pairs, handles its continuing
pick, and avoids exposing this certified four-pair win. Any proposed replacement
must confront this counterplay and predict a safe move before thirteen; it must
then face fresh larger-pair tests. The present experiment stops at the failed
closure rather than adding an unexplained exception and declaring a general rule.
