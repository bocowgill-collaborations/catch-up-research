> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.AnchorFour](../../CatchUp/AnchorFour.lean), [CatchUp.AnchorFourEndgames](../../CatchUp/AnchorFourEndgames.lean).

# Anchored-four reserve: eight is necessary and cannot be the winning pick

The four lower-pick families have been narrowed by new unbounded Lean theorems.
For five separated adjacent pairs with even starts and minimum at least four:

1. At deficit three, the position is nonwinning if the start eight is absent.
2. In the anchored-four family, picking the lower counter eight always leaves
   the defender a nonlosing child.
3. Consequently any unresolved win must contain both `{4,5}` and `{8,9}` and
   pick one of the other three lower counters.

These are statements about optimal outcomes under the frozen reference rules.
Nonwinning means the acting player cannot force a win; a draw is not asserted.
There is no upper bound on magnitudes or gaps. The full canonical minimum-four
claim, arbitrary-length interval claim, original C, and binary-machine delivery
remain open. No counterexample to those claims is established here.

## Mathematical mechanism and every opponent response

`AnchorFourEndgames.lean` proves the smaller nonwinning families used in the
repair, with all parameters unbounded:

| Remaining counters | Deficit | Hypotheses |
|---|---|---|
| `{5,b,b+1}` | 10 | even b>=6, b!=8 |
| `{5,b,b+1}` | 8 | even b>=6 |
| `{5,7,b,b+1}` | 1 or 3 | arbitrary b>=8 |
| `{5,7,b,b+1,c,c+1}` | 2 | arbitrary b>=10, c>=b+2 |
| `{5,b,b+1,c,c+1}` | 7 | even separated starts>=6 |
| Same five counters | 9 | additionally start8 absent |
| `{5,b,b+1,c,c+1,e,e+1}` | 8 | even separated starts>=6, start8 absent |

Proofs enumerate every available opposing pick and supply a legal safe reply.
The only low even start that can continue at the seven-counter deficit-eight
root is six (and its upper mate seven); these cases reduce respectively to
the two-odd-counter deficit-two lemma and the existing drawn three-pair family
at deficit one. Upper picks use the companion deficit-seven lemma; lower picks
use deficit nine. Catching reverses perspective, continuing preserves it.

`AnchorFour.four_four_nonwin_no_eight` proves that the four-pair position
`({4,5,b,b+1,c,c+1,e,e+1},4)` is nonwinning when its even starts omit eight.
It covers all eight possible first picks. For a nonminimal lower pick q>=10,
the defender continues with four, then catches with q+1, leaving the singleton
five and two remaining pairs at deficit nine. At q=6, four catches immediately,
leaving `{5,7}` and two pairs at deficit two. The lower pick four normally
allows reply five; the two known three-pair obstructions `(6,10,12)` and
`(6,10,20)` receive explicit replies ten and twenty, checked on six-counter
leaves. Every upper pick has the existing safe mate response.

`AnchorFive.lower_orphan_no_eight` addresses the requested five-pair child.
With three intact pairs omitting eight and the missing pair's upper counter
q+1, at deficit q-3: if q=6, reply seven and use the new four-pair theorem;
if q>=8, continue with four and then catch with q+1. The residual is precisely
the seven-counter deficit-eight family above. This supplies all four lower
replies when eight is absent. If the opponent picked eight, every remaining
intact pair omits eight, so the same theorem applies in either possible
sorted location of that pick. The prior lowest-lower and upper-pick theorems
complete the five-pair assembly.

The final theorem `win_requires_four_and_eight` retains an explicit losing-child
witness at a lower counter different from four and eight. It does not replace
an unresolved strategic property with a predicate defined to mean draw.

## A certified failure retained

The no-eight condition on the seven-counter residual cannot be dropped:

```
value({5,8,9,16,17,20,21},8) = win.
```

Lean certifies this in `eight_residual_win`. At starts `(4,8,10,16,20)`, after
the opponent picks ten and the defender continues with four, the defender
reaches `({5,8,9,11,16,17,20,21},3)`. Both five and the orphan's mate eleven
lose, but eight is safe. `post_four_two_replies_lose` formally proves all three
facts. Thus a four-first strategy needs an adaptive continuation in the
remaining family. These are counterexamples to a residual lemma and reply
rules, not to the five-pair claim or C. No least-witness claim is made.

The exact exploratory scan found taking four safe in all104160 tested orphan
shapes, while748 direct mate continuations failed. A q>=8 scan found179 cases
where both five and the mate failed after four. Those observations motivate the
next repair; they are not proofs of an unconditional four-first strategy.
Bounds, commands, and diagnostics are retained in `failed_attempts.md` and the
C++ source/output files.

## Verification and evidence boundaries

Run from the pinned downstream directory `research/catchup`:

```
python3 anchored_four/verify.py
```

The verifier checks earlier proof hashes and pinned reference transformations,
builds the full default target and new audit with warnings treated as errors,
freshly elaborates all four new proof files, and replays seventeen transitive
axiom reports. Their permitted axioms are exactly `propext`, `Classical.choice`,
and `Quot.sound`. Headline results include the reference bridge, classifier
soundness, new structure/regressions, and prior high-level search equivalence.
Finite leaves use kernel reduction through the proved evaluator or classifier;
no native-only computation or external answer is a proof premise. The fresh
independent read-only mathematical review accepted statement fidelity, all
branches, and scope; its minor comment caveat was fixed. See `review.md`.

The independent bounded checks completed4185 family cases and33279 immediate
opponent replies, with144 absolute-score comparisons. They include1365
exhaustive five-pair no-eight shapes with minimum4 and other starts in6..36,
and120 held-out sparse shapes with starts below512, seed20261024. Full policy
expansion covered12 whole no-eight five-pair roots and8 lower-eight child roots:
128 installed response obligations,50559 distinct states,53230 opponent edges,
86189 friendly edges,57654 same-player continuation edges, and2776 terminals.
Every visited state was independently compared with the absolute-score
recurrence. All legal opponent choices are expanded. Below the installed
response rules, exact safe friendly choices supply experimental continuations.
These tests remain separate from the parameterized Lean proofs. The two losing
replies and safe alternative in the regression are tested as negative controls.

Every verification subprocess group is capped at120 seconds. The C++ loops
have20-second caps, the Python recurrence has a60-second internal bound, and
an incomplete run is an error rather than a game outcome. No heartbeat limit
was raised. No dependency was upgraded, and no public action was taken.

Lean remains4.27.0 with Mathlib
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. `SOURCES.json` pins the reference,
research API, and Cryptids commits; the unfinished conjecture is absent from
the compiled API. `benchmark.json` records every new source, all local imported
support, derived compiled-module sizes, artifact hashes, actual command times,
and maximum individual child RSS. Mathlib is separately pinned, not counted
as newly introduced mathematics. Discovery time is separate and was not timed.
No compact proof of C, minimality claim, proof-size lower bound, or binary
machine state count follows from this milestone.

## Completed replay and proof-size record

The complete verifier finished successfully. All seventeen axiom lists contain
only the three standard axioms named above. Prior tied-four proof hashes were
also compared separately with their earlier benchmark and remain unchanged.
New proof/support source totals36041 UTF-8 bytes across18 theorem declarations;
reused local import support totals241314 bytes. The five new compiled modules
total11821280 bytes. These counts include every new intermediate endgame,
repair, regression, and audit file; there is no external proof certificate.

Fresh source replay plus the axiom audit took44.98 seconds; all recorded
verification subprocess times sum to112.46 seconds, including the40.43-second
warning-strict build and22.72-second adversarial check. Maximum individual
child RSS was6025756672 bytes on the recorded16-logical-CPU arm64 macOS26.6.2
host. This is not aggregate process memory. The CPU brand query was unavailable
inside the sandbox. Interactive discovery was not timed. The short source is
an upper bound for this restricted structural proof, not a proof of C or an
argument for a short universal proof.

## Exact remaining obligation

For even u<v<w with u>=10, roots with both required pairs have either starts
`(4,8,u,v,w)` or `(4,6,8,u,v)`. It suffices now to prove nonloss of the child
after each lower pick in `{u,v,w}` in the first family, or `{6,u,v}` in the
second. Deficits are the picked counter minus three, and every other counter
remains except that pick. Three choices remain per root. The case six must
retain the immediate catch after four; larger cases retain same-player
continuation. The highest-value next step is a safe adaptive continuation
through the pair at eight, preserving the certified `(8,16,20)` residual
obstruction rather than assuming the mate or smallest counter is safe.
