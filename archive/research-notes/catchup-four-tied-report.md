> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.TiedFour](../../CatchUp/TiedFour.lean), [CatchUp.ThreePairClose](../../CatchUp/ThreePairClose.lean).

# Symbolic tied-four and deficit-one five-pair results

The recommended tied-four nonwinning obligation is proved for arbitrary pair
magnitudes and gaps. The proof strengthens the minimum from four to three and
also establishes two useful adjacent results:

* `three_pairs_one_draw`: `{a,a+1,b,b+1,c,c+1}` at deficit one draws whenever
  `3 ≤ a`, `a+2 ≤ b`, and `b+2 ≤ c`.
* `four_pairs_tied_nonwin`: four arbitrary disjoint adjacent pairs, with minimum
  at least three, are nonwinning at deficit zero.
* `five_pairs_one_nonwin`: five arbitrary disjoint adjacent pairs, with minimum
  at least four, are nonwinning at deficit one.

All are theorems about optimal ternary outcomes under the frozen reference
semantics. No bound on counter magnitudes or gaps occurs. These are fixed pair
counts; closure for arbitrary pair counts and the universal conjecture remain
unproved. No Catch-Up counterexample was found. The high-level search halting
equivalence already present remains checked; no binary-machine table or new
machine-state claim is supplied in this milestone.

## Mechanism and complete opponent coverage

The new proof kernel is a three-counter arithmetic classification in
`CatchUp/ThreePairClose.lean`. For `0<a<b<c<2a` and `d<2a`, put
`t=a+b-c`, `u=a+c-b`, and `v=b+c-a`. Then

```
nonloss iff d≤t OR (c-a≤d AND d≤u) OR (b<d AND d≤v)
win     iff d<t OR (c-a≤d AND d<u) OR (b<d AND d<v).
```

The source proves the equivalent nonwinning formula as the negation of the
second line. Both classifications follow from the existing exact pair theorem,
with all three moves present. There is no computation over a bounded range of
parameters in these proofs.

For three pairs in the dense case `c+1<2a`, the proof shows at least one of
`a+1,b+1,c+1` is safe. It retains all five opponent replies to each candidate,
then all four possible friendly replies, before applying the three-counter
classification. Lean's arithmetic tactic supplies kernel proofs for the
resulting linear inequalities. Both continuing and catching transitions are
kept; no move is silently treated as changing players.

In the wide case `c≥2a-1`, choosing `a+1` suffices. The existing proof already
covered `b≥2a-1`. When only the last pair is sufficiently high, the formerly
problematic reply is `c+1`. The repair chooses `b+1`: it catches if `c≤a+b`,
leaving a nonwinning boundary triple. If `c>a+b`, it must continue, then takes
`c`, leaving `{a,b}` at deficit `a+b`. This is a checked nonwinning pair endgame.
The other four opposing replies use the existing orphan and tied-two-pair
results. Combining dense and wide cases proves a draw, using the existing
uniform three-pair nonwinning theorem for the other inequality.

At tied four pairs, after each of the eight possible picks, the defender takes
the mate. A lower-counter opening allows the mate to catch, leaving three
pairs at deficit one from the opponent's perspective. An upper-counter opening
requires the lower mate to continue the same defender turn, leaving the same
drawn family from the defender's perspective. Thus every opening is covered.

At five pairs and deficit one, all ten possible first picks have a catching mate
reply. The remaining four pairs have deficit two after a lower pick, or deficit
zero after an upper pick. The existing uniform four-pair deficit-two theorem
and the new tied-four theorem establish both cases.

`reserve_one_nonwin_structural` instantiates the five-pair theorem for all six
pair deletions from `[4,15]`. It uses finite set equalities only, with no finite
game evaluation. It replaces the old tied-leaf table **for the purpose of this
deficit-one nonwinning claim**. The old table proved draw of its tied supports,
a stronger conclusion than the new general tied nonwinning theorem. The old
files remain intact, and the deficit-three reserve proof still needs its
separate four-pair deficit-four analysis.

## Failed rules retained

A fixed choice of the smallest, middle, or largest upper counter is not always
safe. The exact position with starts `(11,14,18)` draws, while taking the middle
upper counter `15` loses. `fixed_middle_choice_loses` certifies both facts in
Lean. The opening loss is not a loss of the optimal position.

`probe.json` also preserves failures of proposed orphan and conditional-opening
invariants. `triples.json` preserves witnesses against each fixed upper choice.
These were exploratory calculations, not conjecture counterexamples. An early
interpretation conflated a previously known losing smallest-upper opening with
a losing three-pair position; that interpretation was corrected before any
formal claim. The successful proof retains all three upper choices.

## Assurance and reproducibility

Run from `research/catchup`:

```
python3 four_tied/verify.py
```

This checks pinned sources and prior proof hashes, performs a warning-strict
build, freshly elaborates every new proof source, audits thirteen headline and
bridge theorems transitively, and runs bounded independent tests. Every
subprocess has a 120-second process-group limit; the Python experiment also
has an internal 60-second bound. A timeout is an error, never a game outcome.

The package remains Lean 4.27.0 with Mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Reference and earlier research pins
are in `SOURCES.json` and copied into the benchmark record. No reference
semantics or dependency versions changed.

The proof sources use no `sorry`, external answer as an axiom, or native-only
evaluation. Concrete regression leaves use `decide +kernel`. Python uses exact
integers and a separately implemented absolute-score evaluator for selected
comparisons; it is experimental evidence outside the formal trust boundary.
A fresh-context independent reviewer accepted statement fidelity, all branches,
perspective swaps, and the fixed-pair-count scope. This review is distinct from
Lean's verification.

The first dense symbolic simplification exhausted the default 200,000
heartbeats. The accepted declaration has a 1,600,000-heartbeat limit and an
external wall-clock bound. Interactive proof discovery time was not measured;
checking cost is recorded separately. Source byte counts include every new
supporting lemma, and reused support and compiled artifacts are counted
separately. These are upper bounds for explicit proofs, with no minimality
claim or comparison between unlike target propositions.

## Next precise mathematical obligation

Prove five arbitrary pairs nonwinning at deficit three. Lower-counter first
picks can make a mate reply expose a winning four-pair deficit-four position;
these orphan nodes need uniform safe repairs. The known sparse obstruction
must remain in the test suite. Deficit-one closure is now available uniformly,
so that is the remaining five-pair reserve obligation for further pair deletion.

## Completed checks and size record

The reproducible command completed successfully. All thirteen transitive axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx` or custom result axiom appears. The warning-strict build and fresh
elaboration of all three new proof sources passed. The audit source also
re-elaborated successfully. Source and earlier-proof hash checks passed.

Bounded tests completed 216,200 three-counter states, 18,424 three-pair shapes,
7,315 four-pair shapes, and 6,188 five-pair shapes. They checked 124,190
opponent edges after safe three-pair openings, 58,520 tied-four opening replies
(including 29,260 continuing mate picks), and 61,880 five-pair opening replies.
869 comparisons used the independent absolute-score implementation. The
regression rejects the fixed middle-upper rule at `(11,14,18)`.

The new formal sources contain 30,882 UTF-8 bytes and
16 theorems, including all new supporting mathematics.
Reused sources total 184,177 bytes, including the earlier
finite N15 API imported by the regression corollary. The new main proof imports
no finite N15 table. Derived compiled modules total
25,941,664 bytes; the arithmetic-generated proof terms are
substantial despite the shorter source. This is not a claim of a small proof
of the universal conjecture.

Checking ran on macOS-26.6.2-arm64-arm-64bit, 16 logical CPUs.
Fresh dense-kernel source replay took 36.25s;
structural assembly 11.36s; regression
5.58s. The recorded verification commands
totaled 81.34s. Peak individual child
RSS was 6,867,599,360
bytes (not aggregate process memory). Full hashes and per-command records are
in `benchmark.json`; Python checking took
11.50s, separately from proof discovery.
