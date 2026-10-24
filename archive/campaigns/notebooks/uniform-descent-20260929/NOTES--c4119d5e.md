> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Uniform exact-sum descent session

Start: 2026-09-29 08:43:29 EDT (12:43:29 UTC).
Hard deadline: 2026-09-29 12:13:29 EDT (16:13:29 UTC).
[Administrative account detail omitted.]
Base: faad9dcc. Branch: codex/catchup-uniform-descent-20260929.

## Acceptance and dependency map

The main closure is existing `value_Icc_eq_draw_of_lower_pair_deletion_nonloss`:
all Q_N(b) nonloss plus Q_N(2) draw imply interval draw. Target A addresses only
b>=3 via `pair_deletion_position_value_ne_loss_of_upper_residuals`; Target B is
the additional first-pair draw (nonloss and nonwinning must be distinguished).

Target A family is F(m,k)=[2,m] union [m+3,m+k+2], m>=1, k>=1, with N=m+k+2
admissible and N>=11. Exclude loss after every upper opening. First diagnostic k=4.

Blueprint: read the k=3 exact-sum tree; design a closed support family recording
holes introduced by exact-sum exchanges; find a decreasing rank and geometric
terminal blocks; otherwise isolate failed closure and move to actual adjacent-pair
geometry. No global compatibility assumption counts as a theorem.

Target B: first-pair draw, with odd disjoint actual adjacent pairs at deficit one
as a candidate nonloss sublemma. This candidate is not yet tested or assumed.

New exact-computation budget: 15 minutes maximum, targeted falsification only.
No research agent launched yet. Independent review only after a complete candidate.

## Research checkpoint, 09:08 EDT

One conceptual helper completed an independent upper-only closure obstruction;
see INDEPENDENT_IDEA.md. The upper-only forcing class necessarily encounters a
lower intruder, even for arbitrarily large m. Its repair deletes small counters
and does not return to the original family.

Symbolic exact-block search (not an outcome solver) found four forcing trees
for k=4. LeanProbe checked all four, with m>=17 separating small complements
(at most 11) from lower pivots (at least m-5). This yields Q_N(N-4) nonloss for
N>=23, no parity assumption. Production module built warning-strict; audit
module syntax is being corrected before its final build. One independent
reviewer is active; the conceptual helper has stopped.

New targeted computation so far: under one minute. Odd actual adjacent-pair
nonloss survived the saved bounded probe, but is unproved. A stronger window
formula based only on pair count and deficit is false: S={3,4,5,6},d=1 loses
although the dominant-pair terminal-window model predicts win. Also S={2,3,4,5},
d=2 wins although that model predicts draw. These refute the window, not the
odd-pair deficit-one target.

Current conceptual sublemma for Target B: T odd intact adjacent pairs, a<min T,
consider orphan supports {a} union T at deficits a-1 and a+1. If nonwinning
could be proved there, matching the mate of a higher reply after opening the
smallest upper counter would yield a useful pair-peeling induction. This
sublemma is a candidate, not a premise; it needs independent falsification and
actual closure, especially when successive mate replies drift to a±2.

## Prior traps retained

- Different exact-sum blocks give different tied supports. A shared positive-deficit
  parent can have several winning catches; tied uniqueness cannot be applied there.
- Fixed mate responses, copying common counters, and prepaid reserve initialization
  are not available invariants.
- Full explicit DAG exponential size does not imply a long symbolic proof.

## Mechanism checkpoint, approximately 10:00 EDT

Target A has a fully verified k=4 endpoint, but not a closed family in k.
The upper-only two-step obstruction is now formalized and independently reviewed.
The exact lower-intruder repair changes the gap and spends counters that cannot
be reused. No repeatable replacement was found; a larger hard-coded forest was
not pursued as a putative uniform mechanism.

Target B yielded a substantive local geometric theorem: the orphan-minus state
draws exactly above b≥2a−1, while the orphan-plus state always draws under the
disjointness/minimum assumptions. This yields arbitrary-gap three-pair nonwinning
and separated three-pair draw, including anchor {3,4}. All are Lean-checked and
independently reviewed. Pair count remains fixed; P_8 is the only interval endpoint
covered by this new draw family.

The parity/low-deficit nonwinning induction fails at {4,5,7,8,14,15},d=3.
The aligned-pair draw window fails at {6,7,10,11},d=2. The odd-pair d=1
candidate itself remains unrefuted. A multiple-pair orphan extension is not
routine: GapAccounting proves that its two nonwinning hypotheses already force
the underlying d=1 draw. This conditional statement does not prove either premise.

## Final-check checkpoint, 10:06 EDT

All four production audits pass together: 24 named declarations, standard
logical axioms only. GapAccounting passes warning-strict standalone checking
with the same axiom whitelist. The negative-control check now rejects the
existing open conjecture specifically for sorryAx (an initial monadic return-type
ambiguity in the test was repaired first).

Final saved probe baseline: 691 odd-pair cases; no loss found. Exact counterexamples
and other named probes replay successfully. Symbolic forest replay gives 35 nodes,
14 leaves, depth≤5, small counters≤11, large pivots≥m−5, valid for all m≥17.
All new outcome computations remain under three minutes in total, well below
the 15-minute cap. No new outcome table or finite controller was produced.

[Administrative account detail omitted.]
The next gap is adaptive mathematical closure, not absence of finite evidence.
