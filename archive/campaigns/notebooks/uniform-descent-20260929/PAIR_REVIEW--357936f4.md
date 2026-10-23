> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent adjacent-pair obstruction review

Date: 2026-09-29. Production files are read-only for this reviewer.

## Acceptance ledger

- [x] P1: All four public statements have their claimed parameters and meaning.
  EVIDENCE: Direct source inspection at AdjacentPairGeometryObstruction.lean:55,84,140,160; the only hypotheses are a : Nat and the displayed bounds a≥4 or a≥6.
- [x] P2: Every catch, subtraction, reply, and early terminal condition is valid.
  EVIDENCE: All four branches checked in the table below. Pair endpoints d=lower at a=4 and a=6 preserve the equality switch. Both local minimax helpers explicitly establish nonemptiness and sum≥deficit.
- [x] P3: Warning-strict affected build and transitive axiom audit pass.
  CHECK: lake --wfail build catch_up.AdjacentPairGeometryAudit
  EXPECT: Build completed successfully
  EVIDENCE: Independent rerun after parent completion; exit 0 and expected token matched. CWD=HISTORICAL_TMP/catchup-score-debt-20260928; zsh launcher/direct child process; 2884 ms; SHA256(stdout+stderr)=86a1a4b3d01e3c7790be1ceb17653001046601417a34a9a196ba285495e6d249; 795 bytes. All four declarations have exactly propext, Quot.sound, Classical.choice.
- [x] P4: The conclusions refute only the proposed mechanisms, not odd-pair nonloss.
  EVIDENCE: The final claim is about moveOutcome(a+1), not the value of the six-counter parent. The orphan assertion concerns the precise deficit a−1. Neither assertion excludes refined invariants or other opening choices.

## Verdict

PASS. No substantive mathematical error found. Four gates met; none unmet
or abandoned. No production file or other contributor's file was edited.

## Statement and polarity checks

The four public claims match the assigned statements exactly:

- For every natural `a≥4`, `({a,a+2,a+3},a−1)` has value `.win`.
- For every natural `a≥6`, `({a,a+2,a+3,a+4},5)` has value `.loss`.
- For every natural `a≥6`, picking `a+1` from `([a,a+5],1)` has
  current-player move outcome `.loss`.
- That pick belongs to the support, catches the deficit, and is made from
  a nonterminal `GamePosition`.

The normalized position is an ordinary post-opening position with deficit
one, not the original game's special first move from equal scores. For the
three adjacent pairs `(a,a+1)`, `(a+2,a+3)`, `(a+4,a+5)`, the chosen counter
is exactly the smallest upper member.

Every selected pick in the new proofs catches, so the child value must be
negated. The helpers do this correctly. They establish `sum remaining ≥ d`
from one available catching counter and establish nonemptiness from its
membership before invoking the best-move recurrence. Thus no move is
justified by ignoring the early terminal rule.

The losing-pair helper uses the exact two-counter classification with
`0<p<q` and `q−p<d≤p`; its required side condition `q−p≤p` follows from
these hypotheses. Both picks catch. Their singleton child deficits are
strictly below the surviving positive counter, so both child values win
and both parent moves lose. Equality `d=p` gives child deficit zero and
still switches player, as required.

## All four repair branches

Write `Q=({a,a+2,a+3,a+4},5)`, where `a≥6`. Every counter in Q catches
deficit 5. After each possible pick x, the opponent has a winning reply:

| Pick x from Q | Opponent's deficit | Opponent's reply | Resulting pair and deficit |
| --- | --- | --- | --- |
| `a` | `a−5` | `a+2` | `({a+3,a+4},7)` |
| `a+2` | `a−3` | `a` | `({a+3,a+4},3)` |
| `a+3` | `a−2` | `a+4` | `({a,a+2},6)` |
| `a+4` | `a−1` | `a+3` | `({a,a+2},4)` |

All four replies are available, catch their displayed deficits, and yield
exactly the displayed natural-number differences. The first two pairs
have gap one with `1<7≤a+3` and `1<3≤a+3`; the last two have gap two with
`2<6≤a` and `2<4≤a`. Thus every resulting pair loses, every opponent's
triple wins, and every pick from Q loses. The fourth row invokes the
separately proved orphan theorem, which uses that same reply `a+3`.

The orphan theorem works already at `a=4`: picking 7 from `({4,6,7},3)`
leaves `({4,6},4)` for the opponent. The critical quadruple boundary is
`a=6`, where the third row leaves `({6,8},6)`. Both lie in the valid
`d=lower` endpoint of the pair-loss rule. No subtraction truncation occurs
under the stated bounds. These checks establish sufficiency of the bounds;
no claim that they are optimal is needed.

Finally, picking `a+1` from deficit one leaves the opponent at deficit a
with `{a,a+2,a+3,a+4,a+5}`. Their legal catching reply `a+5` leaves exactly
Q at deficit five. Since Q loses, that five-counter child wins and the
original pick loses. The separate legality theorem proves support,
catching, and nonterminality, so this is not merely the value of an
unavailable total transition.

## Trust and scope

The independent warning-strict affected-target rerun succeeded. Lake
replayed the current artifacts produced by the parent's original build.
`Lean.collectAxioms` audits all four public declarations transitively and
rejects every axiom outside `{propext, Quot.sound, Classical.choice}`;
each declaration reports exactly those three. No `sorryAx`, native trust,
conjecture dependency, or custom axiom occurs. The only mathematical
classification imported for this argument is the already-proved exact
two-counter theorem; its relevant loss case was also checked directly.

The result refutes a universal claim that the smallest-upper move is safe
and a blanket nonwinning claim for an orphan-plus-adjacent-pair reserve at
these deficits. It does not refute odd-pair nonloss, which permits other
moves, and does not refute an orphan invariant with additional hypotheses
excluding these states. The source's scope language is appropriate.

No new mathematical computation or bounded game search was performed in
this review. Only source inspection, hashing, and the affected Lean build
were run.

Reviewed SHA-256 snapshots:

- `AdjacentPairGeometryObstruction.lean`:
  `89b45a954923dc5ea93f4c38d0b587019103434ea6912eeb6adcd87e10c14f3e`
- `AdjacentPairGeometryAudit.lean`:
  `2045d3adebc6831efad0c12be048837e747b59c943411da81a4c16d3db594eea`
