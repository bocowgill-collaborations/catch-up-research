> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Uniform descent session artifacts

Start: 2026-09-29 08:43 EDT. Parent report:
`../../CATCHUP_UNIFORM_DESCENT_REPORT_20260929_0843_ET.md`.

## Authoritative proved results

Production modules and their `Audit` partners:

- `../../scripts/catch_up/LowerRayFifthEndpoint.lean`: Q_N(N-4) nonloss, N≥23.
- `../../scripts/catch_up/UniformExactSumDescentObstruction.lean`: precise failure
  of an upper-only exact-sum grammar, not of the outcome conjecture.
- `../../scripts/catch_up/AdjacentPairGeometryObstruction.lean`: failed orphan
  and smallest-upper rules, parametrically.
- `../../scripts/catch_up/AdjacentPairGeometryRepair.lean`: sharp one-orphan
  geometry and positive two-/three-pair repairs.

`GapAccounting.lean` is a proved conditional diagnostic. Its orphan hypotheses
are not established. It is deliberately not a new claimed target theorem.

## Reproducible experiments

Run each Python file from the repository with `python3 -B PATH`. Scripts import
the existing exact recurrence and use no network or third-party solver.
`PROBE_RESULTS.json` retains the final baseline outputs, timings, and hashes.
Elapsed-time fields vary on replay. Values -1, 0, 1 mean loss, draw, win.

- `symbolic_blocks.py --k 4 --depth 5 --radius 6` searches the bounded affine
  exact-sum grammar; `quad_trees.json` is the saved forest.
- `tree_replay.py` checks all affine identities and permitted witnesses for
  m≥17. This is not a substitute for Lean's game-semantics proof.
- `pair_probe.py` tests odd actual adjacent-pair nonloss. The default fixed
  prefix is 691 cases. `--max-cases 722 --seconds 60` replays the earlier
  exploratory prefix when the time limit permits. No surviving prefix is proof.
- `pair_window_probe.py`, `paired_parity_window_probe.py`, and
  `paired_low_deficit_nonwin_probe.py` refute specified broader deficit windows.
- `pair_opening_probe.py` refutes specified greedy opening rules.
- `orphan_probe.py` tests only orphan anchors 2 and 3, not arbitrary a.
- `separated_orphan_probe.py` tests an unproved separated multi-pair extension.
- `even_pair_nonwin_probe.py` and `paired_phase_lift_probe.py` test specific
  deficit-two claims; no general theorem follows from their surviving samples.
- `aligned_pair_window_probe.py` refutes the draw window with aligned pair
  starts. Its optional `--nonwin` mode tests a weaker, unresolved hypothesis.

`QuadCandidate.lean` is an obsolete scratch draft, not a build target or proof
artifact. Use the production endpoint module instead. `AxiomNegativeControl.lean`
is intentionally rejected for the existing conjecture's `sorryAx`; it is not a
production module. Its expected failure is documented in `CHECKS.json`.

`NOTES.md` records checkpoints; `INDEPENDENT_IDEA.md` records the conceptual
helper's arguments. The four `*REVIEW.md` files are independent completed-proof
reviews. `GATES.md` is the final acceptance ledger. No scratch file is imported
by production, and no old report or certificate was overwritten.
