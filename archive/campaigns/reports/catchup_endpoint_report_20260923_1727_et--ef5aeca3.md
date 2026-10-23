> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up endpoint transfer — 2026-09-23, 17:27 EDT

## Result

**Proved.** For every natural number `N ≥ 7`, a draw after opening one in the
interval of size `N - 4` implies that the lower-ray state at `b = N - 2`
cannot be a loss. The proof is symbolic and has no parity assumption.

This closes the requested conditional endpoint. It does not prove the full
Catch-Up conjecture or extend the certified finite frontier.

Work began at 17:27 EDT. The first complete proof and independent review were
finished by 17:38 EDT. Final scoped verification passed at 17:40 EDT, within
the one-hour limit.

## Repository and deliverables

- Base: `codex/catchup-campaign-20260812`, commit
  `313f86dd98b8d53ac6bd31b2423124343edef50c`.
- New local branch: `codex/catchup-endpoint-20260923`.
- Isolated worktree: `HISTORICAL_TMP/catchup-endpoint-20260923`.
- Proof: LowerRayAntepenultimateDescent.lean (`scripts/catch_up/LowerRayAntepenultimateDescent.lean`; historical path).
- Reproducible statement and axiom audit:
  LowerRayAntepenultimateDescentAudit.lean (`scripts/catch_up/LowerRayAntepenultimateDescentAudit.lean`; historical path).

The previous temporary checkout and incomplete August attempt were absent.
The proof was reconstructed from committed APIs. Existing reports, certificates,
toolchain pins, and dependency manifests were preserved. The work is committed
locally; no push or merge is part of this task.

## Exact theorem

In namespace `CatchUp`:

```lean
theorem pair_deletion_position_antepenultimate_value_ne_loss_of_opening_one_draw
    (N : ℕ) (hN : 7 ≤ N)
    (hdraw : (afterOpening (Finset.Icc 1 (N - 4)) 1).value = .draw) :
    (pairDeletionPosition N 1 (N - 2)).value ≠ .loss
```

The existing definition is

```lean
def pairDeletionPosition (N a b : ℕ) : Position :=
  ⟨((Finset.Icc 1 N).erase a).erase b, b - a⟩
```

Thus the conclusion is exactly nonloss for remaining counters
`I_N \ {1, N-2}` and deficit `N-3`. The audit module proves this
set-difference formulation explicitly, checking both the support and the
natural-number subtraction.

The hypothesis concerns the value **after the specified opening one**.
A draw for the smaller game's root alone does not supply this hypothesis:
the existing draw-opening theorem guarantees some drawn opening, without
identifying it as one.

## Proof

Write `S = I_N \ {1, N-2}` and `d = N-3`. Suppose `Position(S,d)`
loses. Since `N ≥ 7`, the counter `d` belongs to `S`.

Apply the existing theorem
`loss_with_available_deficit_forces_large_unique_winning_opening`.
It gives a counter `y` in the tied residual

```text
R = S \ {d} = I_N \ {1, N-3, N-2}
```

such that `y > N-3` and `afterOpening R y` loses for its player to move.
Membership and the strict lower bound leave exactly `y = N-1` or `y = N`.
The uniqueness portion of the existing theorem is not needed afterward.

If `y = N-1`, respond with `N`. This is an available counter and a catching
move. The remaining support is `I_(N-4) \ {1}`, and the new deficit is one.
Lean proves the exact identity

```lean
(afterOpening R (N - 1)).afterPick N =
  afterOpening (Finset.Icc 1 (N - 4)) 1
```

The right side draws by hypothesis. Changing perspective negates its outcome,
and the negation of draw is draw. Therefore the response is a drawing move.

If `y = N`, respond with `N-1`. This response continues the current turn,
rather than catching. The existing theorem
`move_outcome_after_opening_comm` says that swapping the first two distinct
counters negates the second-pick outcome. The first case's draw therefore
makes this response a draw as well. The support and deficit are the same.

A position with an available drawing move cannot lose. The private helper
`value_ne_loss_of_draw_move` verifies this without assuming away terminal
pruning: if the remaining sum were below the deficit, the existing
`Position.move_outcome_eq_loss_of_sum_lt_deficit` would make every available
pick losing, contradicting the drawing move. Otherwise the minimax recurrence
contains a draw and its best outcome is not loss.

Both cases contradict the residual post-opening loss.

## Checks and trust

Pinned environment: Lean `v4.27.0`; mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Matching locally available
dependency caches were copied into this isolated worktree.

The changed scope passed:

```sh
lake --wfail build catch_up.LowerRayAntepenultimateDescent \
  catch_up.LowerRayAntepenultimateDescentAudit
```

Result: `Build completed successfully (8058 jobs).` The job count includes
the imported dependency graph; this was a scoped target build, not a full
repository build.

The audit uses `Lean.collectAxioms` and fails if either the production theorem
or its set-difference restatement uses an axiom outside:

```text
propext
Classical.choice
Quot.sound
```

Both have exactly those three axioms. There is no `sorryAx`, native-evaluation
axiom, or project-declared axiom in either proof's dependency footprint.
The production module contains no `sorry`, `admit`, `native_decide`,
or declared `axiom`. Its only theorem hypothesis beyond the bound on `N`
is the stated smaller opening-one draw.

One independent reviewer, assigned only after the complete candidate compiled,
returned **PASS**. The review checked statement fidelity, subtractions, move
availability, terminal pruning, both outcome polarities, imports, and
non-circularity. At the smallest required boundary `N=7`, the tied residual
is `{2,3,6,7}`; either top-counter order leaves `{2,3}` with deficit one,
exactly the opening-one state at size three.

Source hashes:

```text
LowerRayAntepenultimateDescent.lean
bd14a01eac8c06631601f380c6bdcbabff2f3d5f6940b1331c0bb90a7d47b20a

LowerRayAntepenultimateDescentAudit.lean
e8d782ac7e920159fe6845ec71f9d0854d4b9c5937b96742fc8822e28c196052
```

## Remaining obligations

Using the August report's notation,

```text
A(N,b)  = pairDeletionPosition N 1 b
B(N,x)  = Position ((Icc 3 N).erase x) (x-1)
TA(N,b) = ((Icc 2 N).erase (b-1)).erase b
TB(N,x) = ((Icc 3 N).erase (x-1)).erase x
```

the progress and gaps are:

- `A(N,N)` and `A(N,N-1)` were already nonlosing under their existing
  size bounds.
- `A(N,N-2)` is now nonlosing whenever opening one at size `N-4` draws.
- `A(N,2)` and the interior `3 ≤ b ≤ N-3` remain unresolved uniformly.
- The endpoint `B(N,3)` and the interior `4 ≤ x ≤ N-2` are untouched.
- The stronger claim `value(TA(N,N-2)) ≠ win` is **not** established here.
  The new proof instead excludes the two possible winning residual openings
  under the smaller-draw hypothesis.
- A full induction still needs to establish and propagate its opening-one draw
  premise, together with the remaining ray conditions. This endpoint theorem
  alone does not provide that induction.

The next bounded task should formalize how this endpoint fits into a lower-ray
induction interface, stating all remaining assumptions explicitly, or attack
one of the endpoint states `A(N,2)` and `B(N,3)`. Reusing the present theorem
requires a proved opening-one draw at the smaller size; assuming the main
conjecture, or silently replacing this premise with an arbitrary root draw,
would not close the gap.
