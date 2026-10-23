> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up local-exchange report — September 23, 2026, 18:20 EDT

## Verdict

The requested forbidden-jump lemma is **not proved and not refuted**.

This run produced two rigorously certified obstructions to proposed proof mechanisms:

1. In the original admissible family, the natural counter correspondence can send **every nonlosing move** in the winning right game to a losing move in the left game. Direct strategy copying therefore fails immediately, even before either exceptional counter is taken.
2. Alternating parity and an arbitrary number of disjoint adjacent-pair erasures do **not** prevent the jump. A six-counter counterexample also shows that the neighbor-jump implication has no converse: a distant reply can save the middle opening.

These are mechanism obstructions, not a proof or counterexample to the original one-pair-root statement. No general Catch-Up theorem or certified interval frontier was advanced.

## Repository and scope

- Starting commit: `ffc6e65836cd2599af92b3513ff07ddefc564c2d`.
- Starting local branch: `codex/catchup-endpoint-20260923`.
- New branch: `codex/catchup-adjacent-jump-20260923`.
- Worktree: `HISTORICAL_TMP/catchup-adjacent-jump-20260923`.
- Repository remote in this checkout: `collaboration` points to `the historical private research remote`; `origin` still names the upstream repository. **No push or merge was performed.**
- Start: 17:44:59 EDT; hard deadline: 18:44:59 EDT.
- Read the September endpoint report and relevant August final handoff. Also checked the earlier campaign discussion of abstract no-jump failures and the existing four-boundary reduction.
- Existing reports, certificates, and production files from the starting commit were preserved. Only new files belong to this run.
- Used one independent reviewer, after the first complete candidate existed; the same reviewer checked subsequent completed refinements.

## Exact target and polarity

Write \(R_{N,b}=\{1,\ldots,N\}\setminus\{1,b-1,b\}\). The target assumes
\(N\ge11\), even \(N(N+1)/2\), \(3\le b\le N\), and
\(y-1,y,y+1\in R_{N,b}\). It asks to exclude
\[
 \operatorname{value}(\langle R_{N,b}\setminus\{y-1,y\},1\rangle)=\mathrm{loss},
 \qquad
 \operatorname{value}(\langle R_{N,b}\setminus\{y,y+1\},1\rangle)=\mathrm{win}.
\]

The existing `after_opening_loss_forces_neighbor_value_jump` API was inspected and axiom-audited. Its direction is correct:

- Values are from the **current mover's** perspective.
- After opening \(y\), the deficit is \(y\).
- Picking \(y-1\) continues the same turn, yielding the left state at deficit one.
- Picking \(y+1\) switches players, yielding the right state at deficit one and negating its value.
- A losing post-opening position therefore forces left loss and right win.
- The converse is false in general; see the certified example below.

The exact executable recurrence is:
\[
 F(S,d)=
 \begin{cases}
 0,&S=\varnothing,\ d=0,\\
 -1,&S=\varnothing,\ d>0\text{ or }\sum S<d,\\
 \max_{x\in S}
 \begin{cases}
 F(S\setminus\{x\},d-x),&x<d,\\
 -F(S\setminus\{x\},x-d),&x\ge d,
 \end{cases}&\text{otherwise}.
 \end{cases}
\]
Here \(-1,0,1\) mean loss, draw, win. Equality switches players. Counter \(x\) is bit \(x-1\); zero is never a counter. Recursion strictly removes a counter.

## Exhaustive finite gate

The checker enumerates every admissible \(b,y\) at each listed size. No random choices or floating-point arithmetic enter these tests.

| N | Tested triples (N,b,y) | (draw,draw) | (draw,win) | (win,draw) | Forbidden jumps |
|---|---:|---:|---:|---:|---:|
| 11 | 42 | 33 | 4 | 5 | 0 |
| 12 | 56 | 51 | 2 | 3 | 0 |
| 15 | 110 | 110 | 0 | 0 | 0 |
| 16 | 132 | 132 | 0 | 0 | 0 |
| 19 | 210 | 210 | 0 | 0 | 0 |
| 20 | 240 | 240 | 0 | 0 | 0 |
| **Total** | **790** | **776** | **6** | **8** | **0** |

In fact neither neighboring state loses in these tests. This is finite evidence, not a parametric theorem. No large interval tables were regenerated; the probe refuses interval sizes above 20. The sparse six-counter example below is not a table for size 23.

## Certified obstruction inside the requested family

Take \(N=11,b=4,y=8\). Then
\[
 R=\{2,5,6,7,8,9,10,11\},\quad
 U=\langle\{2,5,6,9,10,11\},1\rangle,\quad
 V=\langle\{2,5,6,7,10,11\},1\rangle.
\]
All requested hypotheses hold, including triangular total 66. Lean proves \(U\) draws and \(V\) wins.

Let \(\phi:V\to U\) fix common counters and replace \(7\) by \(9\). The complete move profiles, measured from the parent mover, are:

| V counter x | U counter φ(x) | V move outcome | U move outcome |
|---|---|---|---|
| 2 | 2 | loss | draw |
| 5 | 5 | win | loss |
| 6 | 6 | loss | loss |
| 7 | 9 | loss | loss |
| 10 | 10 | draw | loss |
| 11 | 11 | loss | loss |

The main exact theorem is `CatchUp.AdjacentHoleExchange.safe_right_move_copies_to_loss`:
for every legal right move \(x\),
\[
 V.\mathrm{moveOutcome}(x)\ne\mathrm{loss}
 \Longrightarrow U.\mathrm{moveOutcome}(\phi(x))=\mathrm{loss}.
\]

Thus even choosing freely among all right nonlosing first moves cannot make direct copying work. The proof cannot postpone every repair until the exceptional counter is selected.

### Forced first repair

If one simultaneous first pick preserves a right **win** and a left **nonloss**, the picks are uniquely \(u=2,v=5\). The resulting positions are
\[
 U'=\langle\{5,6,9,10,11\},1\rangle,\qquad
 V'=\langle\{2,6,7,10,11\},4\rangle.
\]
Both now have the other player to move. Their deficit difference is 3, and their unmatched sets are \(\{5,9\}\) and \(\{2,7\}\).

The theorems `forced_first_repair` and `forced_first_repair_endpoints` certify this. A synchronous one-pick repair preserving those outcomes must therefore accommodate two unmatched counters on each side and gap difference three.

**Scope:** this is not a lower bound on every asynchronous or completed-turn construction. It does not refute a proof that additionally exploits a hypothetical left loss. It refutes the specified unconditional first-move transport mechanism.

## Certified failure of the alternating-parity / arbitrary-pair extension

Deleting adjacent pairs preserves alternating even/odd order of the remaining counters. That suggested a structural strengthening. It is false:
\[
 \operatorname{value}(\langle\{6,11,14,15,18,23\},1\rangle)=\mathrm{loss},
 \quad
 \operatorname{value}(\langle\{4,11,14,15,18,23\},1\rangle)=\mathrm{win}.
\]
Both sorted supports alternate even, odd, even, odd, even, odd. Their effective totals are 88 and 86.

These are exact neighboring states at \(y=5\) of
\[
 R^*=\{4,5,6,11,14,15,18,23\}
 =\{2,\ldots,23\}\setminus
   \bigcup_{a\in A}\{a,a+1\},
 \quad A=\{2,7,9,12,16,19,21\}.
\]
Lean checks the seven pairs are disjoint, lie in the interval, and \(23\cdot24/2=276\) is even. Each neighboring support therefore deletes eight disjoint adjacent pairs from the interval.

This refutes the **arbitrary-pair-erasure extension of no-jump**. It does not refute the original root with exactly one erased pair. It also does not establish failure of a conditional hereditary theorem whose premise has not been checked.

### A useful non-converse

Despite the neighbor jump, Lean proves
\[
 \operatorname{value}(\operatorname{afterOpening}(R^*,5))=\mathrm{draw}.
\]
The reply 11 has draw outcome, also certified in `parity_root_reply_eleven_draw`. The exact checker identifies it as the unique drawing reply; both neighbors 4 and 6 lose from the post-opening mover's perspective.

Consequently, a neighbor jump does not itself establish a winning opening. A successful direct attack on winning openings may exploit distant replies even where a stronger no-jump assertion fails.

## Search decisions and remaining gap

- **Natural one-counter correspondence:** blocked by the admissible first-move certificate.
- **Parity order alone / unrestricted number of adjacent holes:** false by the six-counter certificate.
- **Two-unmatched-counter or asynchronous repair:** not proved or exhaustively tested. The forced pair \((U',V')\) above is a concrete necessary test instance for a synchronous repair, not a proposed invariant assumed to work.
- The older abstract two-unit-replacement counterexample was reproduced but is not counted as new.
- The four-boundary classification was already in `LowerRayInteriorReduction.lean`; it was not reimplemented or counted as new.

The exact remaining local obligation is the original no-jump statement for **all** admissible \(N,b,y\). Neither a global strategy, a well-founded repair relation, nor a parametric invariant has been supplied.

Even if that statement is proved later, it excludes only winning openings with both neighbors present. The candidates
\(\{2,b-2,b+1,N\}\cap R_{N,b}\) still require treatment. Nonwinning alone is not a proof that the residual draws; the other outcome direction remains separate.

The September endpoint transfer and the August campaign's unresolved lower-ray, shifted-tail, and anchor obligations remain unchanged.

## Verification and trust

- Warning-strict scoped build of the two new Lean modules passed.
- Every one of the 18 new public theorems, plus the existing forced-neighbor API, is checked by an executable axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorryAx`, new mathematical assumptions, `native_decide`, compiler-trust axioms, or dependence on the Catch-Up conjecture occurs in these proofs.
- Finite evaluations use `decide +kernel` through the existing classifier's proved equivalence with `CanAvoidLoss` and the actual minimax value.
- Independent absolute-score minimax **without early pruning** agrees on 2,176 small states: all \(S\subseteq\{1,\ldots,7\}\), \(0\le d\le\sum S+2\).
- The same independent recurrence verifies five principal witness states and all 31 of their legal first moves.
- One independent reviewer passed the complete move profiles, admissibility, player switches, terminal conventions, forced repair, sparse geometry, and limitations. Its key caution is reflected above: no claim against all adaptive or contradiction-based couplings.

## Files and reproduction

New files:

- Lean certificates (`scripts/catch_up/AdjacentHoleExchangeObstruction.lean`; historical path)
- Axiom audit (`scripts/catch_up/AdjacentHoleExchangeAudit.lean`; historical path)
- Exact checker (`scripts/catch_up/adjacent_jump_probe.py`; historical path)
- Independent unpruned regression (`scripts/catch_up/test_adjacent_jump_probe.py`; historical path)
- Saved results (`scripts/catch_up/adjacent_jump_results_20260923.jsonl`; historical path)
- This timestamped report.

Run from the worktree root:

```bash
python3 -B scripts/catch_up/adjacent_jump_probe.py --sizes 11 12 15 16 19 20
python3 -B scripts/catch_up/test_adjacent_jump_probe.py
lake --wfail build catch_up.AdjacentHoleExchangeObstruction catch_up.AdjacentHoleExchangeAudit
git diff --check
```

The next focused experiment, if desired, is a history-aware repair with two unmatched counters, starting with the forced \((2,5)\) pair above. It needs explicit adversarial transition closure and a strictly decreasing measure. Merely defining the relation by safe outcomes or by existence of the desired strategy would restate the missing theorem.
