> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseTerminalNonloss](../../CatchUp/DenseTerminalNonloss.lean).

# Terminal gap arithmetic classification, ambient N ≤ 9

The requested arithmetic predicate has **10 block cases, 9 parent-gap cases, and 8 distinct continuing states**. All eight continuing states are nonloss: five draws and three wins. Every terminal result was independently replayed with literal scores, including every legal first pick. This is reproducible finite computational evidence; the proposed Lean classifier and kernel outcome checks are separate proof obligations.

The domain is every `N=0..9`, every `S⊆{1,…,N}`, actual `h=N-|S|`, and every `d,w,B` satisfying

```
2h+1 ≤ d ≤ N; Even(sum(S)+d);
w∈S; w<d; t=d-w; 1≤t<h;
no subset of S sums to t;
B⊆S; sum(B)=d; w∉B;
C=(S\B).erase(w); sum(C)<w.
```

There is no `d∉S`, maximal-block, `max(B)<w`, or game-value filter. This scope agrees with the arithmetic terminal cutoff being developed separately. Every compatible exact block is retained, including nonterminal ones, so omissions are independently checkable.

| N | S | d | w | B | C |
|---|---|---|---|---|---|
| 5 | {2,3,4} | 5 | 4 | {2,3} | ∅ |
| 5 | {2,4,5} | 5 | 4 | {5} | {2} |
| 6 | {2,3,4,5} | 6 | 5 | {2,4} | {3} |
| 7 | {1,3,4,5} | 7 | 5 | {3,4} | {1} |
| 7 | {2,3,4,6} | 7 | 6 | {3,4} | {2} |
| 7 | {1,3,5,6} | 7 | 5 | {1,6} | {3} |
| 7 | {2,4,5,6} | 7 | 6 | {2,5} | {4} |
| 9 | {1,3,4,6,7} | 9 | 7 | {3,6} | {1,4} |
| 9 | {2,3,4,6,8} | 9 | 8 | {2,3,4} | {6} |
| 9 | {2,3,4,6,8} | 9 | 8 | {3,6} | {2,4} |

The old seven full-witness terminal blocks are recovered by requiring `d∉S`, `w>global_b`, and `B` containing the global maximal member of an exact-d block. The three additions above are the N5 block `{5}` (`d∈S` and `max(B)>w`), N7 block `{1,6}` (`max(B)>w`), and N9 block `{2,3,4}` (not globally maximal). The last shares its parent-gap case with `{3,6}`.

The continuing state is `(S.erase(w),t)`, not the terminal residual `(C,w)`. Its complete first-pick values are:

| Continuing S | t | Value | All first-pick outcomes |
|---|---|---|---|
| {2,3} | 1 | draw | 2:loss, 3:draw |
| {2,5} | 1 | win | 2:loss, 5:win |
| {2,3,4} | 1 | draw | 2:draw, 3:draw, 4:loss |
| {1,3,4} | 2 | draw | 1:draw, 3:loss, 4:loss |
| {1,3,6} | 2 | win | 1:win, 3:loss, 6:draw |
| {2,4,5} | 1 | draw | 2:draw, 4:loss, 5:loss |
| {1,3,4,6} | 2 | draw | 1:draw, 3:draw, 4:loss, 6:loss |
| {2,3,4,6} | 1 | win | 2:draw, 3:win, 4:loss, 6:draw |

The independent literal-score replay checks all 9 parent values, all 8 distinct child values, 36 parent first picks, 27 child first picks, and all 10 terminal residuals/tied residual roots. Of those 63 first picks, 38 continue with the same player. It verifies both the actual-score child `absolute(S.erase(w),w,d)` and the normalized child `absolute(S.erase(w),0,t)`. All terminal after-opening states `(C,w)` are losses, and every tied residual `S\B` has a winning opening. No assumed translation or turn alternation was used.

Completeness and resource receipts:

- One unmodified frozen `PackedExactTable(16)`; all 1,114,112 scalar labels independently rechecked once. Only query/parent domain `N≤9` was enumerated; no N expansion.
- The C++ probe enumerates 191 even-density true-gap parent candidates and 328 exact blocks avoiding w. A separate plain-set Python enumeration matches both complete sets, including all terminal flags.
- All ambient N=0..9 complete. Terminal block counts by N are 5:2, 6:1, 7:4, 9:3; other N have zero.
- Compile 1.119s, probe 1.030s externally (internal solver/query timer 0.020s), replay 0.063s. Peak reported compiler RSS 203,784,192 bytes, probe RSS 2,670,592 bytes, replay RSS 17,219,584 bytes: all below the 30s/512MiB bounds.
- `terminal_gap_results.json` retains every candidate and block, plus explicit `unique_terminal_parent_gap_cases`, `terminal_B_cases`, `distinct_continuing_states`, all move outcomes, and scope flags. The nonterminal diagnostic values were not literally replayed; all terminal results were.
- `terminal_gap_run.json` retains exact command arrays, command hashes, output hashes, and resource receipts. `terminal_gap_manifest.json` hashes frozen sources and all new artifacts.

A small Lean closure can define `K : Finset (Finset ℕ × ℕ)` to be the eight continuing pairs above. A precise finite arithmetic classification target is:

```
∀ N ∈ Finset.range 10,
∀ S ∈ (Finset.Icc 1 N).powerset,
∀ d ∈ Finset.Icc 1 N,
∀ w ∈ S,
∀ B ∈ S.powerset,
  TerminalGapArithmetic N S d w B → (S.erase w, d-w) ∈ K
```

Here `TerminalGapArithmetic` is exactly the displayed predicate, with `h=N-S.card`. Prove this finite statement with kernel reduction (`decide +kernel`, if its cost is acceptable), then kernel-check the eight outcome values separately and compose with the independent universal arithmetic cutoff `N≤9`. Alternatively classify the full five-tuples into the ten rows first. This suggestion is not a completed formal proof in these artifacts; `goal_frontier_audit` owns the new Lean closure.

The terminal premise is needed. Existing candidate id14 has N7, S={3,4,5,7}, h3, d7, w5, t2 and a true subset-sum gap, but continuing child `{3,4,7}`, deficit2 is a table loss. Both compatible blocks are nonterminal. This existing table diagnostic was forwarded to prevent replacing the arithmetic classifier with an invalid all-small-gap assertion; it was not an additional experiment.
