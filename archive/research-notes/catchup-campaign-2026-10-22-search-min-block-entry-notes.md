> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseBlockEntryObstruction](../../CatchUp/DenseBlockEntryObstruction.lean).

# Minimum-block entry and every opponent whole turn

The proposed minimum-block entrance fails in a nonterminal full strategic witness at **N10**. More strongly, **N11** has a full witness where both block elements lose as first picks; the only safe first pick belongs to C. Thus a controller restricted to entering through `{a,b}` cannot cover the full nonterminal domain.

The domain is exactly the 69 two-element blocks among the previously completed 95 full strategic block witnesses, all ambient N≤16. Their inherited conditions include even effective total, actual holes h, `2h+1≤d≤N`, `d∉S`, true original-S subset-sum gap `t=d-w∈[1,h)`, globally maximal exact-d block member b, `w>b`, and actual winning opening w of the tied residual `S\{a,b}`. Writing `B={a<b}`, `C=(S\B).erase(w)`, we have `V(C,w)=LOSS`, `c=a-t>0`, and `w=b+c`. No N expansion or broader state search was performed.

All 69 cases and all 375 legal opponent whole turns completed. The full frozen N16 table passed the scalar checker on 1,114,112 labels. Independent plain-set enumeration separately matched every whole-turn subset.

| Domain | Cases | Entry a loss/draw/win | Both a,b lose | Safe friendly picks / all picks | Opponent whole turns |
|---|---:|---|---:|---:|---:|
| Nonterminal `sum(C)≥w` | 62 | 10 / 49 / 3 | 5 | 198 / 401 | 360 |
| Terminal `sum(C)<w` | 7 | 2 / 4 / 1 | 1 | 12 / 22 | 15 |

The smallest diagnostics use order `(N,h,d,mask,w,B)`; in particular, the smallest ambient N is exhausted before either finding.

**First nonterminal failure of picking a:** N10, h4, S={3,4,5,7,8,10}, d9, w7, t2, B={4,5}, c2, C={3,8,10}. The low state is `({3,4,5,8,10},2)`, which draws. Its full first-pick outcomes are `3:L,4:L,5:D,8:L,10:L`; only b=5 is safe. After a=4, every legal opponent whole turn is:

| Opponent Y | Original endpoint | Deficit | Value |
|---|---|---:|---|
| {3} | {5,8,10} | 1 | win |
| {5} | {3,8,10} | 3 | loss |
| {8} | {3,5,10} | 6 | win |
| {10} | {3,5,8} | 8 | win |

**First nonterminal failure of both block entrances:** N11, h4, S={4,5,6,7,8,10,11}, d9, w6, t3, B={4,5}, c1, C={7,8,10,11}. The low state `({4,5,7,8,10,11},3)` draws; its complete first-pick map is `4:L,5:L,7:L,8:D,10:L,11:L`. Hence only the C-element 8 is safe. After a=4, every legal opponent whole turn is:

| Opponent Y | Original endpoint | Deficit | Value |
|---|---|---:|---|
| {5} | {7,8,10,11} | 4 | loss |
| {7} | {5,8,10,11} | 6 | win |
| {8} | {5,7,10,11} | 7 | win |
| {10} | {5,7,8,11} | 9 | win |
| {11} | {5,7,8,10} | 10 | win |

The five nonterminal both-unsafe cases are source-sorted case IDs 20,35,48,53,56 in the complete JSON. All ten nonterminal minimum-entry failures, both terminal minimum-entry failures, and the equality diagnostic received independent literal-score replay of **every** legal opponent whole turn, every friendly initial pick, and every applicable later b reply: 13 cases, 70 whole turns, 79 friendly picks, and 56 b replies. Replay also verifies the full residual premise `V(C,w)=LOSS`. The remaining safe-case values are table diagnostics, not additional literal replay claims.

For a low state `L=S.erase(w)` at deficit t, picking a ends the original player's turn and leaves the opponent at `(C∪{b},c)`. A nonempty subset Y is an attainable whole turn exactly when

```
c ≤ y=sum(Y) < c+max(Y).
```

The canonical order takes all of `Y\{max(Y)}` first, then `max(Y)`. Every earlier prefix is strictly below c, and the last pick reaches or exceeds it. Equality y=c switches roles and leaves the original player at deficit 0. The original player's endpoint is `((C∪{b})\Y,y-c)`. The minimum of all endpoint values matched the exact move value of a in every case.

The three reply branches are completely retained:

- **b∈Y:** 75 turns (68 nonterminal). Then `Y=Z∪{b}`, `sum(Z)=z<c`, and b is the largest/last element. The endpoint is `(C\Z,b+z-c)`, with correct deficit `w-2c+z = (w-z)-2(c-z)`. Across all 75 endpoints: 12 losses, 57 draws, 6 wins. All observed losing-entry replies lie here.
- **b∉Y, y≠w:** all 299 cases align with the losing shadow and playing b wins: 164 below-w, 135 above-w. For y<w, Y is a continuing shadow prefix, leaving `V(C\Y,w-y)=LOSS`; playing b switches to that losing opponent state. For y>w, max(Y)-last is a legal shadow whole turn, leaving `V(C\Y,y-w)=WIN`; playing b continues in that winning state. These deductions describe the exact recurrence conditional on the shadow loss, and are suitable for a later proof.
- **b∉Y, y=w:** exactly one equality hazard. The endpoint can be nonloss while blind b loses, because b equals the current deficit and switches roles. Here the shadow whole turn gives `V(C\Y,0)=WIN`, so original b-play has value LOSS.

The equality case is N13, h5, S={2,4,5,6,7,8,10,13}, d11, w10, t1, B={4,7}, c3, C={2,5,6,8,13}. After initial a4, opponent order `(2,8)` is legal: the first pick leaves it behind and the last gives y10=w. The original endpoint `({5,6,7,13},7)` draws, but b7 ties and switches to the opponent, so it loses. All ten legal whole turns of this case were independently replayed, not only `(2,8)`.

The initially suggested reflected expression `w-2(c-z)` contains an arithmetic error. The first run stopped on the first z>0 case (N11, case18), before completing its domain. Its source, failed log, and run receipt are preserved as `min_block_entry_probe_initial.cpp`, `min_block_entry_probe_initial.log`, and `min_block_entry_initial_run.json`. The corrected completed run uses `(w-z)-2(c-z)`. The same unmodified N16 table was rebuilt for this correction; no larger table was used. A routine replay parser failure is also retained in the run receipts; the corrected replay completed.

The completed run took 1.023s compile, 1.721s externally for the probe (internal solver/query timer 0.020s), and 0.056s successful replay. Including the initial equation-check attempt and parser failure, total external jobs used about 5.124s. Peak compiler RSS was 205,078,528 bytes; completed probe RSS 2,392,064 bytes; literal replay RSS 17,285,120 bytes. Every job remained below 30s and 512MiB.

`min_block_entry_results.json` retains all 69 case records, every friendly first-pick outcome, all 375 whole turns and endpoints, branch/equality checks, exact failure IDs, and literal replay flags. `min_block_entry_run.json` and `min_block_entry_initial_run.json` retain commands/hashes/resources. `min_block_entry_manifest.json` hashes all artifacts, the source 95-witness file, and frozen solver/literal sources. No Lean source or existing artifact was edited. These findings falsify concrete entry policies; they do not refute the full nonloss claim or solve its remaining nonterminal branch.
