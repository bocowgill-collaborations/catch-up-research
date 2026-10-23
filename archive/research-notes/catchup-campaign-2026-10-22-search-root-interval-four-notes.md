> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Fixed actual-interval entry4 test

All **51 opponent endpoints** completed and passed independent literal-score replay. The proposed first pick4 **fails at N12**. It draws at exactly the other five tested N:11,15,16,19,20. Every tested full E1 state draws; this is a counterexample to the fixed entrance policy, not to interval nonloss or the original conjecture.

The exact fixed domain is N∈{11,12,15,16,19,20}, `E={4,7}∪[9,N]`, initial deficit1, candidate first pick4. This ends the original player's turn at actual scores4 versus1 and leaves the opponent at `F={7}∪[9,N]`, deficit3. Since **min(F)=7>3**, every first pick y reaches/passes3; every completed opponent whole turn is exactly a singleton `{y}`. Conversely every y∈F is legal. Thus the waiting original player returns at `(F.erase(y),y-3)`, and

```
entry4 = -V(F,3) = min_y V(F.erase(y),y-3).
```

For each fixed N, entry4 is nonloss exactly when all its endpoints are nonloss, equivalently F3 is nonwinning. The endpoint counts are4+5+8+9+12+13=51; no multi-pick opponent turn was excluded by an outcome assumption.

| N | E1 | F3 | Entry4 | Endpoint LOSS/DRAW/WIN | Safe E1 first picks |
|---:|---|---|---|---|---|
| 11 | DRAW | DRAW | DRAW | 0 /1 /3 | {4} |
| 12 | DRAW | WIN | LOSS | 2 /1 /2 | {7} |
| 15 | DRAW | DRAW | DRAW | 0 /6 /2 | {4,9,10,11,13,14} |
| 16 | DRAW | DRAW | DRAW | 0 /3 /6 | {4,7,10,11,12} |
| 19 | DRAW | DRAW | DRAW | 0 /12 /0 | {4,9,10,11,12,13,14,15,16,17,18,19} |
| 20 | DRAW | DRAW | DRAW | 0 /13 /0 | {4,7,9,10,11,12,13,15,16,17,18,19,20} |

At N12 the complete E1 first-pick map is `4:L,7:D,9:L,10:L,11:L,12:L`. All six values were independently checked literally, as was the actual E1 draw. After first4, opponent7 leaves `({9,10,11,12},4)=LOSS`; opponent9 leaves `({7,10,11,12},6)=LOSS`. Every legal first pick of both losing endpoints was literally checked and loses. The other N12 endpoints have values y10:DRAW,y11:WIN,y12:WIN; the complete F3 first-pick map was also replayed.

Every one of the51 endpoint values was evaluated literally both as normalized scores `(0,y-3)` and actual scores `(4,1+y)`. All matched:2 losses,36 draws,13 wins. There are no skipped, missing, or capped endpoint values. The literal root/first-pick replay scope is N12 only; the other E1 roots and all57 first-pick values across the six supports are native ExactSlots data. Their full maps and safe-choice arrays are retained in the combined JSON. A separate same-support helper/log preserves the original complete endpoint probe receipts.

`root_interval_four_results.json` is the combined result. `root_interval_four_endpoint_results.json` preserves the completed51-endpoint literal receipt before the first-pick metadata join, with its hash linked from the combined result. Sources, logs and exact command/hash/resource receipts are in the same new prefix. The manifest hashes those artifacts and frozen solver/literal sources.

The unchanged `seven_pairs/slots.hpp` was used with at most14 actual counters and labels≤20; no interval table or larger N was used. Native original compile/probe0.936s; same-support first-pick compile/probe0.824s; literal replay2.152s; metadata join0.023s, about3.935s total. Peak compiler RSS132,694,016 bytes; native solver2,162,688 bytes; literal23,658,496 bytes. All bounds30s/512MiB were met. No further strategy batch, ad-hoc repair, or N expansion followed this fixed test.
