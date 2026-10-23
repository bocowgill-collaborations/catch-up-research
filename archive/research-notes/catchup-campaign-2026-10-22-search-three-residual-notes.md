> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseThreeResidual](../../CatchUp/DenseThreeResidual.lean).

# Three-counter residual audit

The complete arithmetic domain has **142 configurations**. Exactly **20** have `V(C,w)=LOSS`, matching the saved 20 full-F blocks without additions or omissions. They give 19 distinct continuing states: 15 ambient cases draw and 5 win. **Every qualified case has a safe first pick in B.** The smallest B-element fails in one case, so a fixed minimum-B rule remains false.

Scope: `S=B⊔C⊔{w}⊆{1,…,N}`, `|C|=3`, `k=|B|∈{2,3}`, actual `h=N-|S|`, `2h+1≤d=sum(B)≤N`, even `sum(S)+d`, `b=max(B)` globally maximal among members of every exact-d subset of S, `b<w<d`, and true original-S subset-sum gap `t=d-w∈[1,h)`. No game-value condition was used in the arithmetic enumeration. Global maximality forces `d∉S`: otherwise singleton `{d}` would have maximum d>w>b. Every static row records that fact.

The structured scan uses exactly the proposed A lists, `A=B.erase(b)`: singles 1..5 for k2; pairs 12,13,14,15,23,24 for k3. A second support-first enumeration permits all B of size 2 or 3, with no A-list restriction. The two complete configuration sets agree exactly. Arithmetic counts by ambient N are 9:13, 10:30, 11:58, 12:15, 13:26; all other N≤13 have zero. Frozen ExactSlots classifies their three-counter shadows as 20 losses, 29 draws, 93 wins. All 142 shadow values received independent literal-score replay.

| N | B | C | d | w | t | Chosen safe B pick | Continuing value |
|---:|---|---|---:|---:|---:|---:|---|
| 9 | {2,5} | {3,8,9} | 7 | 6 | 1 | 2 | draw |
| 10 | {4,5} | {1,7,10} | 9 | 6 | 3 | 4 | win |
| 10 | {4,5} | {2,8,10} | 9 | 6 | 3 | 4 | win |
| 10 | {4,5} | {3,8,10} | 9 | 7 | 2 | 5 | draw |
| 10 | {3,7} | {4,5,6} | 10 | 9 | 1 | 3 | draw |
| 10 | {2,8} | {4,5,6} | 10 | 9 | 1 | 2 | draw |
| 11 | {1,3,5} | {4,10,11} | 9 | 7 | 2 | 3 | draw |
| 11 | {1,3,7} | {4,5,6} | 11 | 9 | 2 | 3 | draw |
| 11 | {3,8} | {4,5,6} | 11 | 9 | 2 | 3 | draw |
| 11 | {3,8} | {5,6,7} | 11 | 10 | 1 | 3 | draw |
| 11 | {2,9} | {5,6,7} | 11 | 10 | 1 | 2 | draw |
| 11 | {4,7} | {5,9,10} | 11 | 8 | 3 | 4 | win |
| 12 | {1,3,7} | {4,5,6} | 11 | 9 | 2 | 3 | draw |
| 12 | {1,3,8} | {5,6,7} | 12 | 10 | 2 | 3 | draw |
| 12 | {2,3,7} | {5,6,8} | 12 | 11 | 1 | 2 | draw |
| 13 | {1,4,8} | {5,6,7} | 13 | 10 | 3 | 4 | draw |
| 13 | {1,3,9} | {5,6,8} | 13 | 11 | 2 | 3 | win |
| 13 | {1,3,9} | {6,7,8} | 13 | 11 | 2 | 3 | draw |
| 13 | {1,5,7} | {6,10,11} | 13 | 9 | 4 | 5 | win |
| 13 | {2,3,8} | {6,7,9} | 13 | 12 | 1 | 2 | draw |

The N11/N12 rows with B={1,3,7}, C={4,5,6}, d11,w9 repeat the same game at different ambient N. All other qualified game keys differ. Ten cases have B-cardinality 2 and ten have cardinality 3. All 142 static configurations, and hence all qualified cases, are nonterminal (`sum(C)≥w`).

All **110** legal friendly first picks were replayed literally, including 10 picks that continue with the same player. There are 58 safe friendly first picks, including 37 safe B picks. Safe-B counts per case are: five cases have one, thirteen have two, two have three; none has zero. The chosen controller uses the least safe B pick that ends the friendly turn. Such a pick exists in all 20 cases, is strictly greater than t, and has move value DRAW. This certifies nonloss even in the five states whose optimal value is WIN.

After those entries, every **90** completed opponent whole turns was enumerated and replayed with literal scores. Endpoint values are 64 wins and 26 draws for the original player, with no losses. For each opponent deficit c, all nonempty subsets Y of the remaining counters were checked against `c≤sum(Y)<c+max(Y)` (with the separate tied-state singleton convention available in code). The independent enumeration shows that all 90 actual legal turns in this selected domain happen to be singletons; multi-pick turns were not omitted by a single-pick assumption. Every endpoint was verified both at actual scores `(friendly_score, t+sum(Y))` and normalized deficit `sum(Y)-c`. Each full residual also has its unique winning opening w independently replayed.

The sole minimum-B failure is arithmetic row26: N10, S={3,4,5,7,8,10}, B={4,5}, C={3,8,10}, d9,w7,t2. The continuing first-pick map is `3:L,4:L,5:D,8:L,10:L`. Thus min B=4 loses, while B-pick5 draws. This reproduces the earlier minimum-entry diagnostic; the broader existential B-entry claim has no counterexample in the complete c3 family.

The arithmetic cutoff pre-audit is independent of parity and shadow value. Set `q=sum(A)=d-b`. The h disjoint pairs `{j,d-j}` for j=1..h lie in [1,N] because `2h+1≤d≤N`. If none were wholly in S, one hole per pair plus the distinct missing d would require h+1 holes. Therefore some exact-d pair has maximum at least d-h; global maximality yields `b≥d-h`, hence `t<q≤h`. Since `|S|=k+4`, density and d≤N give `h≤k+3`. Thus `k(k-1)/2≤q≤k+3`, excluding k≥5. If k4, A is a three-element positive set of sum at most7, hence {1,2,3} or {1,2,4}; each represents every 1≤t<q, contradicting the true gap. Hence k≤3, N≤2k+7≤13, with exactly the listed A possibilities. This is an audited proof sketch for the formal worker, not a kernel theorem in this artifact.

Files: `three_residual_arithmetic.json` retains all 142 static rows and the independent scan comparison; `three_residual_results.json` retains all shadow values, all 20 qualified cases, every legal first-pick value, safe B sets, chosen entries, all opponent turn/endpoint values, and source-key comparison. `three_residual_run.json` stores exact commands, hashes, and resource receipts; `three_residual_manifest.json` hashes all new artifacts and frozen sources. These were sent directly to `goal_frontier_audit` for finite classifier planning.

No interval table was built. The unmodified frozen `seven_pairs/slots.hpp` handled only 3-counter shadows and 5/6-counter continuing states. External times: arithmetic0.042s, compile0.791s, probe0.310s, literal replay0.046s (total1.190s). Peak compiler RSS142,491,648 bytes, probe1,589,248 bytes, literal15,532,032 bytes. All jobs stayed below30s/512MiB. No files outside the new `three_residual_*` ownership were changed. Formal c3 closure still requires the kernel classifier/composition; finite computation alone is not the theorem.
