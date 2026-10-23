> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.AlternatingTailObstruction](../../CatchUp/AlternatingTailObstruction.lean).

The generic alternating-tail claim is false. The approved fixed batch found T={19,36,37,52,57,62,101}, E={4,7} union T, deficit1, with value LOSS. All nine legal first picks (4,7,19,36,37,52,57,62,101) have outcome LOSS, independently confirmed by literal-score replay. The tail sum is364; its ranks are odd/even/odd/even/odd/even/odd and minT=19>=9. The effective total sum(E)+1=376 is even.

The exact proposed claim was: for sorted T with minT>=9, alternating odd/even ranks starting odd and Even(sumT), V({4,7} union T,1) is NONLOSS. This counterexample refutes that generic claim. Its optional contexts are E3=WIN, C8=WIN, C2=DRAW and (C\{2},4)=WIN, where C={2,3,4,7} union T. In particular this is neither a two-anchor jointLOSS counterexample nor a counterexample to the conditional B reflection or to an actual contiguous interval/root C conjecture.

The batch was fixed before solving and independently approved by the parent. It used all subsets of sizes3,4,7,8 from {18,33,35,36,52,56,62,74,100}, then minimally rounded each sorted coordinate upward: q=max(original,previous_rounded+1), followed by adding1 exactly when q has the wrong rank parity. There were255 base provenances,223 distinct rounded base tails; eight added named/interval provenances brought the totals to263 records and229 distinct tails. Final cardinality counts were75,108,35,11. All coordinate steps, subset indices, originals, controls and duplicate provenance are retained in root_alternating_gap_seeds.json. Max label101; primary E supports have at most10 labels. The ordered-tail compact-JSON SHA256 is fe564c2ce3730d78f8efef5b7219e28e606abaf5dd47e177df420821433e4c91, matching an independent arithmetic enumeration.

The witness is case212 in the prescribed order (maxT,cardT,sumT,T lexicographic), from original subset {18,35,36,52,56,62,100}, base indices {0,2,3,4,5,6,8}. Its rounded image is {19,36,37,52,57,62,101}. Exactly212 primary cases completed:140 WIN,71 DRAW,1 LOSS. The run stopped immediately at that first loss;17 cases were intentionally unprocessed and are retained explicitly in root_alternating_gap_unprocessed_seeds.json/.txt. This is the first loss in this fixed ordering only; no global minimality claim is made. No time/resource cap was reached and no additional support was searched.

All eight named/interval provenance controls (six distinct supports) were literally checked at the root and at every first pick. Their values were all DRAW. Safe sets, with all other picks LOSS, are:

| Control T | Safe first picks |
|---|---|
| {9,10,13,16}, both rounded-old and literal records | {4,10} |
| {9,16,17,18,27,28,31,38}, both rounded-old and literal records | {7,9,16,17} |
| [9,11] | {4} |
| [9,12] | {7} |
| [9,15] | {4,9,10,11,13,14} |
| [9,16] | {4,7,10,11,12} |

The supplied old8 safe set {7,9,17} was incomplete:16 also draws. The source logs and JSON retain the supplied set and its failed completeness comparison; the literal map determines the corrected set.

Literal replay completed13 root records and112 corresponding first-pick records: one witness with9 picks, eight control provenance records with62 picks, and four optional witness contexts with41 picks. Duplicate named/literal controls remain separate records as requested. The independent implementation was unchanged verify.absolute with literal scores (0,d); after a pick x<d it evaluates the same player at (x,d), and after x>=d it negates the opponent value at (d,x). Thus continuing same-player picks remain included. All root and move values matched unchanged ExactSlots, whose actual labels were retained. These are exact computations for the encoded finite games, with no kernel certification claimed here.

For gap terminology, alternating tail ranks imply even-length omitted runs within [9,maxT], including the initial run [9,minT). The bridge from reserved anchor7 to odd minT omits an odd number of labels (11 here); full E does not have only even gaps.

Generation took0.046240750s, compile0.685851583s, native probe0.897267584s, literal replay0.392292s externally:2.021651917s total. The native search reported0.00253613s and2113536-byte RSS; compiler peak recorded child RSS144375808 bytes, literal RSS24363008 bytes. All processes stayed below30s/512MiB, and native search below20s. Commands, command hashes, output hashes and resource receipts are in root_alternating_gap_run.json. No interval table, frozen source modification, extra N or subsequent batch was used.

Read-only independent reviews checked the arithmetic encoding before native execution and the completed receipt afterward: all212 ordered rows,17 remaining inputs, direct E1 perspective, first-stop witness, four contexts,13 literal root records and112 first-pick records. Final hash checks preserved frozen slots.hpp/verify.py and every file hashed by the earlier root_interval_four_manifest.json and root_interval_lead4_manifest.json. This round writes only its new root_alternating_gap_ prefix.
