> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.AlternatingTailObstruction](../../CatchUp/AlternatingTailObstruction.lean).

Frozen witness: T={19,36,37,50,57,60,99}, E={4,7} union T, deficit1 LOSS. Unchanged ExactSlots and independent literal-score replay confirm all nine first picks LOSS. T has min19, odd/even alternating ranks and even sum358; sum(E)+1=370 is even.

All128 deletion subsets of INITIAL T0={19,36,37,52,57,62,101} were accounted before solving. Exactly16 were admissible (10 cardinality3,5 cardinality4,1 cardinality7),112 predicate-skipped. The final approved schedule queried ALL16:9 WIN,6 DRAW,1 LOSS; only T0 lost. Every mask, predicate failure and query outcome is retained in results.json. The seeds JSON records preparation-time status; completed statuses are in results.json.

Coordinate -2 sweeps then compressed T0 without resorting or changing cardinality. All21 attempts are logged:18 legal queries,3 inadmissible skips,3 accepted LOSS trials. Accepted changes were62->60 and101->99 in sweep1, then52->50 in sweep2. Sweep3 accepted none and tried every coordinate from the frozen tail. No cap occurred. This is only a one-step coordinate -2 fixed point. Proper admissible deletions were checked for INITIAL T0; final T deletions were NOT retested. No global or final deletion-minimality claim is made.

Final literal replay covered3 roots and29 first picks. E1 loses at every pick. E3=DRAW with safe picks{4,7}; C8=DRAW with safe picks{2,3,4,7}, C={2,3,4,7} union T. All other context picks lose. verify.absolute used literal scores and retained continuing same-player picks. This refutes generic alternating-tail E1 NONLOSS only; no interval/root or conditional B counterexample follows.

The E1-only cutoff7 certificate has19 nodes,9 seven-counter leaves,18 edges, root19. LOSS retains all legal moves; WIN retains one winning move; child IDs precede parents. Every edge passed independent support/deficit/switch/perspective checks, including5 same-player edges. All9 leaf values passed independent literal replay. The JSON, original NODE/EDGE log, extraction source and leaf/edge checker were handed to density_boundary_proof. No E3/C8 certificate or kernel certification is claimed here.

Commands, command/output hashes and resource receipts are in run.json. Total external cost, including generation, two compiles, compression, literal replay, extraction and certificate check:4.450941791s. Peak recorded child RSS151814144 bytes (compiler); native compression0.000764042s/1769472-byte RSS; final literal replay0.0762875s/22904832-byte RSS. Every process stayed below30s/512MiB, native search below20s.

Independent arithmetic and parent source audits passed. Final hash checks preserve all files hashed by the prior root_alternating_gap, root_interval_four and root_interval_lead4 manifests, including frozen slots.hpp/verify.py. This round writes only its NEW shrink prefix; no table, new seed or further experiment was used.
