# Where the existing research leads

The conjecture remains open. This is a map of what the collected work makes possible, what it rules out, and the exact obligations still missing. Detailed arguments and earlier experiments are in the optional [research notebook](../archive/research-notes/README.md); its historical “next steps” are superseded by this page where they conflict.

The earlier [August–September ledger](legacy-findings.md) preserves alternative lower-ray, shifted-tail and simulation routes. The August four-obligation normal form (CU-L007–CU-L008) is a reported scratch result whose proof file is unrecovered. The antepenultimate and fourth-endpoint proofs (CU-L021, CU-L032) remain archived sources with historical checks. The [fifth endpoint](fifth-endpoint.md), CU-L037, now has a separately checked symbolic port for every N≥23, with no parity or smaller-instance premise. It closes only that endpoint, not the entire lower ray. The finite two-buffer controller (CU-L026) remains a causal test instance, while its uniform adjacent-hole translator is open.

## Pair deletion and complete defensive turns

The [conditional maximum-reply companion](reply-maximum-companion.md), CU-R001,
is now a checked building block related to CU-L011. Under the explicit nonempty
and catchability hypotheses for every smaller pair-deletion position, a winning
reply from a maximum forces a distinct companion reply and two winning
cross-picks. Establish those hypotheses before using it; it is not an
unconditional outdegree theorem or a shifted deficit-one result.

The [opening guide](../docs/openings.md) connects drawn openings to two-pick continuations. The weaker [lower-ray criterion](../CatchUp/PairDeletion.lean) needs nonloss after deleting counters 1 and b, together with a drawn first-pair position. Increasing-turn normalization and small paired defenses provide proved ingredients, but do not establish those requirements for every eligible N.

The proposed first-pair family is `([3,N],1)` for eligible N>=7, with separate small bases. At N=3 that position is winning, so a statement covering every eligible N without a small-case qualification is false even though the N=3 root draws.

The [paired-strategy notes](../archive/research-notes/README.md#paired-strategies) record a useful progression: five-pair proofs, a failed seven-pair recursion, a whole-turn score-sum defense, a repaired three-core-pair triangle, a failed four-pair orphan invariant, and an adaptive repair of the particular reached obstruction. The last repair is proved for every even q>=42. It is not a uniform strategy for every larger paired support. Do not restart the unchanged mate recursion or infer induction from its first successful response round.

**Useful next obligation:** a condition on the remaining counters and deficits that the selected friendly moves preserve against every opponent reply, including consecutive picks. It must account for the known singleton/orphan failures. The condition cannot simply mean “this position is nonlosing.”

## Dense states, subset sums and the actual interval core

[IncompleteSubsumMass](../CatchUp/IncompleteSubsumMass.lean) constrains missing subset sums. [AlternativeSumDefense](../CatchUp/AlternativeSumDefense.lean) turns an alternative exact-sum block into nonloss under a precise near-maximum bound. The [dense-loss frontier](../CatchUp/DenseLossFrontier.lean) closes terminal branches and restricts remaining obstructions; it does not prove recursive preservation of density or safety.

One concrete remaining route uses:

```text
C_N = {2,3,4,7} union [9,N]
E_N = {4,7} union [9,N]
A_N = {3,4} union [9,N].
```

The compiled [eight-shadow criterion](../CatchUp/RootUpperEightCriterion.lean), for N>=11 and **assuming V(C_N,8)=LOSS**, equates nonwinning of its reserve-five endpoint with nonloss of `(E_N,1)`. Retaining that hypothesis is essential: sparse counterexamples to unconditional E nonloss have a winning high shadow and do not refute this conditional route.

For `(A_N,1)`, the [boundary theorem](../CatchUp/ConsecutiveGuardBoundary.lean) proves that a winning pick q>=14 must satisfy q+6<=N. The original q is removed in the residual support. A larger residual witness is not automatically a winning pick on the original support, so the numerical increase is not yet an infinite-descent proof.

**Useful next obligation:** handle the interior reentry/equality case with its actual losing-shadow hypotheses and consecutive-tail deletion geometry. [EqualityReserveObstruction](../CatchUp/EqualityReserveObstruction.lean) rules out every first repair turn containing the specified reserve under its hypotheses. A successful first repair must avoid that reserve or explain a different strategic route. Static parity, pair counts and an attainable quota do not supply preservation.

## Use computation to discriminate between claims

The [experimental findings](experimental-findings.md) retain successful tests, counterexamples and vacuous tests separately. Useful questions include whether a proposed response is legal until the first catch, whether every opponent continuation is covered, and which friendly alternatives survive. A failed fixed policy can coexist with a drawn position.

The [raw observations](../computation/observations/README.md) are retained output, not proof certificates. Historical finite-arity SMT UNSAT results are evidence for their unverified bounded encoding; UNKNOWN is not a result. Several tempting universal guard principles have since been kernel-refuted. More positive samples cannot restore those exact claims.

## Proof compression and the cryptid

The [certificate-size theorem](../docs/proof-size.md) bounds one full terminal-leaf DAG language. Structural target leaves permit a different language. A compact uniform strategy lemma could improve both explanation and checking cost; an exponential bound for that DAG language is not a bound for all Lean proofs.

The [complete cryptid](../cryptid/) already proves blank-tape halting equivalent to a counterexample to C. The smaller candidate still needs inherited-core preservation under redirected hooks, a full partial-program simulation and the final equivalence. Historical [machine-design notes](../archive/research-notes/README.md#machine-design) explain successful representation changes and failed proof-reduction routes. Component state counts are not complete Catch-Up machine counts.

These are separate ways to contribute. The main mathematical bottleneck remains a uniform adversarial strategy or a certified initial-interval counterexample, rather than another outcome table or an isolated machine component.
