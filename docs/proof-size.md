# Proof size and certificate size

A game solver, a strategy certificate, a formal proof and a Turing machine are different objects. Their sizes need separate accounting.

## A proved bound for full strategy DAGs

[CertificateComplexityHighCounters.initial_certificate_exponential_floor](../CatchUp/Earlier/CertificateComplexityHighCounters.lean) proves that, for N≥16, **any valid full nonloss certificate from the actual initial interval root**, for either specified protected player, has at least

```text
2^floor((N-2)/12)
```

listed nodes. Valid-certificate existence is a hypothesis. The theorem does not assert that both players have nonloss certificates for every N.

This model allows sharing identical states, but only genuinely terminal leaves. A protected-player node supplies a legal witnessing choice; an opponent node covers every legal pick. The proof uses large counters and a covering argument to force many different remaining-state labels. The exact language is defined by [StrategyContract](../CatchUp/Earlier/StrategyContract.lean), [CertificateChecker](../CatchUp/Earlier/CertificateChecker.lean), and [InitialCertificate](../CatchUp/Earlier/CertificateComplexity.lean).

The bound concerns this explicit certificate class. It is not a lower bound on the length of all Lean proofs, on arbitrary algorithms, or on machine-state count. A symbolic theorem can justify a family of states without listing that entire strategy graph.

## A broader certificate language

[CertificateComplexityCompression](../CatchUp/Earlier/CertificateComplexityCompression.lean) supplies a proved target rule: when the protected player acts and their deficit is an available maximum counter, that position is nonlosing. The target requires no table of game outcomes. It certifies a region of states; it is not an instruction always to take the largest counter.

Partial certificates can stop at such a target because its safety has been proved separately. The [literal fixtures](../CatchUp/Earlier/CertificateComplexityFixtures.lean) give these kernel-checked counts:

| N | Protected player | Full DAG nodes | Structural-target nodes |
| --- | --- | ---: | ---: |
| 3 | P1 | 6 | 5 |
| 3 | P2 | 10 | 9 |
| 4 | P1 | 10 | 8 |
| 4 | P2 | 17 | 15 |
| 7 | P1 | 58 | 54 |
| 7 | P2 | 80 | 75 |

These are counts of particular witnesses, not minima or an asymptotic upper bound. The compression theorem and its supporting mathematics must be counted in a complete proof-size comparison. Changing the leaf rules changes the certificate class to which the full-DAG bound applies.

## What to measure

Record the target proposition and definitions; serialized certificate bytes; node counts and leaf rules; proof-source bytes and imported supporting mathematics; checking time and peak memory on identified hardware; and search/generation cost separately. [Earlier benchmarks](../verification/benchmarks.json) and [verification records](../verification/) provide examples.

For a cryptid-based proof, count both the equivalence `Halts(M) ↔ ¬C` and the eventual halting or nonhalting argument. A small interpreter can run an enormous search; a short program is not automatically a short proof.

The useful next question is which proved strategic or arithmetic targets compress the remaining interval families. Failure to find a shorter proof supplies no general lower bound.
