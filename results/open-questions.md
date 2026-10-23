# Open questions

This page separates the central conjecture, wider questions about the game, and the specific frontier of the collected proof campaign. Some wider questions are research directions rather than precise conjectures with a proposed answer.

The [current route guide](research-routes.md) gives concrete proof obligations; [experimental findings](experimental-findings.md) explain what the existing tests support and which tests were vacuous. Detailed earlier arguments are retained in the [research notebook](../archive/research-notes/).

## The central problem

**C:** for every N, even `N(N+1)/2` implies a draw on `{1,…,N}` under optimal play. This includes N=0. C remains open in the inspected [formal statement](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjectures/Paper/CatchUpConjecture.lean#L182).

An equal partition or a drawn play is insufficient. A proof must supply the needed adversarial guarantees for all eligible N. A counterexample needs an exact forced winner and a checked connection to these rules. One nonlosing strategy does not certify a draw.

## Wider game-theoretic and number-theoretic questions

| Question | What is established here / useful next evidence |
| --- | --- |
| When does every opening draw, rather than just the root? | The existing [all-opening/pair-neutrality equivalence](../CatchUp/Earlier/ReplyDigraphReduction.lean) reduces this stronger property to every two-pick continuation. Small roots can draw while some openings lose. The [opening guide](../docs/openings.md) explains the distinction and the remaining uniform obligation. |
| Which player wins odd-total interval games, and with which opening? | Small calculations show both P1 and P2 wins. The [2019 report](../docs/sources.md) describes P1 wins with opening at most three from N=21 through its tested range; extending that to all relevant N would require a proof. |
| Which nonconsecutive supports draw or have a forced winner? | The library has exact small classifications and sparse obstructions. Parity and pair geometry alone are insufficient. Formulate a family with precise hypotheses. |
| Can subset-sum structure give a uniform defensive rule? | [IncompleteSubsumMass](../CatchUp/IncompleteSubsumMass.lean) and [AlternativeSumDefense](../CatchUp/AlternativeSumDefense.lean) are useful positive results. The challenge is preserving a strategic condition after every legal opponent turn. |
| Which safe strategies have short descriptions and small certificates? | Existing proofs share subpositions and use structural lemmas. The recovered [full-DAG lower bound and structural compression examples](../docs/proof-size.md) already distinguish two certificate languages. Proof-source size, certificate serialization and total supporting mathematics must all be counted. |
| What exact algorithms, state bounds or complexity lower bounds can be proved? | Reachable-state bounds and finite exact solvers are available. Specify input encoding and whether counting picks, turns or merged states. A large raw game tree is not a lower bound on algorithmic work or formal proof size. |
| What happens with repeated counters, unequal initial scores, different tie-breaks or more players? | These are related variants, also raised by the original paper. The current Finset library and C do not automatically cover them. Give a separate semantics and target. |
| Which practical heuristics work across supports or against adversarial opponents? | The original paper studies heuristic play. Measured win rates against chosen opponents are distinct from a guarantee under optimal play. |

For sources and attribution, see the [reading guide](../docs/sources.md). No “largest known checked N” or “first computation” claim is made by this collection.

## Current structural proof frontier

The collected campaign uses [PairDeletion](../CatchUp/PairDeletion.lean) and [RootUpperEightCriterion](../CatchUp/RootUpperEightCriterion.lean). One remaining interval core is `{4,7} ∪ [9,N]` at deficit one, **under the original losing-shadow hypothesis**. Another branch involves `{3,4} ∪ [9,N]` at deficit one. The [top-six exclusion](../CatchUp/ConsecutiveGuardBoundary.lean) leaves other picks unresolved; its residual support differs from the original support, so the bound alone does not give infinite descent.

The highest-value mathematical next step for this route is a defensive condition surviving every legal opponent turn on those cores. Exact-sum blocks are promising ingredients, but a subset sum alone supplies neither a legal first-catch turn nor preservation of nonloss. Keep the parent and shadow hypotheses. The [failed-idea guide](failed-ideas.md) identifies specific shortcuts already refuted.

## Cryptid and verification frontier

The 388,819,712-state baseline has `Halts(M) ↔ ¬C`. The 211,100,482-state candidate has checked local routines and all 277 added bank-site relocations, but still needs inherited-core preservation under hook redirection, full partial-program simulation and final equivalence. See [the machine page](../cryptid/).

Another useful task is to locate the older solver and retained outputs, audit its semantics and reproduce small cases before considering a full large-instance replay. Large reruns are optional, separately budgeted work; existing structural arguments may be more useful for a general proof. Connecting output to a sound certificate checker is a distinct obligation. A least-counterexample claim would additionally require certification of all smaller eligible cases. A smaller machine, by itself, proves neither C nor a short proof-size bound.
