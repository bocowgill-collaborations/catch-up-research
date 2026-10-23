# Glossary and conventions

| Term | Meaning here |
| --- | --- |
| Initial game | Scores zero, counters `{1,…,N}`, and P1's forced single opening pick. |
| Eligible N | `N mod 4` is 0 or 3, equivalently `N(N+1)/2` is even; includes 0. |
| Support / remaining set | The distinct positive counters still available, often written `R` or `S`. |
| `[a,N]` / `Icc a N` | All integers from a through N, inclusive; empty if N<a. |
| Normalized position `(R,d)` | R remains and the player acting now trails the opponent by `d≥0`. |
| `Position.value` | The three-valued optimal outcome measured for the acting player. |
| `CatchUp.value S` | The optimal initial-game outcome measured for P1. |
| WIN / DRAW / LOSS | The outcomes, ordered win > draw > loss. Numerical -1,0,1 in the explorer encode only this ordering. |
| Nonloss / CanAvoidLoss | The specified player has a strategy guaranteeing a win or a draw. |
| Nonwin | The acting player has no strategy forcing a win; the opponent can avoid losing. |
| Draw | Both players can avoid losing. One nonlosing strategy alone is insufficient. |
| Pick | One counter removal. Several picks can belong to one turn. |
| Completed turn | Picks ending at the first catch; their order/preparatory sum must meet the legal-turn conditions. |
| Opening / `afterOpening S x` | P1 takes exactly x, leaving P2 acting on `S.erase x` at deficit x. |
| Paired support | A set arranged in adjacent pairs such as `{a,a+1,b,b+1,…}`. Geometry is a hypothesis, not a guarantee of a draw. |
| Orphan | A counter left without its usual partner after one member of an adjacent pair is taken. |
| Anchor / reserve | A specified retained counter or pair used by a proposed defense; not a special move in the rules. |
| Exact-sum block | A subset whose counter sum equals a specified deficit or target. Its existence alone does not certify a legal or safe turn. |
| Shadow | A related position assumed to have a particular value in a conditional reduction. That value hypothesis must be kept. |
| Dense support / holes | A subset of `[1,N]` with a bounded number of missing counters. Consult each theorem's explicit hole bound. |
| Counterexample | Always specify the claim: an initial-interval win refutes C; a sparse-state example may only refute an auxiliary strategy principle. |
| Cryptid | Here, a specified blank-tape Turing machine whose halting is proved equivalent to the falsity of C. |

The [paper](https://www.nealen.net/papers/catch-up-a-game-in-which-the-lead-alternates-2015.pdf) also discusses repeated counters. This repository's current Lean target and explorer use finite **sets**, so duplicates are not silently merged or accepted as a multiset game. Alternative tie-breaks, multiplayer rules and unequal starting scores are separate variants unless explicitly modeled.
