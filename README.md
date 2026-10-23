# Catch-Up Research

A shared home for Catch-Up research: proofs, computations, failed approaches,
and the Catch-Up cryptid.

**Status, 22 October 2026:** the conjecture remains open. Verified work currently
covers intermediate results and the machine construction.

## The game and the conjecture

For a precise Lean statement, see the [formal conjecture in Google DeepMind's FormalConjectures repository](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean#L182).

Two players start with zero scores and counters **1, 2, …, N**. Taking a counter
adds its number to your score and removes it.

1. The first player takes **exactly one counter** on the opening turn.
2. On every later turn, the acting player takes at least one counter and keeps
   taking while their score is below the opponent's. Reaching or exceeding the
   opponent's score ends the turn; equality counts as catching up.
3. If catching up is impossible, the acting player receives all remaining counters
   and the game ends. When all counters are gone, the higher score wins; equal
   scores draw.

One drawn play with `{1,2,3}`: the first player takes 3, then the second takes 1
and 2. Both finish with 3 points.

**The conjecture:** whenever the total `1 + 2 + … + N` is even, optimal play results
in a draw. Optimal play means preferring a win to a draw, and a draw to a loss.
The statement also includes the trivial empty game, `N = 0`.

## Find your way

| Section | What you will find |
| --- | --- |
| [results/](results/) | Readable results and informal arguments, with review status. |
| [CatchUp/](CatchUp/) | Lean definitions, intermediate theorems, and checked certificates. |
| [computation/](computation/) | Solvers, finite results, and reproduction instructions. |
| [cryptid/](cryptid/) | The machine, its equivalence proof, and documentation. |
| [Open questions](#open-questions-and-contributions) | Research goals and ways to contribute. |

## Proofs and intermediate results

The existing proofs, checked by the Lean proof assistant, establish:

- **Correct evaluation:** an executable evaluator agrees with the reference rules.
- **Structural defenses:** a player can avoid losing in certain families of
  partially played positions. Other results rule out specific winning choices.
- **Failed strategy principles:** certified counterexamples refute several
  proposed general strategy rules on other counter sets. They do not refute
  the conjecture about `{1,…,N}`.

Results label their evidence and review status. Lean proofs include checking
instructions; informal arguments and heuristic observations are identified separately.

## Computational evidence

[catchup-exact](https://github.com/t1merickson/catchup-exact) reports exact draws for
`N = 23, 24, 27, 28`.
[c5-k4](https://github.com/Kuberwastaken/c5-k4/blob/main/README.md) also reports
Catch-Up computations for `N = 23, 24`. These reports await independent audit here.
Entries distinguish reported, reproduced, and Lean-certified results. Finite cases
do not settle the universal conjecture.

## The Catch-Up cryptid

A cryptid is a Turing machine connected to an unresolved problem. Our verified
binary machine satisfies:

**The machine halts from a blank tape if and only if the Catch-Up conjecture is false.**

The best fully verified project construction has **388,819,712 states**, including
initialization. A smaller **211,100,482-state candidate** has checked component
contracts, but its full halting-equivalence proof remains unfinished.

It uses [Google DeepMind's Cryptids infrastructure](https://github.com/google-deepmind/cryptids).
Whether the machine halts remains open. Machine size and proof size are tracked
separately.

## Open questions and contributions

- Can we prove the conjecture or certify a counterexample?
- Can the local defenses be extended to cover every opponent response for all
  relevant initial games?
- Can proofs and certificates be compact and practical to check?

Contributions can include proofs, computations, failed approaches, or explanations.
State the claim, identify the rules and evidence, explain how to check it, and
credit earlier work.

Catch-Up was introduced by **Isaksen, Ismail, Brams, and Nealen (2015)**. See the
[authors' original code](https://github.com/aisaksen/catch-up) and the
[reference Lean formalization](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean).
See [credits and AI assistance](CREDITS.md) and [verification instructions](verification/).
