# Catch-Up Research

Catch-Up is a two-player game invented by **Aaron Isaksen, Mehmet Ismail,
Steven J. Brams, and Andy Nealen**, and introduced in their 2015 paper
[*Catch-Up: A Game in Which the Lead Alternates*](https://www.nealen.net/papers/catch-up-a-game-in-which-the-lead-alternates-2015.pdf).

This repository is a shared home for research on the game-theoretic and
number-theoretic properties of Catch-Up, including the main
[Catch-Up Conjecture](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean#L182).
It contains proofs, computations, failed approaches, and the
[Catch-Up cryptid](cryptid/).

**Status, 23 October 2026:** the conjecture remains open. Verified work currently
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

[A precise Lean statement in FormalConjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean#L182).

## Find your way

| Section | What you will find |
| --- | --- |
| [Start here](docs/) | Worked play, a glossary, and the number theory behind the question. |
| [Reading and related work](docs/sources.md) | The original paper, earlier results, public solvers, and discussions. |
| [results/](results/) | Readable results and informal arguments, with review status. |
| [CatchUp/](CatchUp/) | Lean definitions, intermediate theorems, and checked certificates. |
| [computation/](computation/) | Solvers, finite results, and reproduction instructions. |
| [cryptid/](cryptid/) | The machine, its equivalence proof, and documentation. |
| [Open questions](results/open-questions.md) | Research goals and ways to contribute. |
| [Research notebook](archive/research-notes/) | Existing findings, failed ideas, bounded experiments and how the approaches developed. |

## Proofs and intermediate results

The existing proofs, checked by the Lean proof assistant, establish:

- **Correct evaluation:** an executable evaluator agrees with the reference rules.
- **Certificate checking and size:** sound strategy checkers, a size bound for
  explicit full certificates, and examples of structural compression.
- **Structural defenses:** a player can avoid losing in certain families of
  partially played positions. Other results rule out specific winning choices.
- **Failed strategy principles:** certified counterexamples refute several
  proposed general strategy rules on other counter sets. They do not refute
  the conjecture about `{1,…,N}`.

Results label their evidence and review status. Lean proofs include checking
instructions; informal arguments and heuristic observations are identified separately.

## Computational evidence

A [2019 LSE report](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf#page=5) describes computations through **N = 34**, consistent with the conjecture.
Later public implementations include [catchup-exact](https://github.com/t1merickson/catchup-exact)
and [c5-k4](https://github.com/Kuberwastaken/c5-k4). Their large runs await independent
audit here. See [the evidence table](computation/) for sources, dates and assurance.
Finite cases do not settle the universal conjecture.

Try a small exact position without installing Lean:

```sh
python3 computation/explore.py --initial 4
```

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

The [full problem guide](results/open-questions.md) also covers odd-total games,
nonconsecutive supports, number-theoretic structure, complexity, and variants.

Contributions can include proofs, computations, failed approaches, or explanations.
State the claim, identify the rules and evidence, explain how to check it, and
credit earlier work.

Catch-Up was introduced by **Isaksen, Ismail, Brams, and Nealen (2015)**. See the
[authors' original code](https://github.com/aisaksen/catch-up) and the
[reference Lean formalization](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/CatchUpConjecture.lean).
See [credits and AI assistance](CREDITS.md) and [verification instructions](verification/).

## Citing this repository

If this repository helps your research, please cite it:

```bibtex
@misc{cowgill2026catchup,
  author       = {Cowgill, Bo},
  title        = {{Catch-Up Research Repository}},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/bocowgill-collaborations/catch-up-research}
}
```

For reproducibility, identify the release or commit used. Please also cite the
original papers and upstream projects relevant to the results you use.

**Contributor credit:** As others contribute research, proofs, code, computations,
failed examples or documentation, we will update this citation to include them as
co-authors, with their agreement. Individual contributions and their sources will
also be credited throughout the repository.
