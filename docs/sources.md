# Reading and related work

Checked 23 October 2026. This is a curated starting point, not a claim that every publication or implementation has been found. Machine-readable links and source pins are in [sources.json](sources.json).

## Original game and formal target

- **Isaksen, Ismail, Brams and Nealen (2015)**, [*Catch-Up: A Game in Which the Lead Alternates*](https://www.nealen.net/papers/catch-up-a-game-in-which-the-lead-alternates-2015.pdf). Game & Puzzle Design 1(2), 38–49. The starting paper; includes examples, experiments and variants. The [authors' repository](https://github.com/aisaksen/catch-up/tree/41407faa7e60ebeb6be07d32141f24343cd9b9ee) contains a demo and computational notebooks. Its 2016 code check-in is distinct from the paper's 2015 publication.
- **Google DeepMind FormalConjectures**, [the precise target](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjectures/Paper/CatchUpConjecture.lean#L182). The conjecture still has an unfinished proof in this inspected source. [Issue #1324](https://github.com/google-deepmind/formal-conjectures/issues/1324) records its addition; the issue being closed does not mean the mathematical problem was solved. [Issue #4834](https://github.com/google-deepmind/formal-conjectures/issues/4834) discusses the normalized API.

## Earlier mathematical and computational work

**Bernhard von Stengel (2019)**, *Computational progress on the Catch-Up game*. The [LSE seminar abstract, 22 February 2019](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf#page=5) reports optimal-play computations through **N=34**, consistent with the even-total draw conjecture, and states that a winning first move, if one exists, is unique. It also reports a pattern for odd-total games from N=21 onward, with a first-player winning opening at most three. These computational claims have not been independently replayed here. A [King's workshop program, 25 March 2019](https://www.kcl.ac.uk/events/fair-play-in-economics-and-politics), lists a talk with the same title.

This source predates the 2026 solver repositories below and reports a larger range. Their runs must not be described here as the first computations through N=28 or as extending the known range. The [Lean uniqueness theorem](../CatchUp/WinningOpening.lean) formalizes an already reported mathematical fact. A public solver/certificate archive for the LSE report has not been located in this audit; finding it would help with independent reproduction.

## Public solver implementations

| Project | What the source reports | Assurance in this collection |
| --- | --- | --- |
| [t1merickson/catchup-exact](https://github.com/t1merickson/catchup-exact/tree/6785c5e0d81a66002544d81af5307a97faf4e8dd) | Exact outcomes through N=28, including draws at 23,24,27,28; C++ and Python implementations | Source inspected; large runs not reproduced or Lean-certified here. Historical novelty claims are not adopted. |
| [Kuberwastaken/c5-k4](https://github.com/Kuberwastaken/c5-k4/blob/e2cee93231eefb91c41e35450f7eeb19fd9c8c75/results/expansion/live-search-2026-08-14/catchup-n24-parity-packed-development/result.md) | Exact N=23 and N=24 draws; the later parity-packed report supersedes the earlier N=24 timeout bracket | Report/source inspected; not independently replayed or Lean-certified here. Repository-wide recent commits are not dates of new Catch-Up results. |
| [This repository's small explorer](../computation/explore.py) | Outcomes and every legal first pick for a supplied small position | Bounded exact Python calculation, checked against an independent recurrence; not a proof certificate. |

Follow each project's license and reproduction instructions. Links are provided rather than silently vendoring other authors' solvers. A source's own use of “certified” is not automatically a Lean kernel certificate.

## Cryptids and further contributions

[Google DeepMind Cryptids](https://github.com/google-deepmind/cryptids) provides the machine infrastructure reused by this project. The [Catch-Up machine page](../cryptid/) explains the actual theorem, source pins and state counts. The baseline is fully connected to C; the smaller candidate is not yet a verified replacement.

Helpful additions include older source code, talks/slides with mathematical arguments, checked finite strategies and corrections to this reading list. Supply a stable source, identify its rules and claimed result, and say what has actually been checked. Similar names in sports, education or other games do not by themselves identify this counter-removal game.
