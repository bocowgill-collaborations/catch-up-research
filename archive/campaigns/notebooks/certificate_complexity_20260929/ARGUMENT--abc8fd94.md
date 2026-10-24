> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Candidate complete argument — target-set covering

This note is an argument for review, not a claim that Catch-Up is solved. The
certificate existence premise is indispensable. The exponent below is of order
sqrt(N), not N. The arithmetic counting lemma is being formalized separately.

## Full model

Use `CertificateChecker.DAGValid`, with gameSize N, protected player p, and root
decoding to `(I_N,0,p1)`. At deficit zero every legal positive pick switches player,
so this root faithfully includes the mandatory one-pick opening. Count every listed
node (including the root and terminal leaves). Nodes are distinct full encoded
states; sharing identical states is allowed, but symmetry quotients and nonterminal
macro leaves are not. Unreachable nodes may be pruned and never improve a minimum.
Let D_p(N) be the minimum only on the domain where such a certificate exists.
The two players' minima are added, without sharing across their certificates.

## Calibration

There are k labeled pairs `(i,0),(i,1)`. At an adversary synchronization state all
remaining pairs are intact. The adversary picks any remaining member. The defender
must pick a remaining member; a non-mate pick immediately loses for the defender.
A mate pick deletes the pair and returns to an adversary synchronization state.
The state with no remaining pairs is a terminal defender win. The objective is to finish without
ever making a non-mate response. Thus every nonlosing certificate must choose the
mate, and cover both members of every remaining pair on adversary turns.

For each subset T of labels, the adversary can delete exactly its complement in
any order. Therefore all 2^k synchronization states occur in every full explicit
certificate. Conversely, the family of all subsets is deletion closed and realizes
exactly 2^k synchronization states. This lower bound is for every nonlosing policy,
not just a chosen implementation of the mate policy: the rules force that policy.
Correctness for every k is a short induction on the number of intact pairs.
The Lean deletion-closure lemma is the combinatorial core; the game-to-closure
identification is the explicit rule analysis above, not a general formal game engine.

## Catch-Up lower bound

**Claim.** Let N >= 16 and choose an integer h >= 1 with
`N <= h(h+1)/2`. Put `M=h+1` and `t=floor((N-1)/(2M))`.
Every full nonloss certificate for either protected player has at least `2^t`
nodes. More generally the same proof works whenever `2Mt <= N-1`.
This bound does not depend on parity and asserts nothing about existence.

### 1. Bounded deficit and a long nonterminal zone

Every reachable state has counters in I_N and deficit at most N: start at zero;
each pick x replaces d by |d-x|, and both x and d are at most N.

Any reachable state retaining at least floor(N/2) distinct positive counters is nonterminal:
their sum is at least `r(r+1)/2 > N` for r=floor(N/2), N>=16. Its remaining set
is nonempty, and its sum is greater than its deficit. This handles early termination,
not just empty-set termination.

### 2. Any uninterrupted protected turn uses at most h picks

If the turn begins with positive deficit d <= N, each proper prefix before the
first catch has sum strictly below d. Equality catches and switches players.
If h distinct positive counters had been picked without catching, their sum would
be at least h(h+1)/2 >= N >= d, a contradiction. Thus, provided the short path has
not already terminated, the turn switches by pick h. At zero deficit the first
pick switches, so the same h>=1 bound holds. No optimality or score-margin
assumption is used here.

### 3. Interval-root entry

For a p2 certificate the initial node itself is adversarial; take S0=I_N.
For a p1 certificate, its first prescribed pick a is legal and switches to p2.
The checker covers this child. Take S0=I_N\{a}; this is an adversary node, and
|S0|=N-1. The entry child is nonterminal by the previous zone bound.

Write r0=|S0|, so r0>=N-1. All further remaining sets are subsets of S0.

### 4. Deleting a chosen target T, despite adaptive responses

Fix any t-element subset T of S0. At each adversary synchronization state, if a
target counter remains, pick one such x (e.g. the least). This is a legal move and
is covered by the certificate. If x is below the current deficit, it is still the
adversary's turn; this macro removes one counter. If x catches, follow the
certificate's chosen protected moves until the adversary moves again; this removes
at most 1+h=M counters. These are actual atomic picks, not certificate macro leaves.

Each macro removes at least one previously present target. Protected picks may
also remove targets; that helps. Thus at most t macros suffice. At every prefix
of these macros at most Mt counters have disappeared from S0. Since
`Mt <= (N-1)/2`, at least floor(N/2) counters remain. Therefore no early terminal
can interrupt the construction, including inside the final protected turn. The
turn-length argument ensures that it really reaches the next adversary node.

This construction uses the certificate's actual choices, which can depend on its
state and hence be fully adaptive. The adversary only observes current state;
no future-choice inspection is needed. Stop at the resulting adversary state,
where all of T has disappeared. If t=0, simply use the entry state.

### 5. Count sets rather than histories

Let C be the family of deleted subsets `A=S0\S` at adversary states of this
certificate with |A|<=a:=Mt (one can include all such listed states). Every
t-subset T of S0 is contained in some A in C by step 4. Each A covers at most
binom(a,t) such targets, so

`binom(r0,t) <= |C| binom(a,t) <= (# DAG nodes) binom(a,t)`.

This inequality explicitly permits multiple target choices and arbitrarily many
histories to merge at the same state. Different deficits or player identities with
the same remaining set only increase the node count; projecting to deleted sets
cannot increase it.

Since r0>=2a, each falling-factorial factor `r0-i` is at least `2(a-i)` for
0<=i<t. Hence `binom(r0,t) >= 2^t binom(a,t)`. Finally a=Mt>=t, so the common
binomial factor is positive and can be cancelled. The result is `#nodes>=2^t`.

Choosing h=ceil(sqrt(2N)) gives t=Theta(sqrt(N)), hence the conditional bound
`D_p(N) >= 2^{Omega(sqrt(N))}`. This is weaker than the proposed `2^{cN}` bound.

## What is and is not established by this mechanism

The deletion-cover argument is a single mechanism; it does not rely on permanently
encoding independent bits. It proves many distinct remaining sets after accounting
for the bounded number of targets one state can cover. It is not an outcome lookup.
The proof does not establish any nonloss strategy, the conjecture, a linear-in-N
exponent, or a mathematical proof-length lower bound.

Conditional on existence, trimming a full certificate to root-reachable nodes also
gives the elementary upper bound `D_p(N)<=2(N+1)2^N`: there are 2^N remaining sets,
N+1 reachable deficit values, and two actual movers. Both certificates are counted
separately. Existing extracted counts are only upper bounds on their corresponding
minima, and only when they start at the same root and use the full checker language.
