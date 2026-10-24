> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent review: high-counter strengthening

## Verdict

**PASS.** The mathematical strengthening in `HIGH_COUNTER_ARGUMENT.md` is correct
for the specified full atomic certificate language. In particular, for `N >= 16`
and natural `t` with `12t+2 <= N`, every `InitialCertificate N player dag` satisfies

\[
2^t\le \operatorname{length}(\texttt{dag.nodes}).
\]

This establishes the conditional exponential-in-`N` explicit-DAG lower bound,
not merely the earlier exponential-in-`sqrt(N)` bound. I found no mathematical
gap, incorrect constant, or counterexample in the strengthening.

Reviewed independently on 2026-09-29. The reviewed argument's SHA-256 was
`d982ec7684fe69bd28c8a477271fbb75009033c573477e79e7a50e15663f621b`.
No helper agents, outcome computations, solver runs, or tables were used. This is
an audit of the mathematical argument and its agreement with the actual game and
checker, not a compilation or axiom-audit certificate for concurrently written
Lean code.

## Exact scope

The underlying definitions are the ones audited in `REVIEW.md`:
`CatchUpSearch.StrategyDAG`, `CertificateChecker.DAGValid`, and the actual
`GamePosition` transition, terminal condition, and fixed-player semantics.
The graph starts at the decoded interval root `(I_N,0,p1)`. Its owner nodes choose
one legal atomic pick; its opponent nodes cover every legal atomic pick; all
leaves are actual terminal positions. Nodes are counted as listed full states,
including the actual mover, with no symmetry quotient or nonterminal macro leaf.

The prior review's wording correction about the toy empty state has now also
been made. Its calibration and interpretation remain valid. The present argument
strengthens the earlier Catch-Up bound using the same target-cover mechanism.

## Detailed verification

### 1. Large-counter geometry and root entry

Let

\[
L=\{\lfloor N/2\rfloor+1,\ldots,N\}.
\]

Then `|L|=ceil(N/2)`. Each `x in L` satisfies `2x>N`; hence any two distinct
members `x,z` satisfy `x+z>N`.

Every constructed reachable position has remaining counters in `I_N` and deficit
at most `N`: a legal transition changes `d` to `|d-x|`, which is at most `N` when
both inputs are at most `N`. Thus any such position retaining two members of `L`
is nonempty and has remaining sum greater than `N`, and therefore greater than
its deficit. It satisfies neither terminal condition. This assertion uses the
reachable-deficit bound; it is not asserted for arbitrary unrelated listed states.

For protection of `p2`, the initial `p1` root is already an opponent node.
For protection of `p1`, follow the certificate's prescribed opening. It removes
one positive counter and switches to `p2`, exactly as the mandatory opening rule
requires. This loses at most one member of `L`.

Let `S0` be the members of `L` present at that opponent entry node. Then

\[
r_0=|S_0|\ge \lceil N/2\rceil-1\ge 6t,
\]

because `12t+2<=N`. Also `r0>=7` follows from `N>=16`. Both entry cases are
therefore nonterminal, with the correct actual mover. All subsequent surviving
large counters lie in `S0`; removed counters never reappear.

### 2. An owner turn deletes at most two large counters

Consider a turn starting at positive deficit `d<=N`. Every prefix before the catching pick
has total strictly less than `d`. If two members of `L` belonged to that prefix,
its total would exceed `N>=d`, a contradiction. The preparation prefix therefore
contains at most one large counter. The final catching pick can contribute at
most one more.

At deficit zero the very first pick ends the turn. At a positive deficit, equality
also ends it: the actual transition continues the mover only when `x<deficit`.
There is no equality case allowing a third large counter in the same turn.

This proof bounds the number of large picks, not the number of all picks. An
arbitrarily long finite sequence of small picks is permitted and does not weaken
the conclusion. Moreover, every still-uninterrupted noncatching prefix has at
most one large pick, so the same reasoning controls partial turns without assuming
in advance that the turn has ended.

### 3. Why small picks cannot prevent completion

Here is a direct justification of completed-turn existence, independent of the
large-counter count. If a nonterminal position has remaining sum `s` and deficit
`d`, then `s>=d` and its remaining set is nonempty. After a legal noncatching pick
`x<d`, the new sum and deficit are `s-x` and `d-x`. They satisfy
`s-x>=d-x`. The new remaining set cannot be empty: otherwise `s=x<d`, contradicting
the original nonterminal condition. Thus a noncatching pick preserves
nonterminality.

At a nonterminal owner position, checker validity supplies the prescribed legal
pick and a covered child. If that pick does not catch, repeat at the child.
Every such transition strictly reduces remaining cardinality. An infinite
noncatching owner sequence is therefore impossible, and a finite such sequence
cannot end without a prescribed move while still nonterminal. A catching pick
must occur and its covered endpoint switches to the adversary.

This is exactly the reasoning implemented by the inspected
`owner_completed_turn` in `CertificateComplexityGame.lean`. Its applicability
requires a nonterminal owner entry; the next step supplies that hypothesis.

### 4. Target macros and all prefix states

Fix one `t`-subset `T` of `S0`, while keeping the entire certificate and its owner
policy fixed. After `j<t` macros, at most `3j` large counters have been deleted.
If a target remains, the adversary selects a currently present target. The
certificate covers this legal pick. It deletes exactly one more large counter.

If this pick is below the current deficit, the adversary still moves; this is
already a completed macro of large-counter cost one. If it catches, the owner
starts a turn. Just after the adversary pick, at most `3j+1` large counters have
been deleted. In particular, the owner entry still retains at least two members
of `L`, so is nonterminal. By the preceding completed-turn argument its prescribed
choices reach the next switch, deleting at most two further large counters.

At every prefix within that owner turn, at most two additional large counters
have been deleted. Hence, throughout this macro,

\[
\#\{\text{deleted members of }S_0\}\le 3j+1+2\le3t.
\]

It follows from `6t<=r0` that the number of large counters still present is at
least

\[
r_0-3t\ge\lceil r_0/2\rceil\ge4.
\]

Thus every actual prefix, including the final catching child, is nonterminal.
There is no circular dependence on eventual macro completion: the owner entry
is nonterminal before invoking completed-turn existence; noncatching steps then
preserve nonterminality directly; and the large-counter bound rules out a terminal
catching endpoint. Equivalently, the prefix large-counter invariant proves
nonterminality throughout by itself.

Each macro deletes the chosen target, which was present at its start. Owner
picks may additionally delete targets. Therefore no more than `t` macros are
needed. If the last target disappears during an owner turn, the remaining
prescribed picks through the catch are still within the same two-large-counter
budget. The process ends at a covered opponent node with every target gone and
at most `3t` members of `S0` gone. For `t=0`, take the entry node and make no moves.

The adversary is allowed to use a different sequence for each fixed target set.
The owner's choices do not change between these constructions; they are always
the choices stored in the same arbitrary certificate. Only current availability
is needed to choose the next target. Adaptivity, continued adversary turns, and
targets consumed by owner responses are all included.

### 5. Projection and cover-count arithmetic

Project relevant listed nodes to `A=S0\remaining`, retaining only projections
with `|A|<=3t`. Let `C` be the resulting family of distinct subsets. Its size
cannot exceed the number of listed nodes. The previous construction gives, for
every `t`-subset `T` of `S0`, some `A in C` with `T subset A`.

A projected set covers at most `binom(3t,t)` targets. Consequently

\[
\binom{r_0}{t}\le |C|\binom{3t}{t}
\le \operatorname{length}(\texttt{dag.nodes})\binom{3t}{t}.
\]

No injection from targets or histories into nodes is asserted. Several targets
may produce the same node; arbitrarily many histories may merge. Their possible
contribution is precisely what the covering-capacity factor bounds. Small-counter
differences or different deficits can only create more full nodes mapping to the
same deleted-large-counter set, and cannot invalidate the lower bound.

For `0<=i<t`, the inequality `r0>=6t` yields

\[
r_0-i\ge6t-i\ge2(3t-i).
\]

Multiplication and cancellation of `t!` give
`binom(r0,t)>=2^t binom(3t,t)`. The factor `binom(3t,t)` is positive, including
when `t=0`. Cancelling it proves `2^t <= length(dag.nodes)`.

### 6. Exponent and constants

For `N>=16`, the natural number `t=floor((N-2)/12)` satisfies `12t+2<=N`, so the
displayed minimum-size consequence is valid wherever that minimum is defined.
For `N>=28`,

\[
\left\lfloor\frac{N-2}{12}\right\rfloor
\ge\frac{N-2}{12}-1
=\frac{N-14}{12}
\ge\frac N{24}.
\]

Thus `c=1/24` and `N0=28` are valid stated constants. No parity condition was used;
restricting to admissible even-total sizes preserves the result.

## Interpretation and verification gates

The result is conditional on existence of the relevant full nonloss certificate.
It does not establish a nonloss strategy, either player's certificate existence,
or the Catch-Up conjecture. It is a lower bound for explicit atomic state-DAG
representation size. It does not lower-bound mathematical proof length, symbolic
strategy-description size, or certificates in a richer language with proved macro
rules. If both players' minima are added, both existence hypotheses are needed and
their nodes remain separately counted.

All four mathematical review gates are met: faithful root/checker semantics;
large-counter and finite-progress control of every prefix; quantifier-correct
state projection allowing arbitrary collisions; and valid constants with honest
representation/existence/proof-length distinctions. No mathematical gate is
abandoned. Lean compilation and the transitive axiom audit remain separate author
verification tasks.
