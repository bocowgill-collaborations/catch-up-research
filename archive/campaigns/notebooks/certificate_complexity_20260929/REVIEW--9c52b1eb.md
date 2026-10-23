> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent review: explicit certificate complexity

## Verdict

**PASS WITH CAVEATS.** The conditional Catch-Up lower bound is correct as a
mathematical argument for the stated full, atomic `CertificateChecker.DAGValid`
representation. The paired-game synchronization-state calibration is also correct.
I found no blocking mathematical gap or counterexample. Two wording clarifications
and a formal-verification scope limitation are recorded below.

Reviewed on 2026-09-29, independently of the author, with no helper agents, solver
runs, or new outcome tables. Only this review file was written. The reviewed
`ARGUMENT.md` had SHA-256
`8ee65dbe330cb9138800076a96c07b9644230e5f8c888b986f1aa1a987f9b3f9`.
The subsequent revision with SHA-256
`e411d12bed5d4cbb9636209c9c25010b8a5acc9c3bce5980444cec49656c29dc`
was also checked; it resolves finding 1 by adding “reachable.”

The exact reviewed assertion is: for natural numbers `N >= 16`, `h >= 1`,
`N <= h(h+1)/2`, `M=h+1`, and any natural `t` satisfying `2Mt <= N-1`, every
valid full certificate with `gameSize=N` and decoded root `(I_N,0,p1)` has at
least `2^t` listed nodes, for either protected player. The displayed floor choice
of `t` satisfies this hypothesis.

## Findings and limitations

1. **Minor, resolved: qualify the nonterminal-zone statement.** In Step 1, “Any state
   retaining at least floor(N/2) distinct positive counters is nonterminal” needs
   “any reachable state,” or the explicit hypothesis `deficit <= N`. For example,
   with `N=16`, remaining counters `{1,...,8}`, and deficit `37`, the remaining
   sum is `36`, so the state is terminal. This is not a counterexample to the
   theorem: the preceding reachable-state invariant supplies the missing premise
   in every application. Adding the qualifier removes the standalone false reading.

2. **Minor: make the toy terminal convention unambiguous.** Replace “No remaining
   pair is a terminal defender win” with “The state with no remaining pairs is a
   terminal defender win.” The exact `2^k` count concerns synchronization states,
   including that empty state, not all atomic nodes. Intermediate defender-response
   states must also be present in a full atomic certificate. The candidate already
   labels its exact count as a synchronization-state count, which is correct.

3. **Formal-verification scope, not a mathematical objection.** The inspected
   `CertificateComplexity.lean` defines the interval certificate and contains the
   deletion-closure and target-cover counting lemmas. Those lemmas do not by
   themselves formally establish the Catch-Up-to-cover construction. In particular,
   the file inspected did not contain the full theorem from `InitialCertificate`
   to the displayed exponential node bound. The reviewed Catch-Up result is an
   independently checked mathematical proof; it must not be reported as an
   end-to-end Lean theorem on the strength of the combinatorial lemmas alone.
   This review did not run a Lean build or an axiom audit and does not certify them.

## Check against the actual representation

The relevant definitions were read in `StrategyContract.lean`,
`CertificateChecker.lean`, `CertificateSoundness.lean`, and the actual
`GamePosition` definitions in `FormalConjectures/Paper/CatchUpConjecture.lean`.

- A state records the remaining mask, natural deficit, and actual mover. The
  latter cannot be suppressed when fixing the protected player.
- `DAGValid` requires root membership, distinct encoded states, and local validity
  for every listed node.
- A nonterminal owner node supplies a legal pick and covers its exact decoded
  successor. A nonterminal opponent node covers every available counter, including
  non-optimal moves and picks which leave the same player moving.
- A terminal branch is permitted only at an actual `IsTerminal` position and must
  be safe for the protected player. Nonterminal macro leaves are not permitted.
- Coverage is stated using decoded positions. This is sufficient for the proof:
  every constructed successor has a listed representative to which local validity
  applies. Valid bounded masks are also injectively decoded, so encoded-state
  uniqueness does not conceal several prescribed moves for one game position.
- `afterPick` erases the chosen counter. It keeps the mover precisely when
  `x < deficit`; equality switches. The new deficit is the natural absolute
  difference. `IsTerminal` means an empty remaining set or remaining sum strictly
  below the deficit.

These are the conditions used by the argument. No optimal-play assumption or
unproved outcome classification is imported.

## Constructive audit of the lower bound

### Root entry and reachable invariants

Every legal pick from the interval root is positive. At deficit zero it therefore
switches to `p2`, leaves deficit equal to the picked counter, and agrees exactly
with `GamePosition.afterOpening`. This validates use of the normalized root for
the mandatory one-pick opening.

For a `p2` certificate, the root itself is an opponent node with `S0=I_N`.
For a `p1` certificate, the root is an owner node; its prescribed opening `a`
is covered and leads to an opponent node with `S0=I_N\{a}`. Thus
`r0=|S0| >= N-1` in both cases. The entry node is nonterminal.

Along every path used in the proof, the remaining set is a subset of `I_N`, all
picked counters are distinct, and `0 <= d <= N`: the transition sends `d` to
`|d-x| <= max(d,x) <= N`. These bounds are asserted only for the constructed
reachable states, not arbitrary unrelated nodes listed in the certificate.

Let `r=floor(N/2)`. Then `r>=8` and `N<=2r+1`. The difference

\[
\frac{r(r+1)}2-(2r+1)=\frac{r^2-3r-2}{2}>0
\]

for `r>=8`. Any reachable state retaining at least `r` distinct positive counters
therefore has remaining sum greater than `N`, hence greater than its deficit, and
is nonempty. This excludes both forms of terminal state.

### Owner-turn length and the no-early-terminal induction

During a still-uninterrupted turn beginning at positive deficit `d`, the deficit
after a noncatching prefix is `d` minus that prefix's sum. If the mover still has
the turn after `h` picks, those `h` distinct positive counters have total strictly
less than `d`. Their total is at least `h(h+1)/2 >= N >= d`, a contradiction.
At zero deficit the first pick switches. Equality is correctly counted as a
switch, not a further continuation.

The potentially delicate part of Step 4 is not circular. It can be written as
the following bounded-prefix induction. Fix a `t`-subset `T` of `S0`. Suppose
`j<t` macros have finished, no more than `jM` counters have been removed, and a
target remains. Pick a present target `x` at the opponent node. Its child is
covered and the number removed is at most `jM+1`.

If the pick does not catch, this child is already the next opponent node. If it
does catch, follow the prescribed owner picks. After `ell` such picks, for every
`0<=ell<=h`, the number removed is bounded by

\[
jM+1+\ell\le (j+1)M\le tM.
\]

Consequently every prefix through the prospective `h`th owner pick has at least

\[
r_0-Mt\ge N-1-Mt\ge
\left\lceil\frac{N-1}{2}\right\rceil
=\left\lfloor\frac N2\right\rfloor
\]

counters remaining. Here the middle inequality uses integrality and `2Mt<=N-1`.
The nonterminal-zone result supplies a legal prescribed owner pick whenever one
is still needed; it is not inferred from an already completed macro. The
owner-turn bound forces a switch by pick `h`. Thus the next opponent node really
exists, with no early termination anywhere inside the macro.

Every completed macro removes at least the target selected at its start. If owner
picks remove additional targets, the process finishes sooner. If the final target
is removed in the middle of an owner turn, the construction can still finish that
turn within the same budget. Hence at most `t` macros remove every element of `T`
and end at an opponent node. For `t=0`, the entry node itself is the witness.

All owner choices in this construction are the choices of the fixed certificate.
The construction is repeated separately for each target set; it does not change
the owner's policy from target to target. Selecting a presently available target
requires neither future knowledge nor an assumed fixed pairing. Continuing
opponent picks remain opponent nodes and are covered by the same local rule.

### Counting distinct states, not histories

Project the listed opponent nodes with at most `a=Mt` deletions onto their deleted
sets `A=S0\S`. The resulting finite family `C` has cardinality at most the node
count. The preceding construction proves that each `t`-subset of `S0` is contained
in at least one member of `C`. Each member contains at most `binom(a,t)` target
sets. Therefore

\[
\binom{r_0}{t}\le |C|\binom at
\le (\#\text{nodes})\binom at.
\]

This is a union bound over sets, not an injection from paths or targets into nodes.
Many targets and arbitrarily many histories may merge at one node without
invalidating it. Multiple nodes with the same remaining set can only make the
projection smaller.

Since `r0>=N-1>=2a` and `a=Mt>=t`, for `0<=i<t` we have
`r0-i >= 2(a-i)`, with positive `a-i`. Multiplying the falling-factorial
inequalities and cancelling `t!` gives

\[
\binom{r_0}{t}\ge 2^t\binom at.
\]

The factor `binom(a,t)` is positive, including when `t=a=0`. Cancellation proves
the claimed node bound. The floor choice of `t` and the choice
`h=ceil(sqrt(2N))` have the advertised consequences: a conditional
`2^{Omega(sqrt(N))}` lower bound, not a `2^{Omega(N)}` lower bound.

## Toy calibration and interpretation

At every nonempty synchronization state of the paired game, the mate is still
available after the adversary's pick. Any other defender response loses by the
specified rules. Thus every nonlosing certificate is forced to cover the mate
response after every adversarial member choice. Its synchronization-state family
contains the full label set and is closed under deleting each present label.
Successive deletions reach every subset. Conversely, all subsets support those
transitions. This proves the exact `2^k` synchronization-state count, including
`k=0`. It applies to every nonlosing policy, not merely a chosen implementation.

The short induction proving that mate responses work is compatible with the
exponentially large explicit state family. There is no deduction from explicit
representation size to mathematical proof length, symbolic strategy-description
length, or a lower bound for a richer checker with proved macro rules or symmetry
quotients.

For Catch-Up, existence of a valid certificate remains a separate hypothesis.
The result neither constructs a nonloss strategy nor proves the game conjecture.
When a certificate exists, pruning to reachable nodes preserves validity and
bounds the minimum above by `2(N+1)2^N`, using masks, reachable deficits, and actual
movers. This upper bound is compatible with the lower bound. A sum of the two
players' minima is meaningful only where both certificates exist; their nodes
are counted separately as stipulated. Extracted witness sizes are upper bounds
for the corresponding minima, not established exact minima.

## Review gates

- Met: the checker language and root agree with the actual game rules.
- Met: adaptive choices, continuation, equality, and early termination are handled.
- Met: the lower bound counts distinct states after allowing history merging.
- Met: certificate existence, explicit representation size, and proof length are
  separated.

There are no abandoned mathematical review gates. Compilation and the transitive
axiom audit remain the author's separate verification tasks, not claims of this
review.
