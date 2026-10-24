> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up: exponential explicit certificates, not a proof-length barrier

## Verdict

**The proposed conditional exponential lower bound is proved for the specified
full, atomic strategy-DAG representation. Catch-Up itself remains open.**

For either protected player, whenever a full nonloss certificate exists,

\[
N\ge16\quad\Longrightarrow\quad
D_p(N)\ge 2^{\lfloor(N-2)/12\rfloor}.
\]

This is a parametric, end-to-end Lean theorem, not a fit to numerical data or a
lower bound on a preselected policy. It survives independent mathematical review,
warning-strict compilation, and a transitive axiom audit allowing only `propext`,
`Classical.choice`, and `Quot.sound`.

Consequently the candidate `D(N)>=2^(cN)` for admissible sufficiently large N,
conditional on both certificates existing, holds with **c=1/24 and N0=28**.
Indeed each player's minimum satisfies that weaker bound separately, and
`D(N)=D_p1(N)+D_p2(N)` counts the certificates separately. The theorem does not
need parity; restricting to even triangular totals is permitted.

The right interpretation is: **fully expanded certificates are necessarily
exponential, but mathematical proofs need not be.** A paired-game calibration
demonstrates that distinction. A small theorem-backed compression experiment also
works, although its savings are modest and no polynomial-size symbolic certificate
family for Catch-Up has been constructed.

## Repository, time, and preservation

- Checkout: `HISTORICAL_TMP/catchup-score-debt-20260928`.
- Base: `79ae377f`, the newest local descendant of `d016a035` at inspection. This
  includes the preceding fourth-from-top endpoint theorem.
- New branch: `codex/catchup-certificate-complexity-20260929`.
- Started September 29, 2026, **00:46:04 EDT**; maximum deadline **03:16:04 EDT**.
  The main result and the requested small compression test concluded early; the
  remainder of this session was used for verification and preservation.
- Final acceptance-gate verification completed by **01:30:52 EDT**, about 45 minutes
  after the start: all five gates met. Administrative stopping details omitted.
- The starting research tree was clean. All deliverables are new files. No old
  report, certificate, or production module was edited. The separate main checkout
  and its unrelated untracked file were left untouched.
- One independent reviewer was used, with follow-up reviews of the strengthening
  and final artifacts. No conceptual helper or additional reviewer was spawned.
- No push, merge, frontier expansion, large table, certificate optimization, SAT,
  or QBF run was performed. New exact game computations used only N=3,4,7 and
  took far less than the 15-minute allowance.

## 1. Exact certificate model

`InitialCertificate N player dag` means:

1. `CertificateChecker.DAGValid dag`;
2. `dag.gameSize=N` and `dag.player=player`;
3. the decoded root is `GamePosition(Icc 1 N, 0, p1)`.

This includes the initial opening. At deficit zero every legal positive pick x
switches to p2 and leaves `(I_N.erase x, x, p2)`. The theorem
`initial_after_pick` checks that identity, rather than silently starting from a
post-opening root. The empty-root convention is harmless but outside the main
lower bound's N>=16 range.

The existing full checker records the remaining mask, deficit, and **actual**
player. A protected-player node selects one legal pick; an opponent node covers
all legal picks. Repeated identical states may share a node. Every leaf must be
genuinely terminal and safe for the protected player. Nonterminal outcome-oracle
leaves, symmetry quotients, and theorem-backed macros are excluded from this model.

The count is `dag.nodes.length`, including root and terminal nodes. The checker
forbids duplicate encoded states. Unreachable listed nodes may be pruned and do
not improve a minimum. `CertificateExists` is separate from `minimumNodes`, whose
definition requires an existence proof and whose minimum is proved realized.
An absent certificate is **undefined in this measure**, not evidence of a huge
or infinite mathematical proof.

The candidate was formulated without assuming it:

\[
\exists c>0,N_0\;\forall N\in\mathcal A,\quad
N\ge N_0\ \land\ \text{both certificates exist}
\ \Longrightarrow\ D(N)\ge2^{cN}.
\]

The result above establishes it for this particular language. The size parameter
is the number N of distinct counters; no claim is made here in terms of an
arbitrary compressed input encoding.

For context, whenever a full certificate exists, trimming it to reachable nodes
gives the elementary upper bound `D_p(N)<=2(N+1)2^N`: there are 2^N remaining
sets, reachable deficits 0 through N, and two movers. This counting upper bound
is a mathematical observation, not an additional formal theorem in this delivery.
It says nothing about uniform existence.

## 2. Calibration: exponential DAG, short induction

The toy game has k labeled pairs `(i,0),(i,1)`. At synchronization all remaining
pairs are intact. The adversary picks any remaining member. The defender picks
a remaining member; a non-mate pick immediately loses. A mate pick removes that
pair and returns to synchronization. No remaining pairs is a terminal defender win.

Every nonlosing policy is forced to choose the mate. Every adversary-selected
pair deletion is covered. Thus its synchronization-state family contains the
full label set and is closed under deleting every present label. It contains all
2^k subsets. Conversely all subsets realize exactly **2^k synchronization states**.
Intermediate response nodes are also required by an atomic certificate: this is
not a claim that its total atomic-node count is exactly 2^k.

One short induction proves the mate strategy correct for every k: the mate is
available; deleting the pair leaves the same invariant with one fewer pair.
This is a different game, not a pairing proof for Catch-Up.

Lean proves the deletion-closure implication and exponential cardinality bound
parametrically in `CertificateComplexity.lean`. The transparent toy rules above
identify its synchronization family with that lemma; no general toy-game engine
was introduced.

## 3. The Catch-Up proof: count covered target sets, not histories

Let `L={floor(N/2)+1,...,N}`. The mechanism has five parts.

1. **Reachable deficit is at most N.** Picking x changes d to `|d-x|`; both x and
   d are at most N. Two remaining counters from L have sum greater than N, so
   a reachable state containing them cannot terminate early.

2. **A completed turn removes at most two large counters.** Its preparation
   prefix has sum strictly below its initial deficit, unless empty. Two counters
   from L already exceed N, so at most one is in that prefix. The final catching
   pick can add at most one. At deficit zero the first pick ends the turn;
   equality also switches. Arbitrarily many small picks do not change this bound.

3. **Enter from the actual root.** For protection of p2, the root is already an
   adversary node. For protection of p1, follow its prescribed opening, which
   switches to p2 and deletes at most one large counter. The entry retains a set
   S0 of at least `ceil(N/2)-1` large counters.

4. **Target deletion works against every defensive policy.** Fix any t-subset T
   of S0. At an adversary turn, pick a currently present target. If it does not
   catch, the adversary still moves. If it catches, follow the certificate's
   protected replies until the next switch. This macro deletes at most three
   large counters and at least one new target. At most t macros erase T. The
   condition `12t+2<=N` leaves enough large counters to exclude early termination.
   The formal proof constructs completed turns using the actual selected children,
   noncatching preservation of nonterminality, and strict cardinality progress.
   It does not assume an eventual-entry or compatibility theorem.

5. **Charge mergers explicitly.** Project reached nodes to deleted large sets
   `A=S0\remaining`, with `|A|<=3t`. Every t-subset of S0 lies in some such A.
   Each A covers at most `binom(3t,t)` targets, so

   \[
   \binom{|S_0|}{t}\le\#\text{nodes}\binom{3t}{t}.
   \]

   Since `|S0|>=6t`, falling-factorial comparison gives
   `binom(|S0|,t)>=2^t binom(3t,t)`. The latter binomial factor is positive,
   including t=0; cancelling proves the bound.

This explicitly allows many histories and many targets to merge into one node.
It covers every valid certificate, not merely the extracted least-safe strategy.
The protected choices are never changed to suit T. The adversary chooses from
the observed current state, with no future information. Large-counter interval
geometry supplies the constant deletion budget and terminal guard.

The initial version tracked all deleted counters and gave only
`2^{Omega(sqrt(N))}`, using the triangular bound on completed-turn length. That
complete argument and its formal theorem are preserved. Tracking just the upper
half strengthens the **same covering mechanism**, rather than adding another
unrelated route or numerical search.

### Exact Lean statements

In `CertificateComplexityHighCounters.lean`:

```lean
theorem initial_certificate_exponential (N t : ℕ) (player : Player)
    (dag : StrategyDAG) (hcert : InitialCertificate N player dag)
    (hN : 16 ≤ N) (ht : 12 * t + 2 ≤ N) :
    2 ^ t ≤ dag.nodes.length

theorem minimumNodes_exponential (N : ℕ) (player : Player)
    (h : CertificateExists N player) (hN : 16 ≤ N) :
    2 ^ ((N - 2) / 12) ≤ minimumNodes N player h
```

The audit module also proves the bound for the sum of the two minima and the
integer inequality `N<=24*((N-2)/12)` for N>=28. There is no remaining unproved
Catch-Up-to-cover step: this is an end-to-end checker-language theorem.

## 4. Small measurements and a richer compression language

The named experiment asks whether one existing structural rule compresses the
same policy: **a protected mover cannot lose when its deficit is an available
maximum counter**. This is already proved parametrically in `DeficitWinningBound`.
`CertificateComplexityCompression.lean` wraps it as a sound partial-checker target.
It performs no outcome lookup at the leaf.

The existing exact solver/extractor supplies full least-safe witnesses only at
N=3,4,7. Extraction then stops at the recognized structural leaves, using the
same ordinary-node choices and globally shared descendants. The experiment does
not sum independently minimized subtree sizes or attempt minimization at all.

| N | Protected player | Full nodes: upper bound on D_p | Macro witness nodes | Full JSON bytes | Macro JSON bytes | Nonterminal macro leaves |
|---|---|---:|---:|---:|---:|---:|
| 3 | p1 | 6 | 5 | 367 | 314 | 1 |
| 3 | p2 | 10 | 9 | 581 | 528 | 1 |
| 4 | p1 | 10 | 8 | 598 | 492 | 1 |
| 4 | p2 | 17 | 15 | 976 | 864 | 2 |
| 7 | p1 | 58 | 54 | 3,284 | 3,055 | 2 |
| 7 | p2 | 80 | 75 | 4,516 | 4,221 | 4 |

**No row is an exact minimum. Macro node counts are not upper bounds on D_p,**
because their nonterminal leaves are forbidden in the full language. They are
upper-bound witnesses in the richer, theorem-backed partial language. The full
checker rejects each compressed witness as a full certificate.

Bytes count the compact UTF-8 JSON encoding of each complete DAG object, excluding
the surrounding measurement record and newline. They are not compressed file
sizes or Lean-source lengths. The independent replay recalculates them.

Recorded full/partial checker times, in milliseconds, were respectively:
`1.451/0.217`, `0.160/0.149`, `0.198/0.164`, `0.523/0.448`, `8.607/7.618`,
and `17.979/15.768`, in table order. These are single local runtime observations,
not stable benchmarks or asymptotic verification bounds. In addition, all twelve
literal witnesses and their counts were checked by kernel `decide`; the fixture
module's scoped build took about 10 seconds in this checkout.

The raw JSON includes node and edge lists, counts, timings, and classifications.
`replay.py` independently checks masks, initial root, legal picks, actual mover,
equality switching, early terminals, all opponent replies, child coverage, unique
states, exact reachability, and the unchanged underlying policy. Negative controls
reject a fake terminal root, omitted opponent move, wrong root mover, and use of a
compressed witness in the full language.

Older aggregate campaign counts, such as the August 1,965,165-node total across
four owner certificates, are not presented as D_p minima or directly comparable
root/model measurements. Existing partial-certificate formats can stop at proved
targets and need separate accounting.

## 5. Verification and artifact map

Commands run successfully, scoped to the new modules and their dependencies:

```text
lake --wfail build catch_up.CertificateComplexityAudit catch_up.CertificateComplexityFixtures
lake env lean -DwarningAsError=true research/certificate_complexity_20260929/Measurements.lean
lake env lean --run research/certificate_complexity_20260929/Measurements.lean
python3 research/certificate_complexity_20260929/replay.py
```

The strict build covers:

- `CertificateComplexity.lean`: precise model/minimum, calibration, covering count.
- `CertificateComplexityGame.lean`: actual certificate paths, turn bound, earlier
  square-root-exponent version.
- `CertificateComplexityHighCounters.lean`: the stronger full exponential theorem.
- `CertificateComplexityAudit.lean`: summed-minimum bound, linear exponent estimate,
  transitive axiom whitelist, and a negative control detecting `sorryAx` in the
  existing unproved conjecture.
- `CertificateComplexityCompression.lean`: independently proved structural macro.
- `CertificateComplexityFixtures.lean`: literal full and compressed small witnesses,
  kernel validity/safety checks, counts, and a separate axiom audit.

No audited result uses `sorryAx`, `Lean.ofReduceBool`, a new axiom, or the unproved
Catch-Up conjecture. The original conjecture remains in the repository as an
unproved statement; importing its module is not a dependency on that theorem.
The negative control confirms the whitelist would reject such a dependency.

The research directory preserves `PLAN.md`, `GATES.md`, the initial argument,
the high-counter refinement, the independent reviews, measurement implementation,
raw witnesses, and replay checker. No incomplete experiment is in production sources.
The final independent review reran the strict build and replay and checked the
literal Lean fixture counts against the reported measurements.

## 6. Proof complexity and recommendation

The findings answer the representation question, not the original conjecture:

- Optimizing a full explicit DAG may improve constants, but cannot avoid
  exponential growth in N under this model.
- Failure to find a smaller DAG is never itself a lower bound; the new bound is
  instead a constructive adversarial covering theorem.
- Exponential explicit size does not imply exponential mathematical-proof size,
  symbolic-policy size, or difficulty for stronger theorem-backed representations.
- A short minimax program can conceal exponential execution; program length is
  not the number of expanded certificate states or verification operations.
- A uniform Catch-Up theorem would yield short symbolic instance proofs by
  instantiation in the same theory, without explicitly unrolling the full DAG.
  Lower bounds against all proofs in a strong arithmetic theory are a different,
  substantially stronger subject; nothing here establishes one.

The target proof-graph viewpoint agrees with the owner-choice/opponent-coverage
distinction studied by Furtak and Buro. Their NP-hardness result concerns arbitrary
input DAGs, not this Catch-Up family; it is not used here. Catch-Up's atomic moves
also require actual-player labels, since turns need not alternate at each pick.
See [Minimum Proof Graphs and Fastest-Cut-First Search Heuristics, IJCAI 2009](https://www.ijcai.org/Proceedings/09/Papers/089.pdf).

**Recommendation: bank this complexity result, change representation, and return
the main effort to direct parametric proof search.** Larger full certificates or
full-DAG minimization are not a promising route to a compact general proof. The
proved maximum-deficit shortcut is a small demonstration, not yet a sufficient
symbolic language. Next pursue a theorem-backed interval-family rule with a
well-founded rank, rather than a predicate that merely says the state is safe.

The prior endpoint report provides a concrete starting point: extend its finite
exact-sum forcing trees beyond the certified three-upper-counter family, with
legal completed-turn repairs at the leaves. General interior upper-opening
exclusion and the first-pair endpoint remain open; this session closes neither.
Any new symbolic certificate system must expose those missing mathematical rules,
not bury them in an outcome oracle or an assumed global compatibility statement.

There is no remaining gap in the proved full-DAG size theorem. The open questions
are uniform Catch-Up nonloss itself and whether a sufficiently expressive,
independently proved symbolic strategy language can certify it compactly.
