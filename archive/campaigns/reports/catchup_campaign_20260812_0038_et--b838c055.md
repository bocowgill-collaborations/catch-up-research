> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Catch-Up Campaign — 2026-08-12 00:38 ET

Status: ACTIVE

Hard wind-down deadline: before 2026-08-13 08:30 ET.

This is a new campaign log. The 2026-08-08 reports remain unchanged.

## Objective

Resume from the certified finite frontier and seek a complete proof of the Catch-Up
conjecture. If no complete proof survives adversarial audit by the deadline, preserve
the strongest rigorously proved new results, exact counterexamples, blocked routes,
reproducible artifacts, and the smallest explicit remaining gaps.

## Baseline

- Branch: `codex/catchup-campaign-20260812`
- Starting point: private repository `the historical private research remote`
- Prior frozen reports:
  - `CATCHUP_FINAL_REPORT_20260808_2206_ET.md`
  - `CATCHUP_CAMPAIGN_20260808_2206_ET.md`
  - `CATCHUP_PROGRESS.md`
- Certified root-draw frontier: parity-admissible intervals through `N = 28`.
- Certified dense invariant: `DenseThreeHoleNonloss N` for `9 ≤ N ≤ 25`.
- Sharp surviving parametric route: dense successor reduction, exact small-gap endpoint
  strata, and the shifted-upper-tail package. This is only one route in the portfolio.

## Approach-family registry

| Family | Initial mandate | State |
|---|---|---|
| Minimal counterexample | Derive necessary structure of a least losing interval | active |
| Difference-game algebra | Seek conjugacies, ghost-counter, modular, or scoring invariants | active |
| Macro-turn hypergraph | Exploit the exact completed-turn hypergraph and minimax polarity | active |
| Online quota allocation | Maintain draw quotas under arbitrary legal replies | active |
| Interval decomposition | Find bounded prefix/tail interfaces or prove they cannot exist | active, pruned to distinct lines |
| Four-step induction | Seek a genuine `N -> N+4` strategy transfer | active |
| Two-step/parity transfer | Seek odd/even or `N -> N+2` propagation | active |
| Reply-digraph global theory | Control reply cycles without assuming local neutrality | active |
| Dynamic pairing/matching | Test adaptive rematching beyond fixed queues | active |
| Flow/LP duality | Find integral strategy or obstruction certificates with useful structure | active |
| Additive/extremal subset sums | Turn density into legal safe turns or hole lower bounds | active |
| Majorization/potential | Search vector-valued monotones that survive catch/continue polarity | active |
| Repository/frontier audit | Freeze exact theorem surface, trust boundary, and delivery state | active |

Blocked families will be reopened only after a materially new invariant, construction,
or proof mechanism is supplied.

## Catch-Up adversarial checklist

Every proposed proof or reduction must explicitly survive:

1. the perspective switch at a catch (`x >= deficit`) versus continuation below it;
2. the special zero-deficit rule, where the first positive pick ends the turn;
3. natural-number subtraction and predecessor-hole boundary cases;
4. pruned/terminal states with total remaining sum below the deficit;
5. preservation of effective-total parity;
6. exact completed-turn legality, including a valid final counter and strict prefix bound;
7. reachability claims versus statements about arbitrary normalized positions;
8. the difference between one-sided nonloss and a draw, and between fixed owner and mover;
9. universal opponent replies rather than a single neutral or partition-preserving reply;
10. hole growth and closure under the proposed response grammar;
11. genuine decrease of any proposed rank, including reply-digraph cycles;
12. certificate trust boundaries, target leaves, and native-evaluation assumptions.

## Chronological log

### 2026-08-12 00:38–01:00 ET

- Pulled the private `main` branch and created `codex/catchup-campaign-20260812`.
- Preserved the prior reports under their original filenames.
- Started a deliberately diverse first wave across thirteen approach families.
- Detected and pruned an accidental deep audit expansion that saturated the agent pool;
  retained only mathematically distinct branches.
- Detected one transient scratch Lean file under the production source glob; instructed
  its owner to move it to `/private/tmp` or make it warning-clean before baseline rebuilds.
- First exact result received: the full finite game DAG admits an integral OR/AND flow
  formulation for `CanAvoidLoss`, but the reachable loss `Position({3,4},3)` refutes
  coarse complement/equal-marginal turn flows. This is a useful exact formulation, not
  yet a simplifying invariant.

### 2026-08-12 01:00 ET checkpoint

The first portfolio produced several exact positive lemmas, but no complete proof.

Strongest new reductions:

1. A non-drawing interval `I_N`, for `N >= 7`, forces a loss in one of two bounded,
   top-two-complete families:
   - `pairDeletionPosition N 1 b`, with `2 <= b <= N-2`; or
   - `firstPairChild N x = ((Icc 3 N).erase x, x-1)`, with `3 <= x <= N-2`.
   The witnesses inherit even effective total and remove exactly two or four units from
   the interval total. Combined with the certified range, an admissible counterexample
   must have `N >= 31`. A warning-strict Lean proof exists in `/private/tmp` and is under
   independent audit.
2. A root `N -> N+4` proof needs only transfer of one common drawn old opening, not new
   openings or universal old-opening transfer. For opening one, the exact invariant is:
   every lower pair-deletion state is nonlosing and at least one is drawn. Warning-strict
   Lean packaging exists and is under independent audit.
3. The macro-turn hypergraph has an exact blocker duality: if `D = sum R - d + 1`, then
   minimal blockers of legal turns at deficit `d` are the minimal legal-turn core at
   deficit `D`. This is formally proved, but nonminimal turns are minimax-essential, so
   blocker duality alone does not reduce the game.
4. Certificate mining found a candidate structural lemma: consecutive picks made by the
   least-safe-move policy while still behind are strictly increasing. It holds throughout
   the N27/N28 strategy DAGs and exhaustive small-state audits; formal proof and relevance
   to a bounded strategy grammar are pending.

Routes now marked blocked absent a materially new mechanism:

- pointwise or same-history four-counter lifting;
- raw two-counter lifting (`N -> N+2` also changes triangular parity);
- static exact quotas, balanced partitions, or ordinary basis exchange;
- bounded-arity matching, even with complete rematching at each turn;
- finite block profiles or scalar prefix/tail interfaces;
- hypergraph minimal-edge, maximal-edge, complement, or blocker compression;
- componentwise/WQO monotonicity, translation, majorization, or scalar potentials;
- expectation-only/mixed-flow arguments without recursive endpoint safety.

The next wave is split between the two minimal-loss witness families, the lower
pair-deletion ray, the four alternatives in the seven-hole catch-rank theorem, owner-specific
weak simulations for opening one, and independent certificate-guided strategy mining.

[Administrative account detail omitted.]

[Administrative account detail omitted.]
stopped launching work, requested frozen handoffs, interrupted all still-running
agents and descendants, and ended expensive computation.

No complete proof survived. The strongest new formal result is the independently
audited minimal-counterexample normal form described at the 01:00 checkpoint,
now sharpened to an exact four-obligation closure surface. Further strong outputs
include the same-opening `N -> N+4` root transfer interface, the two-nonlosing-
openings criterion, a reply-graph common-maximum companion theorem, extensive
lower-ray exact data, and a proof-ready least-safe-increasing rule mined from the
N27/N28 certificates.

The full synthesis, exact artifact hashes, trust boundary, incomplete-artifact
warnings, and bounded restart plan are frozen in
`CATCHUP_FINAL_REPORT_20260812_0122_ET.md`. The old August 8 reports remain
unchanged.
