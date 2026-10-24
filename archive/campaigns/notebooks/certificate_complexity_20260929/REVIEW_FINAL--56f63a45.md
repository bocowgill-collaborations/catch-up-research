> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Final independent artifact review

## Verdict

**PASS.** The final Lean statements establish the reviewed conditional
exponential lower bound in the intended full-DAG model. The minimum-size
definition preserves the existence hypothesis. The structural compression rule
is sound and explicitly belongs to a richer certificate language. The small
witness sizes and their upper-bound-only classifications check out.

This review supersedes the earlier time-of-review warning that the end-to-end
Catch-Up lower bound had not yet been formalized. It does not weaken the standing
distinctions between certificate existence, full-DAG representation size, and
mathematical proof length.

No blocking defect or new mathematical gap was found. No helper agents, new
outcome search, minimization, or large computation was used. Only this review
artifact was written.

## Final theorem and minimum

`InitialCertificate N player dag` requires all four intended conditions:

- `DAGValid dag` for the original full checker;
- `dag.gameSize = N`;
- `dag.player = player`;
- the decoded root equals `initialPosition N = (I_N,0,p1)`.

The theorem `initial_certificate_exponential` quantifies over arbitrary natural
`N,t`, either `player`, and every `dag` satisfying that predicate. Its only
additional hypotheses are `16 <= N` and `12*t+2 <= N`; its conclusion is
`2^t <= dag.nodes.length`. There is no outcome-table premise, restricted owner
policy, target-cover premise left for the caller, or certificate-existence
conclusion hidden in the final statement.

`initial_certificate_exponential_floor` specializes this to
`2^((N-2)/12) <= dag.nodes.length` for `N>=16`. Here subtraction and division are
natural-number operations; the size restriction makes the intended floor
interpretation exact.

`CertificateExists N player` is the existential quantification of
`InitialCertificate`. The definition `minimumNodes N player h` requires an actual
proof `h` of that existence proposition and uses `Nat.find` on realizable node
counts. It does not silently assign zero, infinity, or another size to nonexistent
certificates. `minimumNodes_realized` supplies a certificate attaining the count,
and `minimumNodes_le` proves the upper-bound relation for every valid full witness.
Thus it is genuinely a minimum, not merely the size of an arbitrarily chosen DAG.

`minimumNodes_exponential` applies the universal DAG lower bound to a realizing
witness. `sum_minimumNodes_exponential` requires existence separately for `p1`
and `p2` and adds their counts, as stipulated. `exponent_linear_bound` proves
`N <= 24*((N-2)/12)` for `N>=28`, supporting the stated `c=1/24`, `N0=28`
conditional exponential bound.

The source-level proof follows the reviewed chain: two large counters preclude
terminal states; a completed owner turn deletes at most two large counters;
`force_large_target_deletion` allows arbitrary stored owner choices; and the
projection into `deletionFamily` pays for all collisions through the binomial
cover count. The final theorem is connected to the actual game and checker, not
only an abstract covering lemma.

## Structural compression

`maximumDeficitTarget` recognizes exactly a protected mover whose deficit is an
available maximum counter. It checks the mover, membership of the deficit, and
the upper bound on every remaining counter. It performs no minimax or outcome
table lookup.

`maximum_deficit_target_sound` uses the existing general theorem
`Position.value_ne_loss_of_deficit_is_max` and the fixed-player value equivalence
to establish `TargetSound`. `compressed_certificate_sound` then applies the
ordinary partial-checker soundness theorem.

The partial checker allows a recognized target to use the `.terminal` constructor
even when the game is not terminal, but only because its safety is separately
proved. Non-target nodes retain the original checker obligations. The original
`DAGValid` has not been changed. Therefore:

- full witness counts are upper bounds on `minimumNodes`;
- compressed counts are sizes of sound witnesses in the enriched partial language,
  and are not upper bounds on this full-checker `minimumNodes`;
- the observed compression does not contradict the full-DAG lower bound and does
  not establish any asymptotic compression rate or polynomial-size strategy family.

The checked rule guarantees nonloss, not necessarily a draw or a win. Its safety
proof is parametric, rather than an oracle identifying selected solved states.

## Small artifacts and classifications

After reading the replay code, I ran
`python3 research/certificate_complexity_20260929/replay.py`. It exited zero and
reported `CERTIFICATE COMPLEXITY REPLAY PASSED; semantic negative controls rejected`.
It verifies the exact initial roots, both players, mask bounds, terminal safety,
legal transitions, strict progress, owner choices, all opponent moves, node
uniqueness, and reachability of every measured node. It also verifies the stored
node counts, edge counts, JSON byte counts, and classification labels.

The confirmed node counts are:

| N | Protected player | Full | Compressed |
|---|---|---:|---:|
| 3 | p1 | 6 | 5 |
| 3 | p2 | 10 | 9 |
| 4 | p1 | 10 | 8 |
| 4 | p2 | 17 | 15 |
| 7 | p1 | 58 | 54 |
| 7 | p2 | 80 | 75 |

I separately counted the literal node lists in `CertificateComplexityFixtures.lean`;
all twelve counts match the replay. The six full fixtures prove
`InitialCertificate`; the six compressed fixtures pass the proved partial checker
and separately conclude `CanAvoidLoss` at the intended interval root.
The subsequently added `witness_node_counts` theorem also states all twelve
equalities directly and passed a second scoped fixture build during this review.

The replay confirms that compressed surviving nonterminal branches preserve the
same full-witness policy. It rejects the compressed witnesses under the full
checker, rejects a false terminal root, rejects omitted opponent coverage, and
rejects a changed root mover. Explicit equality-switch and below-deficit
continuation controls also pass.

These are witness sizes, not exact minimum sizes. The fixture sizes `3,4,7` are
below the asymptotic theorem's `N>=16` range and are not numerical evidence needed
for that theorem. Stored checker times are single-run observations, not independent
performance benchmarks or complexity estimates. JSON byte counts describe the
specified serialization, not mathematical proof-term size.

## Independent build and axiom verification

I ran the bounded, warning-strict scoped build:

```text
lake --wfail build catch_up.CertificateComplexityAudit catch_up.CertificateComplexityFixtures
```

It exited zero with `Build completed successfully`. Lake reused current compiled
artifacts and replayed the audit messages; this was not a clean rebuild.
After the author added `witness_node_counts`, I also ran
`lake --wfail build catch_up.CertificateComplexityFixtures`; it exited zero.

The inspected audit calls `Lean.collectAxioms` transitively on the central claims,
including all three final lower-bound declarations, both minimum-count support
theorems, the sum theorem, and the linear-exponent arithmetic theorem. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. Unexpected axioms cause
an error. The negative control requires detecting `sorryAx` in the unchanged
Catch-Up conjecture. The build reported that this control passed.

The compression module separately audits both compression soundness declarations,
and the fixture module audits every full-validity, partial-checker, and compressed
root-safety theorem with the same whitelist. Both audit groups passed in the
scoped build. Importing the conjecture's source module therefore does not amount
to using its unproved axiom in these results.

For reproducibility, the inspected SHA-256 hashes were:

```text
CertificateComplexity.lean
6fba3fde548885bce7de1541c53af8cd5293c65c686e7e7b989c9689a69523c1
CertificateComplexityHighCounters.lean
12c43854952ce7140447fe66bf0963b4ddee62070c8f5c3a5d00c894248f60b9
CertificateComplexityCompression.lean
f691cd2e6aae145bb1312d6de881be4edcb217048cf1c1ade96d1bdd88e3ef1a
CertificateComplexityFixtures.lean
94156db47f05f568ff99ac1bcde495c1347005c02fe058b6b73fcfb53310e081
CertificateComplexityAudit.lean
6eba7464d15b1179dd5c7c2bef83d1778c8a47f93b5cdd61c1e0da27119949cf
measurements.jsonl
4aa9b3fd2c61d90b269a047e308fd1379d93b79bd6122ffecc3413eb9bb6a1ae
```

At review time, `git diff --name-only` was empty and `git status --short` listed
only the new pilot research directory and new `CertificateComplexity*.lean`
modules. This supports preservation of existing tracked reports and certificates
relative to the current HEAD. No final timestamped report yet appeared in the
file inventory I inspected, so this verdict covers the listed source and data
artifacts, not unseen final-report prose or later edits.

All four final-review gates are met: final theorem/minimum semantics, sound
separate compression language, faithful classified witness counts, and scoped
build/transitive-axiom verification. No final-review gate is abandoned.
