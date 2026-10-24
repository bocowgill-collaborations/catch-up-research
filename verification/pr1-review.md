# PR 1 source-based review

Review date: 23 October 2026. Reviewed input: `4a778f693ec4d3d95bc93b343234eebfb69e390d`, against main `3293185b6e1e83f5b213f0fec1a25c974fd6255b` and the 15 pinned local refs in [legacy-sources.json](legacy-sources.json).

Verdict: **PASS WITH CAVEATS as an archival contribution**, after the corrections below. No remaining identified mathematical or privacy defect blocks this import. CI must pass on the corrected head before merge. This review neither validates the unrecovered proofs nor certifies the large historical computations.

Codex performed a new source-based adversarial pass in the same conversation as the import. It was not a separate human referee or an independently spawned agent. The original import receipt and four logs remain identified by [its initial snapshot](legacy-import.json); revised fingerprints do not turn those original logs into checks of the revised input.

## Concrete fixes

1. Made implicit hypotheses and perspectives explicit in CU-L001, 008, 012, 014, 015, 024, 029, 031 and 034. In particular, the shifted-tail budget counts deleted lower counters as well as upper holes; continuation and catch clauses have different deficit/catchability premises; zero deficit is an explicit branch of the rank reduction. Reserve preservation needs distinct positive counters, fixed disjoint pairs and an opponent-turn boundary, not just two numerical inequalities.
2. CU-L006 now says that the report *describes* the audits, rather than suggesting their complete supporting artifacts are retained. CU-L011 explicitly leaves the missing maximum-companion theorem's full quantified signature unrecovered. CU-L016 does not add an unsupported reachability assertion.
3. Restored the useful second obstruction in CU-L039: consecutive lower pivots need `k` disjoint complements of `q=k+2`, but at most `floor((k+1)/2)` exist. Its `k≥2`, `m≥2k+2` bounds and restrictions on the forcing language are now visible.
4. Pinned CU-L041/042 to the untracked run record's stable identifier, and linked CU-L043 directly to the supplied handoff, not just the later report quoting it. All findings now require a nonempty provenance-ID list.
5. Added the unrecovered N23/N24 table references and reported hashes. The ledger now has **25** missing-artifact references: the original 23 final-report references plus these two. Their recorded temporary locations were checked; this is not a filesystem-wide absence claim. N32 was explicitly not serialized, so there is no missing saved N32 table to invent.
6. Strengthened `check_legacy_archive.py`: immutable branch-tip history is reconstructed independently of the supplied commit list; exact per-row commit and branch attribution is checked; all 183 sanitized Git exports are reconstructed using [disclosed transformations](../scripts/legacy_archive_format.py); readable claims/evidence must match the JSON ledger. Added email/private-key and missing-history/false-attribution rejection controls.
7. Added [21 literal witness replays](../scripts/check_legacy_examples.py) through two independent recurrences, including every available first pick. These are included in the normal collection check. They are not historical scan replays, Lean theorem checks, or evidence for unbounded claims.

The final privacy pass also made the public formatter's account-detail and private-remote substitutions generic: the transformation code itself must not re-expose the private values it removes. Exact reconstruction of all 183 exports still passes.

## Claim-by-claim coverage

Here `(S,d)` is a normalized position with the mover tied or behind by natural `d`; its value is from that mover's perspective. `value(S)` is the tied initial game with a forced singleton opening. `(S,d,p)` also names the actual mover, not the protected identity. The completed-margin comparisons in CU-L024–027 protect fixed `p1`, including early-terminal allocation of the stranded remainder. See the linked sources for full definitions.

| Finding | Source comparison and assurance decision |
| --- | --- |
| CU-L001 | Compared reference normalization and executable correspondence. Added the mover-behind precondition; intended positive interval semantics are not silently generalized to negative counters. |
| CU-L002 | Compared the retained range dispatch: `N≤24`, parity exclusion at 25/26, then opening-one certificates at 27/28. Native/compiler trust is explicit; no new kernel-only range claim. |
| CU-L003 | Compared dense-family range and report definition: catchable, ambient subset, ≤3 holes, `d≤N`, even effective total, `9≤N≤25`; reachability is not assumed. |
| CU-L004 | Checked the two protected identities at one exact post-opening root and the current draw-opening criterion. Does not promote the separate all-opening observations. |
| CU-L005 | Checked indexed exact-child/coverage obligations and packed decoder description. Generic soundness is historical, not newly built. |
| CU-L006 | Compared audit descriptions, label-count interpretation and missing tools/tables. Reworded artifact availability. |
| CU-L007 | Compared both witness families and index bounds with the August 12 report. `N≥31` inherits native finite evidence; scratch missing. |
| CU-L008 | Checked polarity of exact-deficit catches and exceptional indices. Explicitly identified TA/TB as tied-game values and retained admissibility/`N≥31`. |
| CU-L009 | Compared the sufficient one-common-opening interface. Both fixed-player nonloss transfers remain hypotheses; their missing proof texts are not recovered by a report. |
| CU-L010 | Independently checked the logical consequence: two post-opening values ≠win cannot both be loss by winning-opening uniqueness, hence one draws and the draw-opening criterion applies. The report's contrary sentence cannot refute this conditional implication. |
| CU-L011 | Compared edge meaning and the eligible even five-hole audit scope. The report lacks the scratch theorem's exact signature; no unrestricted theorem is adopted. |
| CU-L012 | Compared all five exceptions and policy challenge count; restored `3≤b≤N` and tied-root perspective. Full historical scan remains unreplayed. |
| CU-L013 | Compared least-safe observation with the later current Increasing module. Interrupted August work does not acquire the later proof's assurance retroactively. |
| CU-L014 | Compared all three predicate definitions and the 12 held-out counts; these sum to 61,746,189 clause tests, not necessarily distinct positions. All deficit, hole, parity and size qualifications are explicit. |
| CU-L015 | Compared the full seven-hole theorem signature and existential winning-move conclusion, including the missing-predecessor set and `y>x−d`. Zero/low/hole/tied branches remain open. |
| CU-L016 | Replayed both literal draw-to-win four-lift witnesses; no initial-interval counterexample or new reachability result asserted. |
| CU-L017 | Compared 106,633/105,712/921 counts and failures at six through nine counters. These finite examples do not exclude every larger fixed cutoff. |
| CU-L018 | Compared progress-ledger simulation variants and current generic soundness. A searched finite product witness is not uniform basin membership. |
| CU-L019 | Replayed the winning `{3,4,5}` and equal-partition trap `{4,5,6,7,8}`. The reported 1,954-set scan and 390 nondraw count remain historical. |
| CU-L020 | Compared the failure list and descent/potential sources. Claims exclude named mechanisms, not every refinement; growing holes defeat the advertised closure. |
| CU-L021 | Compared the exact archived signature: `N≥7` and opening **one** drawn at `N−4`, with no parity premise. Root draw alone is weaker than the required hypothesis. |
| CU-L022 | Replayed both values, every copied move and unique simultaneous repair `(U2,V5)`. Source's unmatched-set conclusion and auxiliary scope retained. |
| CU-L023 | Replayed both sparse values and the distant drawing reply. Compared seven disjoint erased pairs in the parent; not the original exactly-one-pair target. |
| CU-L024 | Compared the current parametric phase, terminal-margin and chosen-shadow-trace theorems. Clarified fixed protected `p1`, the max policy's turns and trace `[c,a]`. |
| CU-L025 | Compared the copied-suffix margins 2/10 and the legal global-max failure margin −2 with archived traces. Policy-specific failures are not impossibility of every controller. |
| CU-L026 | Compared Protocol quantifier order, nonempty strict-win filter, raw remaining-field buffers and finish condition. The 87-node finite policy is not a parametric translator. No archived Lean build rerun. |
| CU-L027 | Compared both preparation transitions, copied-pair trace premises and forced-reply lemma. Conditional uniqueness is not existence of a winning strategy. |
| CU-L028 | Replayed sparse loss, shadow win and all first children. Compared legal-prefix caveat: the size-eight shadow root draws, so that copied prefix is not a supplied winning strategy. |
| CU-L029 | Replayed sparse cycle edges, failed interior slide and singleton outgoing edge from 7. Added exact second support; shifted graph edges are not plays or tied-root replies. |
| CU-L030 | Compared conditional every-vertex successor and nonempty closed-walk statements. Simple-cycle extraction is informal; closed-walk existence alone is not a contradiction. |
| CU-L031 | Checked reserve algebra and empty-pair/early-terminal cases in the paper argument; compared initialization theorem's `N≥7`, legal `a`, and necessary-envelope status. No claim that preservation was Lean-formalized. |
| CU-L032 | Compared fourth-endpoint signatures, unconditional `N≥15` and parity-admissible `N=11,12` additions. Checked `[2,6,15]` is legal at deficit 9 (prefix sum 8), without repeating 6. |
| CU-L033 | Replayed all three winning catches at `({6,7,8},3)`. Positive-deficit uniqueness shortcut is invalid; the example lacks dense ancestry. |
| CU-L034 | Checked dominant-pair algebra as a candidate only: `M=sum T`, separation, utility change and no small-support pruning. Premature-pair argument needs nonempty T; empty T supplies the modified leaf. |
| CU-L035 | Compared current theorem with `InitialCertificate`, both protected players, `N≥16`, listed-node measure and floor bound. Not arbitrary proof length or certificate existence. |
| CU-L036 | Compared the sound maximum-equals-deficit target and N=3/4/7 fixtures; distinguished the paired toy from Catch-Up. No polynomial-size conclusion. |
| CU-L037 | Compared fifth-endpoint `N≥23` and four-tail `m≥17` signatures, forest counts and collision at 16. Historical checked source, not a port or new build. |
| CU-L038 | Compared current obstruction and forcing-language quantifiers. A structurally permitted witness need not actually be losing; semantic branch exclusion lies outside this negative result. |
| CU-L039 | Checked the exact packing arithmetic, attained blocks, consecutive-pivot argument and consumed-reserve support transformation. Restored the missing scheme argument, without a new formalization. |
| CU-L040 | Compared current three-pair/orphan signatures, including all size/gap/separation bounds. Exactly three pairs is not an arbitrary odd-pair induction. |
| CU-L041 | Compared six result rows, state count `(N+1)2^N`, memory/serialization conventions and retained checksums. N31/32 novelty correction is justified by earlier external reports; no large replay. |
| CU-L042 | Compared all six seed means and simulation counts. Neither empirical mean nor favored opening certifies a value. |
| CU-L043 | Compared handoff's finite sequence/openings and source-status narrative with supplied correspondence; checked the later N≥21 qualification. No private correspondence/PDF copied; N≤38 stays external reported evidence. |

## Completeness and fidelity

The original local source checkouts share a Git database. All 14 locally named Catch-Up branches are included and still match their pinned tips. An independent reconstruction of scoped history found the same 55 commits, 236 paths and 290 path/blob pairs. All 183 exported Git-backed versions reconstructed exactly. The 28 multi-version paths include same-name changes, not only added declaration names. Earlier report variants, the thirteen Paper game-file versions, the two pre-move GameTheory versions, old attractor/boundary solvers and trace drivers remain present. No omitted mathematical blob was found within this scope.

Seven metadata-only shared-API entries were compared against their current destinations: geometric pairs, completed turns, draw opening, exact-sum obstruction, pair deletion, reachable bounds and winning opening. After removing comments, imports, indexing attributes and whitespace, all seven complete code bodies matched their current destinations, not just declaration names. Sixteen other metadata-only entries are explicitly large native/generated payloads, including the N27/N28 roots and dense certificates; they are not public build dependencies.

The Catch-Up-specific historical CI workflow is deliberately outside the mathematical path filter. Its source is `.github/workflows/catch-up-ci.yml` at local commit `2c8c3839add9dbf4a7aff2587174a309cd34b243`. It ran the dense certificates sequentially and used a 180-minute job limit. It is not installed or counted as a newly recovered mathematical artifact. Full reproduction of the old native tranche still requires its old layout and large payloads; current portable bounded commands are separate.

Privacy scanning covered the changed public text, including manifests and guides: local paths, email addresses, token/private-key patterns and the private historical remote. Two long-string flags were public GitHub issue URLs, not secrets. Disclosed sanitation changes are mechanically reconstructed; private correspondence and third-party PDFs remain excluded. Original hashes are retained. Absence of a scanner match is not a general confidentiality guarantee.

The three handoffs were also reconstructed exactly from the supplied originals using the disclosed sanitation and evidence banner. The untracked run record matched its original hash and reconstructed exactly after the two documented novelty-sentence replacements. These were local review checks; their private originals are not dependencies of public CI. Direct mutation tests against the full source-audit path rejected an omitted commit, a false observed-commit list and an invented branch attribution.

## Checks and CI

Passed after correction:

- `python3 scripts/check_collection.py`: 96 modules, archive/source fingerprints, documentation links, guide/ledger consistency, 893 noninitial comparisons, 13 roots and the 21 literal positions.
- `python3 scripts/check_legacy_archive.py --source-repository PATH`: all pinned-ref scoped history, exact attributions, original hashes and 183 export reconstructions.
- `python3 scripts/check_legacy_examples.py`: 21 fixed positions, every first pick, two recurrences.
- `python3 computation/experiments/check.py`: small existing solver calibration and corruption/limit controls.
- `python3 computation/experiments/check_campaign.py`: 31 fixed positions, mutation witnesses, SMT goldens, DAG, seeds and incomplete-result controls.
- `git diff --check` and proof/pin byte-preservation comparison against the main base.

On input `4a778f693ec4d3d95bc93b343234eebfb69e390d`, both hosted [push](https://github.com/bocowgill-collaborations/catch-up-research/actions/runs/40036803125) and [PR](https://github.com/bocowgill-collaborations/catch-up-research/actions/runs/40036864806) workflows completed successfully: collection plus mathematics/cryptid builds and transitive axiom audits. These results cover that input, not automatically its successor. Corrected-head CI is reported on the PR. No local Lean build/audit was rerun: all compiled proof sources and both toolchains are unchanged.

## Remaining caveats, not hidden acceptance claims

- The 25 named artifacts remain unrecovered at the checked locations; large generated payloads remain metadata-only. These deliberate archival gaps do not prevent merging an honestly labelled archive.
- Maximum-companion scratch hypotheses and several other scratch proof texts remain unknown, not inferred from successful-check prose.
- No theorem-backed claim is made for historical numerical counts solely because their reports are retained. The new fixed-witness diagnostics do not certify their surrounding scans.
- Handoffs and the editorially corrected untracked run record have original/exported hashes, but require their private originals for an exact editorial comparison; they are not included in Git-blob reconstruction.
- Merge readiness is limited to this archival PR, not the validity of the open conjecture or acceptance of every historical approach. No merge was performed.
