# Maximum-companion recovery: assurance and reproduction

Recovery date: 23 October 2026. Finding **CU-R001** is a later, conditional
recovery related to historical CU-L011. The [manifest](reply-maximum-companion.json)
distinguishes original cached bytes, reconstructed source, context-only Git
provenance, omitted private metadata and the still-missing August source file.

## Reproduce

From the repository root with its pinned Lean 4.27.0 dependencies:

```sh
lake --wfail build
python3 scripts/check_axioms.py
python3 scripts/check_recovered_reply.py --lean
python3 scripts/check_collection.py
python3 computation/check_semantics.py
lake env lean --run computation/CheckEarlier.lean
```

`check_recovered_reply.py` without `--lean` checks five pinned fingerprints,
the source-level declaration inventory, publication hygiene and deliberately
corrupted-input rejection. It does not prove mathematical correctness. With
`--lean`, it runs two separate environments:

1. [ReplayReplyMaximumCompanion](ReplayReplyMaximumCompanion.lean) imports only
   the current verified reply-digraph prerequisites. It reads the original module
   data and topologically re-adds **all ten declarations** using
   `Environment.addDeclCore` with `doCheck=true`. No historical imported environment
   is installed, no unchecked insertion is used, and no expression is rewritten.
   An invalid `False` proof is rejected before replay; only theorem and definition
   declarations are accepted. Every replayed declaration's transitive axioms are
   checked against the standard three permitted axioms. The wrapper also checks
   the exact ten-name inventory and both headline axiom reports.
2. [CompareReplyMaximumCompanion](CompareReplyMaximumCompanion.lean) imports
   the independently compiled readable source. Without installing any old
   declaration, it compares four public types and two definition bodies with the
   cached expressions using Lean definitional equality. Kind and universe
   parameters must match; substituting `False` for a signature must fail.

The readable library proof builds without either archival input. The replay
diagnostic requires the pinned Lean format, but no private checkout or lost
source. This is fresh kernel checking of old terms plus a new readable proof,
**not** source-text recovery and not reliance on native evaluation.

## Review of the mathematics and scope

The constructive argument is in the [result guide](../results/reply-maximum-companion.md).
A hostile self-review checked the following possible overclaims:

- An edge's WIN belongs to the replying player, not the opener. Since `a<c`,
  that reply continues the same player's turn; no sign negation is introduced.
- Nonempty/catchable is needed when identifying value with the best legal pick;
  those assumptions are explicit for **every** smaller member of `S`. No
  catchability premise is inferred from the existence of an unrelated edge.
- The cross-pick equality is used in both possible orders of `a,b`, with all
  strict inequalities justified by membership, erasure and the maximum bound.
- Winning move implies winning value only through the nonterminal recurrence.
  The proof does not assume alternating turns or ignore adversarial replies.
- Neither parity nor initial-interval geometry is smuggled into the statement.
  The result does not establish every-opening neutrality or unconditional
  maximum outdegree exclusion; it says nothing about the shifted graph.

This is an explicit self-review, not a separate human or independently staffed
review. Fresh builds, comparison and axiom checks support the narrower claim.

## Search scope and remaining missing artifacts

The read-only recovery search inspected 35 registered worktrees, including
ignored build files, and branch/reflog history. It scanned 18,146 stored Git blobs
(including unreachable objects; 387,330,395 bytes) against all 24 known original
SHA-256 fingerprints in the missing-artifact ledger; there were no matches.
That search is a retained local investigation, not a reproducible public proof
of absence: its Git object database and private machine state are not vendored.

The six source-level declarations are visible in the recovered `.ilean`; the
`.olean` supplies their original proof/definition expressions plus four generated
declarations. Cache metadata points to a now-absent untracked source in a checkout
directory whose basename matches `codex/catchup-ci-fix`. The manifest records that
branch's observed tip, not a proven checkout association or compilation-time
revision. It is not a tracked source at that commit and does not establish
historical authorship or creation date.

The original named August scratch source and its reported SHA-256 remain
unrecovered. The other missing scratch proofs, audit scripts and large tables
remain missing too. A second source-absent cached module,
`catch_up.TwoStepParityScratch`, exposed only `main` in its metadata; it supplies
no recovered mathematical theorem in this contribution. No new large computation
or research campaign was run.

## Completed checks

The check receipt and retained public logs are listed in
[reply-maximum-companion-checks.json](reply-maximum-companion-checks.json).
Earlier 98 module sources, cryptid proofs, historical ledger and pinned
toolchains are preserved. Hosted CI is separate from these local receipts.

- Mathematics: `lake --wfail build` passed; named axiom audit passed for 164
  endpoints and the full audit for 4,367 public theorem declarations (including
  generated ones). The new source contributes two public theorem statements.
- Recovery: ten original declarations replayed; four source signatures and two
  definition bodies matched; invalid-proof, signature-mutation and corrupted-input
  controls rejected their respective bad inputs.
- Collection: 99 modules, provenance, source fidelity, documentation links and
  historical ledgers passed. Semantics, earlier certificate regressions and both
  bounded solver/campaign smoke checks passed; no large search was run.
- Cryptid: normal `lake build` and both audits passed (23 named / 500 public
  baseline; 201 named / 2,962 public component declarations). An additional
  `lake --wfail build` attempt failed on the five pre-existing module-system
  import warnings in unchanged sources. Those warnings are also noted in the
  [earlier port receipt](fifth-endpoint.md); this task does not repair them or
  claim warning-free cryptid compilation.

These were incremental builds using existing pinned dependency/local caches,
with the new source compiled here, not clean from-source rebuilds of Mathlib or
every unchanged module. Public build logs replace machine-specific repository
and home paths with placeholders; original and public log fingerprints are both
recorded. Earlier receipts and immutable artifact bytes are not edited.

The [subsequent PR review](pr4-review.md) reconciles this contribution with the
separately merged endpoint ports, bringing the combined catalog to 101 modules.
The original check receipt remains a historical run: its shared-infrastructure
fingerprints are not requirements that future aggregators and CI never change.
The recovery manifest still pins all three Lean source/check files and both
original artifacts; fresh replay and comparison remain mandatory.
