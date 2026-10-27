# Two-buffer controller port and audit

Date: 27 October 2026. Base: `fa984bdc3433232480c415604255df36563e9190`.
See [the result guide](../results/two-buffer-protocol.md) for all quantifiers and
limitations, and [the source manifest](two-buffer-port.json) for exact hashes.

## Source fidelity

The two complete protocol/controller files originate in Formal Conjectures
commit `fbce0be86588dd31d7423ae1b026b2b618714e3a`, on local branch
`codex/catchup-two-buffer-20260928`. Local Git history has one introducing
commit for these paths; the archival manifest also identifies later commits
and branches retaining the same blobs. The branch's two files were checked
against the archived bytes. No private repository is required to reproduce
the public port.

Changes are limited to:

1. Replace the protocol's broad `ScoreDebtRepairCertificates` import with
   `CatchUp.Earlier.ScoreDebtTerminalRepair` and `CatchUp.Classifier`. The former
   already supplies the exact `TwoBuffer` and completed-margin dependencies.
2. Adapt the mandatory controller's protocol import. Extract only the original
   `exchangeLeft` and `exchangeRight` definitions, with their docstrings, into
   their original namespace in that file. The surrounding obstruction theorems
   remain archived, not newly verified.
3. Remove the Formal Conjectures indexing attributes `category` and `AMS`.
4. Narrow the lookup docstring: default zero is illegal in the certified
   instance's reached nonterminal actual states, not in every possible natural-
   counter state. A general support may contain zero. No definition or proof is
   changed by this editorial correction.

All theorem statements, proof bodies, protocol constructors, policies and
defaults are preserved. The source checker reconstructs these edits byte for
byte, verifies original Git blob identities and cross-references the historical
manifest. It also independently reconstructs all 76 table rows from the retained
JSON, checking score normalization and scheduling roles. Eleven terminal nodes
are omitted from lookup because the checker handles termination first. The
existing Python replay validates the JSON edges and ownership data separately.

Negative controls change the margin allowance, a root support, a controller
pick, a table row and a scheduling side. All must be rejected or differ from
the accepted reconstructed artifact. These controls check the source/data
boundary, not the Lean kernel.

## Mathematical audit

Verdict: pass for the exact finite protocol statement. Two in-thread review
passes found no proof-body gap; this is not an independent human review.

`run_check_sound` inducts on the finite budget. The zero case requires both
terminal games, buffers and margin. The successor case first checks buffers,
then either finishes or constructs exactly the selected action. Every recursive
call decreases the budget; universal actual and shadow branches remain universal.
The shadow branch also requires a nonempty admissible-reply set. Its classifier
bridge proves the exact opponent-nonloss negation rather than assuming an
unverified solver answer.

`mandatory_policy_checked` uses ordinary `decide +kernel` at budget twelve.
`mandatory_protocol` applies soundness to that proof. Policy lookup defaults to
`actualPick 0`; zero is absent from every reached nonterminal actual support,
so a missing reachable entry cannot silently pass. Terminal payoff accounting
does not erase stranded counters from the raw buffer fields. The comparison is
in fixed `p1` perspective, not mover-relative value.

The port proves the finite inductive protocol, not a parametric translator or
a separately extracted strategy implementation. The scalar strategy API,
necessary-bound theorem and parametric two-pick repair remain archived. A
historical report of those proofs is not upgraded by this contribution.

## Verification

[The check receipt](two-buffer-port-checks.json) records 13 successful commands,
exit statuses, retained output logs and fingerprints. Builds used warm pinned
dependency and local caches; these are not clean-build timings. The new
modules are also compiled directly from source. Both pinned packages are built
and receive named and all-public transitive axiom audits. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed; the audit rejects a `sorryAx`
negative control. The mathematics package additionally builds with `--wfail`.
The unrelated cryptid package uses its documented normal build; its existing
module-system warnings are not changed by this port.

The mathematics audit checks 178 named endpoints and 4,539 public/generated
theorem declarations. Separate cryptid audits check 23 named / 500 public and
201 named / 2,962 public declarations. Generated theorem counts are not counts
of mathematical findings. Comparison with the base confirms 344 existing Lean
source/toolchain files are byte-identical; only the top-level import list and
named audit endpoints change among existing Lean files.

Main's concurrent README/citation-only update was incorporated before publication.
It changes no proof, dependency, toolchain or verification command.

Run the four commands in the result guide for the core checks. The broader
[verification instructions](README.md) cover semantic replays and the cryptid
package. No large search or new exact outcome computation is part of this port.

AI assistance was used for the mechanical port, provenance checks, review and
documentation. Kernel validation and source fidelity are independent checks;
neither establishes the missing uniform strategy-transfer theorem.
