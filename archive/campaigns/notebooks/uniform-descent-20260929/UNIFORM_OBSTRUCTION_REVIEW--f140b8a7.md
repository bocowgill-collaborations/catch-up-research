> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent upper-only obstruction review

Date: 2026-09-29. Reviewer owns only this report.

## Acceptance ledger

- [x] U1: The quantified statement exactly describes two upper-only exact-block levels for every structurally permitted witness.
  EVIDENCE: Direct audit of UpperOnly at line 39 and no_two_upper_only_steps at line 183. The outer existential is one first block; the inner existential may depend on every structurally permitted w. There is no game-value premise.
- [x] U2: Boundary, availability, block uniqueness, and support identities are valid.
  EVIDENCE: All four public proof bodies checked, including m=6, k=2, arbitrary-k conditional lemmas, the exact erased support, and the kernel-checked sum-four lemma. Details below.
- [x] U3: Warning-strict affected build and transitive axiom audit pass.
  CHECK: lake --wfail build catch_up.UniformExactSumDescentAudit
  EXPECT: Build completed successfully
  EVIDENCE: Independent rerun after parent completion; exit 0, expected token matched, no warnings. CWD=HISTORICAL_TMP/catchup-score-debt-20260928; zsh launcher/direct child process; 2275 ms; SHA256(stdout+stderr)=95f64e0a1e31bd41ddfbd11789b57f962bc4bb3bf969b729bec67a8e21e97ce8; 814 bytes. All four declarations use exactly propext, Quot.sound, Classical.choice.
- [x] U4: No actual losing witness or general nonloss refutation is inferred.
  EVIDENCE: No new theorem mentions Position.value or loss. The selected witness is taken from the universally quantified structural set. The module expressly excludes semantic branch eliminations and alternative proof steps.

## Verdict

PASS. No substantive error or missing obligation within the claimed
two-step structural obstruction. Four gates met; none unmet or abandoned.
No file other than this review was edited by the reviewer.

## Quantifiers and exact scope

`UpperOnly S A m` means:

```lean
∀ w ∈ S \ A, (∀ a ∈ A, a < w) → m+3 ≤ w
```

Thus it restricts *every* structurally permitted witness, not merely some
selected witness and not merely witnesses already known to lose. For the
supports in the public theorems, `S ⊆ support m k` supplies the upper bound
`w≤m+k+2`; the explicit lower bound therefore means membership in the
original upper interval. The definition need not carry k separately.
All exact blocks in these applications are nonempty because their sums
are positive. Hence the all-members strict bound is equivalent to
`max A < w`; membership also gives every block element at least two.

For `m≥6`, `k≥2`, `no_two_upper_only_steps` rules out one first block A
with exact sum `m+4`, contained in the support after opening `m+4`, and
upper-only, together with this continuation condition:

> For every w remaining after A and strictly above every member of A,
> there exists an exact block B of sum w, contained in the support after
> deleting A and opening w, and upper-only relative to the original m.

B is allowed to depend on w. There is no unintended demand for a single
common B. There is also no restriction to pairs: A and B are arbitrary
finite subsets. The selected `w=m+3` must be covered because the condition
is universal. The proof never infers that `m+3` is the actual losing
witness supplied by the game-theoretic exact-sum obstruction.

This is a formal two-level combinatorial obstruction. Any recursive proof
tree whose only steps satisfy this exact structural condition would need
these first two levels, so it cannot close. There is no formal datatype of
all possible proof trees here, and there is no claim excluding additional
semantic terminal rules, branch exclusions, or lower-witness repairs.
That is an explicit scope limitation, not a missing step in the stated
Lean theorem.

## First block and arbitrary k

`first_block_forced` correctly has no lower bound on k. It is a conditional
statement about a hypothetical block in the erased support; it does not
assert that `m+4` is an available opening for k=0 or k=1.

Every block element is at least two. If an upper counter occurred in A,
its bound by `sum A=m+4`, together with erasure of `m+4`, would force it to
equal `m+3`. The rest of the block would then sum to one, impossible for
distinct available integers at least two. Thus A is entirely at most m.
If m were omitted, it would remain as a structurally permitted witness
strictly above every block element, contradicting `UpperOnly`. Removing m
therefore leaves an exact sum of four, and its only possible finite subset
is `{4}`. This yields precisely `{4,m}`.

The sum-four proof first bounds all entries by four and at least two, then
uses `decide +kernel` on the eight subsets of `{2,3,4}`. This is kernel
proof reduction, not `native_decide`. Mathematically, no two distinct
entries at least two can sum to four, since the smallest such pair is
`2+3=5`; the only singleton is `{4}`.

## Branch availability and second block

`forced_branch_available` uses `k≥2` exactly where needed: both opening
`m+4` and witness `m+3` belong to the original upper interval. The latter
survives deletion of the opening and `{4,m}`, and exceeds both members of
that block. At `m=6`, these counters are 10, 9, 4, and 6, with no collision.

The second support is exactly

```text
(support m k \ {m+4,4,m}).erase (m+3)
```

The identity used by the final theorem is the same as first erasing
`m+4`, deleting `{4,m}`, and then erasing `m+3`. It introduces no additional
deletion or forgotten counter.

Any exact B of sum `m+3` on this support can contain neither a remaining
upper counter (all are at least `m+5`) nor m. Therefore every member is at
most `m−1`. The counter `m−1` remains available: `m≥6` keeps it at least
five and distinct from the removed 4 and m. If B omitted it, it would be
a prohibited lower witness. The proof obtains this via a legitimate
weakening from cutoff `m+3` to `(m−1)+3=m+2`, then invokes the maximum
forcing helper with `m−1`.

Consequently `m−1∈B`, and the remaining block sum is
`(m+3)−(m−1)=4`. The sum-four lemma requires 4 to remain, contradicting
its explicit deletion. At the boundary `m=6`, the lower support is
`{2,3,5}` and any remaining upper counter is at least 11; the required
deficit is 9. In particular, the forced lower maximum 5 is present while
the required complement 4 is absent. No natural subtraction truncates
under the displayed bound.

The second-block impossibility also holds for arbitrary k. Only the final
claim that this is an available branch needs `k≥2`, and the code places
that requirement correctly.

## Build, dependency, and remaining-scope checks

The independent affected-target build succeeded after the parent's original
build finished. Lake replayed the current checked artifacts. The audit
collects transitive axioms of all four public statements and rejects any
nonstandard axiom. Each reports exactly
`[propext, Quot.sound, Classical.choice]`: no `sorryAx`, native trust,
custom axiom, or conjecture dependency occurs. The proof is combinatorial;
although it imports the exact-sum game module, it never invokes a losing
position to establish these conclusions. There is no circularity.

No new mathematical experiment, game computation, or bounded search was
performed by this reviewer. Kernel reduction of the small sum-four check
is part of the submitted proof. The earlier sharp complement-packing
claim is not formalized by these files and remains outside this candidate.

Reviewed SHA-256 snapshots:

- `UniformExactSumDescentObstruction.lean`:
  `046641bb3e351d7fdbc7844680f40ec3c4f0fc87f60fd74a76a6dfb956f00d7b`
- `UniformExactSumDescentAudit.lean`:
  `971b3045e34bc85377ecff3dd00cd3487f24e38610f73ff7423dd36c58457b9d`
