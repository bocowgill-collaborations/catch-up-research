> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.GapSuccessorObstruction](../../CatchUp/GapSuccessorObstruction.lean).

# Maximal-block gap preservation has a dense even counterexample

Informal statement: The even dense position S={4,5,8,9,10,11,12} at deficit13
has exactly6holes in[1,13] and satisfies2h+1=d. Its exact13blocks are precisely
{4,9} and{5,8}, so their largest possible member is9. The small target3 is
not a subset sum. Nevertheless the legal continuing pick10=d-3, above that
maximal block bound, leaves a LOSS at deficit3 with remaining
{4,5,8,9,11,12}. Every one of that successor's six legal picks loses.
The ancestor itself WINS, so this refutes the proposed unconditional gap
preservation step, NOT C and NOT dense high-deficit nonloss H.

The exact combined Lean theorem statement is:

```lean
theorem dense_even_maximal_gap_counterexample :
    support ⊆ Icc 1 13 ∧ (Icc 1 13 \ support).card = 6 ∧
    2 * 6 + 1 ≤ (13 : ℕ) ∧ Even (support.sum id + 13) ∧
    1 ≤ (3 : ℕ) ∧ 3 < (6 : ℕ) ∧ 13 - 3 = (10 : ℕ) ∧
    10 ∈ support ∧ 13 ∉ support ∧ 10 < (13 : ℕ) ∧
    (∀ B : Finset ℕ, B ⊆ support → B.sum id = 13 → B ⊆ Icc 1 9) ∧
    (({4, 9} : Finset ℕ) ⊆ support ∧ ({4, 9} : Finset ℕ).sum id = 13 ∧
      9 ∈ ({4, 9} : Finset ℕ) ∧ 9 < (10 : ℕ)) ∧
    (∀ B : Finset ℕ, B ⊆ support → B.sum id ≠ 3) ∧
    (⟨support, 13⟩ : Position).afterPick 10 = ⟨residual, 3⟩ ∧
    ((⟨support, 13⟩ : Position).afterPick 10).value = .loss ∧
    (⟨support, 13⟩ : Position).value = .win
```

`every_residual_pick_loses` additionally universally quantifies over each
legal residual pick. `exact_blocks` computes the complete finite collection,
not one chosen block. The target is defined in
`research/catchup/CatchUp/GapSuccessorObstruction.lean`; no paper was edited.

## Verification

Lean4.27.0, mathlib commit a3a10db0e9d66acbebf76c5e6a135066525ac900,
unchanged from the downstream package. From `research/catchup`:

```
lake --wfail build CatchUp.GapSuccessorObstruction
lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/gap-obstruction/audit.lean
lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/gap-obstruction/lean/Main.lean
```

All passed. Build5.685seconds, thirteen transitive axiom audits3.915seconds,
shim import3.700seconds. Every audit uses only propext, Classical.choice,
Quot.sound (one needs only two). No unfinished conjecture, custom axiom,
native proof evaluation, or external solver answer occurs in the proof.
Closed arithmetic, exact-block enumeration and executable values use
`decide +kernel`; `Position.eval_eq_value` connects computation to the reference.
There is no live placeholder proof; source scan found no `sorry` token.

`checks.json` records SHA256, byte count, command strings, elapsed times and
cumulative child peakRSS as reported by Darwin (5,562,777,600bytes across the
build/audit/shim command sequence; this is not isolated per-theorem memory).
Source4381bytes,13theorems,SHA256
`d36f798a130a29fb7e86f5200514752da7081343c5e8fc209f2ceed253862b8e`.
The imported reference/evaluator/exact-block proof support is existing work;
4381bytes is the new source cost, not a bound on the complete dependency proof.
No standalone certificate serialization or proof-size minimality is claimed.

The requested lean/ folder provides a pinned toolchain, path-dependency
lakefile and import shim. The existing downstream package is the authoritative
build target; no alternate mathlib/toolchain was installed or updated.

## Scope

The result says the displayed ancestor conditions alone do not force a safe gap
successor. It does not show failure of the loss dichotomy: that theorem also
assumes the ancestor itself loses, whereas this ancestor wins. A valid H proof
could still exploit the loss assumption to select a different move. It rules
out treating the gap branch as automatically safe from arithmetic and maximality.
Search discovery/minimality and independent literal-score replay belong to the
parent's search workstream; no least-counterexample claim is formalized here.

## Independent review clarification: geometric relaxation only

The N13 example does **not** satisfy the residual winning-opening premise
produced inside `DenseLossSubsumGap.loss_dichotomy`'s proof. For both exact
blocks B={4,9} and B={5,8}, the independently reviewed value is

    (afterOpening (support \ B) 10).value = WIN.

Consequently10 is a LOSING opening of each tied residual, whereas the actual
strategic derivation requires a WINNING residual opening, namely an
`afterOpening` value of LOSS. The compiled theorem asserts geometry,
maximality, arithmetic, and the unsafe direct continuing pick; it does not
assert that missing strategic premise. Therefore this certificate refutes
only the geometric relaxation of the proposed closing lemma. It does **not**
refute a closing lemma retaining the residual winning-opening hypothesis.
These two residual values were supplied by the parent's independent review
and are explanatory notes, not additional declarations in this stable module.
The parent search is checking the full strategic premise separately.
