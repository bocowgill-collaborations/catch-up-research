> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseBlockMass](../../CatchUp/DenseBlockMass.lean).

# Dense exact-block mass bounds small residuals by finite ambient intervals

Informal statement: Let S⊆[1,N], h=|[1,N]\S| and2h+1≤d≤N. Let B⊆S
have sumd, choose b∈B with d−h≤b, and let w∈S\B. Put k=|B| and
c=|(S\B)\{w}|. Then

    k(k−1)≤2h,
    N=h+k+c+1,   h≤k+c,
    k²≤3k+2c.

Consequently c≤4 implies k≤4 and N≤2c+9. The explicit cutoffs are:

| Residual bound | Block bound | Ambient bound |
|---|---|---|
| c≤4 | k≤4 | N≤17 |
| c≤3 | k≤4 | N≤15 |
| c≤2 | k≤4 | N≤13 |
| c≤1 | k≤3 | N≤9 |

These are upper bounds, not optimality claims. The assumptions require no
outcome, parity, winning opening, or global maximality. A strategic application
must separately supply the near-deficit block member. The module does not
prove that the relevant residual is safe or that every branch has c≤4.

## Exact Lean statements

```lean
theorem block_residual_mass_bound
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (hB : B ⊆ S) (hsum : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hnear : d - (Icc 1 N \ S).card ≤ b) (hw : w ∈ S \ B) :
    B.card * B.card ≤ 3 * B.card + 2 * ((S \ B).erase w).card
```

```lean

```

The authoritative file is `CatchUp/DenseBlockMass.lean`. It reuses
`DenseTerminalReduction.interval_subset_sum_lower`; no duplicate triangular
sum proof was introduced. The original task's residual C is represented
literally by `(S \ B).erase w`, including the removal of w exactly once.
No manuscript/paper was edited.

## Proof

Erase b fromB. Its sum is d−b≤h and its cardinality is k−1. Distinct positive
integers have triangular minimum sum, so k(k−1)≤2h. Cardinality partitions
[1,N] into holes, block, openingw and residual, giving N=h+k+c+1. Density
therefore gives h≤k+c, and expanding k(k−1)+k=k² yields the quadratic bound.
For c≤4, any k≥5 makes k²>3k+8, a contradiction. For c≤1, k≥4 is impossible.
Substitute the resulting k bounds into the partition to obtain all four
ambient cutoffs. These arguments are uniform Nat arithmetic, not bounded tests.

## Checks and reproduction

From `research/catchup`:

```
lake --wfail build CatchUp.DenseBlockMass
lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/block-mass/audit.lean
lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/block-mass/lean/Main.lean
```

All passed. Build6.031seconds;6public transitive axiom audits4.332seconds;
import shim4.257seconds. Audits include the2new private arithmetic lemmas and
contain only propext,Classical.choice,Quot.sound. Source scan found no live
placeholder proof token. No native evaluation, external solver assumption,
custom axiom, or unfinished conjecture is used.

Lean4.27.0 and mathliba3a10db0e9d66acbebf76c5e6a135066525ac900 were checked
and preserved. PlatformmacOS26.6.2arm64; no more specific CPU model is claimed.
Darwin cumulative child peakRSS across the command sequence5,477,957,632bytes
is recorded, not interpreted as isolated per-theorem memory. Proof generation
was interactive and not separately instrumented; no computational search ran.

New source5689bytes/128lines,6public+2private theorems,SHA256
`c742f8463cbb01631fde5a45a1693e5e5f1e4c15388dff6555ac51e1426bf140`.
`dependencies.json` records the5local source import files,96280bytes total,
of which90591bytes are existing support. Mathlib is pinned separately and
excluded from that local byte count. This is source accounting, not serialized
kernel proof size or a minimality claim. `checks.json` records commands and
hashes, including preservation of the earlier3gap-obstruction modules.

The lean/ directory supplies the required pinned path-dependency wrapper and
import shim; the existing downstream package is the authoritative build.
Parent independent replay/review remains pending. The highest-value next use
is to instantiate this bound at the selected maximal block and certify the
full strategic gap implication for c≤4,N≤17, while retaining every opponent
reply. Cases with more residual counters remain unbounded by these cutoffs.
