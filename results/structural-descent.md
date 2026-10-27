# Structural descent and conditional interval closure

Four archived modules are now maintained, source-preserving Lean ports, adding
18 public theorem declarations. They provide arithmetic descent, a forced-loss
classification, endpoint rigidity and a conditional closure theorem. **They do
not solve Catch-Up.** See [provenance and checking](../verification/structural-ports.md).

## Effective total: a rank, not a strategic invariant

Write `E(S,d)=d+sum(S)`. If `A ⊆ S`, `sum(A)=d`, and `w ∈ S\A`, then

```text
E((S\A)\{w},w) + 2d = E(S,d).
```

[EffectiveTotalDescent](../CatchUp/EffectiveTotalDescent.lean) proves this
subtraction-free identity, the exact natural-subtraction form, and strict
decrease when `d>0`. It also proves that the residual child is catchable exactly
when `2d+2w ≤ E(S,d)`. A catchable child with `w>d` therefore requires
`4d+2 ≤ E(S,d)`.

These are arithmetic statements about exact blocks. They do not assert that an
arbitrary ordering of a block is a legal turn, that a particular game outcome
is preserved, or that a smaller child satisfies the parent's geometric
hypotheses. In particular, the child can have more holes in the same ambient
interval. A decreasing rank alone does not close an induction.

## Three-hole losses: retain the non-increasing alternatives

Let `S ⊆ I_N={1,…,N}`, `7≤d≤N`, and suppose `I_N\S` has at most three elements.
[DenseLossInjection](../CatchUp/DenseLossInjection.lean) first proves a purely
combinatorial priority rule: `d` is available, or one of
`{1,d−1}`, `{2,d−2}`, `{3,d−3}` is available. At `d≥7`, the three pairs are
disjoint, so blocking all of them while also omitting `d` needs four holes.
The priority version records the failures of earlier alternatives.

If `Position(S,d)` loses, the existing exact-sum obstruction then supplies a
nonempty block `A`, with at most two counters and total `d`, and an opening
`w>max(A)` in the tied residual `S\A` such that
`value(afterOpening(S\A,w))=loss`. This means that **opening w wins for its
opener**; the post-opening value is relative to the next mover. The witness
satisfies `d−2≤w≤N` and `w≠d`, but need not satisfy `w>d`.

The final classification is an upper witness `w>d`, or one of these exact
continuing-pick loss descendants:

| Parent omissions/presences | Descendant certified losing |
| --- | --- |
| `d,1` absent; `d−1` present | `Position(S\{d−1},1)` |
| `d,1,2` absent; `d−2` present | `Position(S\{d−2},2)` |
| `d,2,d−1` absent; `1,d−2` present | `Position(S\{d−2,1},1)` |

The third case checks that the deficit-two intermediate state is catchable
before taking one. Both picks are below their then-current deficits, so the
same mover continues. This is not a uniqueness comparison across different
tied residuals, an injective map between all losing states, or an exclusion of
all dense losses.

## Prefix endpoints: exact shapes and both parity hypotheses

[PrefixBlockedDenseEndpoints](../CatchUp/PrefixBlockedDenseEndpoints.lean)
retains the same subset, three-hole and `7≤d≤N` hypotheses. Three known missing
counters exhaust the parent's hole budget. The module proves exact child
shapes and the following restrictions when the ambient interval total is even:

- If the parent omits `1,2,d`, its effective total is odd. Hence this alternative
  is impossible **if the parent effective total is also even**.
- In the first deficit-one case, if the parent effective total is even, there
  is a third, odd missing counter `h`, distinct from `1,d`, and the child is
  `Position([2,N]\{d−1,d,h},1)`.
- In the third case, even parent effective total forces `d` odd, and the child
  is `Position([3,N]\{d−2,d−1,d},1)`.

The combined theorem `even_dense_loss_forces_upper_or_odd_prefix_endpoint`
leaves an upper exact-block witness or a losing member of one of these two
odd-parameter deficit-one families. Both parity assumptions are explicit;
neither endpoint family is proved nonlosing here. Their shapes and their loss
hypotheses remain part of the proof obligations.

## Lower ray: a conditional route with four boundary candidates

Define `R_{N,b}=I_N\{1,b−1,b}`, using the existing
`lowerRayExactDeficitResidual`. An available `y` missing either adjacent neighbor
must lie in

```text
{2,b−2,b+1,N} ∩ R_{N,b}.
```

[LowerRayInteriorReduction](../CatchUp/LowerRayInteriorReduction.lean) proves
this geometry and defines `LowerRayInteriorDeficitOneNonloss N b`: for every
available `y` whose two neighbors are available, the left-neighbor deletion
`Position(R_{N,b}\{y−1,y},1)` is nonlosing. The existing neighbor-jump theorem
forces exactly such a loss if opening `y` wins. Thus the interior hypothesis,
together with nonloss after each available boundary opening, makes the tied
residual nonwinning. Candidates may coincide or be unavailable; the formal
boundary quantifier handles both cases.

For `N≥7`, the combined theorem `value_Icc_eq_draw_of_lower_ray_interior_and_boundary`
proves `value(I_N)=draw` **assuming** first-pair draw at
`pairDeletionPosition N 1 2`, all interior nonloss conditions for `3≤b≤N`, and
all corresponding available boundary-opening checks. The closure theorem
itself has no parity premise. Applying it uniformly to the conjecture still
requires proving those hypotheses on every eligible interval, and handling
smaller N separately. First-pair nonloss is not a substitute for first-pair draw.

## What the batch changes, and what it does not

The maintained API now exposes a precise scalar rank, all small-deficit
alternatives in the three-hole loss argument, canonical parity-constrained
endpoints, and the interior/boundary closure contract. These are reusable proof
tools, not a new proof that the contracts can always be met.

The three-hole theorems do not directly settle the interior predicate: its
left-neighbor-deletion supports have five holes in `I_N`. An exact-block step
can also increase the number of holes. A future proof needs an explicitly
closed family or a proved transfer restoring the needed geometry, plus the
remaining endpoint and first-pair obligations. No such missing statement is
silently assumed in the ports. See the [handoff](../docs/research-handoff.md),
[routes](research-routes.md), and [open questions](open-questions.md).
