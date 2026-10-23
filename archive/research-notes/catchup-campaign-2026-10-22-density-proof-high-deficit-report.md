> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# High-deficit nonloss: exact obstruction and a conditional top boundary

Notes-only reasoning round. No new computation, Lean edit, or C result.
The high-deficit claim and stronger margin claim remain OPEN.

## Target and tested evidence

The proposed H is: S⊆[1,N], h=|[1,N]\S|, 2h+1≤d≤N and even(d+sumS)
imply V(S,d)≠loss. The parent's complete N24 table test covered31,971,581
even cases with no loss. All44 observed odd losses have d−2h equal1 or2.
Consequently the stronger parity-free margin hypothesis d≥2h+3 survives the
same test. Neither assertion follows from that finite evidence.

I followed the existing maximal-exact-block dichotomy, concentrating on its
small gap branch. No alternative strategy portfolio or larger table was used.

## The failed parity closing step

The new kernel gives, from a hypothetical H loss, either a higher-deficit loss
after deleting a bounded exact block, or

    w=d−t∈S,   1≤t<h,
    t is not any subsum of S,
    V(S\{w},t)=loss.

The second transition is one compulsory continuing pick, so

    t+sum(S\{w}) = d+sum(S)−2w.

Thus effective-total parity is PRESERVED. Evenness gives another even losing
state, not an arithmetic contradiction. Evenness plus a true subset-sum gap
alone does not imply nonloss: the previously kernel-certified state

    R={3,7,9,14,17,20,29,34},  t=1

is losing, has no subsum1, and has even effective total134. Its sparse density
violates H; it is a diagnostic against dropping the global ancestor conditions,
not a counterexample to H.

The lower branch retains additional geometric information. With R=S\{w},
R is missing BOTH w and w+t=d: if d were originally available, the singleton
exact block {d} would have maximum d, prohibiting the maximal-block witness
w<d. Also

    2h+1−t≤w,       w+t≤N,       |[1,N]\R|≤h+1.

A valid gap-branch proof must exploit these ancestor constraints (or something
stronger from maximality), not only t's nonrepresentability and parity.

### Smallest saved lower-branch diagnostic

The existing `subsum_gap_results.json` includes the odd losing H state

    N7, h3, d7, S={2,3,5,6}.

All four first moves lose. Its exact block {2,5} has witness w6 and leaves the
same player's loss at ({2,3,5},1);1 is unrepresentable. Effective total23 is odd.
The nearby even support {2,4,5,6} has the same N/h/d and missing1,d, but taking6
continues to ({2,4,5},1), which draws. At that three-counter state only pick2
draws; picks4 and5 lose:

- pick2 leaves the opponent ({4,5},1), a draw;
- pick4 leaves the opponent ({2,5},3), which wins by2 then5;
- pick5 leaves the opponent ({2,4},4), which wins by2 then4.

An initially considered gap formula for {2,5} was outside the imported pair
classification's gap≤lower hypothesis; that application was rejected. The
explicit legal two-pick witness above is the corrected calculation.

This pair shows the intended parity distinction locally, but supplies no
uniform response rule. The exact unresolved implication is nonloss for the
even low-gap successor under its retained high missing-pair constraints, OR a
different legal move in the ancestor. Proving just the successor nonloss could
be stronger than H and needs its own falsification test before adoption.

## A concrete conditional boundary reduction

There is a useful unbounded implication at ambient top d, with at most two
holes. It is a mathematical derivation from already checked kernels, not yet a
new compiled theorem in this notes-only workstream.

**Claim.** For d≥5, suppose CatchUp.value([1,d−2])≠win. Then every S⊆[1,d]
with at most two holes satisfies V(S,d)≠loss.

This needs no parity assumption. When d+sumS is even in the exceptional family
below, the smaller interval has even total, so its no-win premise is implied
by the smaller instance of C.

### Proof

1. If d∈S, then d is an available maximum. The existing exact-sum dominating
   block theorem applied to {d} gives nonloss.

2. If1∈S, apply `DenseLossGeneral.exact_deficit_nonloss_of_low_subsums` with
   h2, ambient endpoint d and deficit d. Its threshold5≤d holds. The only
   positive required target below2 is1, represented by {1}. This gives nonloss.

3. Otherwise both1 and d are absent. They are distinct since d≥5, and all
   counters of [1,d] other than these two must remain: an additional hole would
   contradict the budget. Thus S=[2,d−1]. Assume V(S,d)=loss.

4. Apply `DenseLossGeneral.loss_dichotomy` with N=d,h2. Its upper branch
   would give w∈S with w>d, impossible since S⊆[1,d]. Its lower branch gives
   an integer1≤t<2, hence t=1, with

       V(S\{d−1},1)=loss.

   Because S=[2,d−1], this is V([2,d−2],1)=loss.

5. The last state is exactly the normalized state after opening1 from
   [1,d−2]. The interval is nonempty and contains1 because d≥5. A losing
   post-opening state means opening1 wins for the original first player;
   hence CatchUp.value([1,d−2])=win. This contradicts the premise.

This proves the claim. In particular, the exceptional two-hole top family
cannot be a loss unless a STRICTLY SMALLER genuine initial interval is a
first-player win. This is a real size descent rather than merely growing holes.

For the parity statement, in that exceptional family

    d+sum[2,d−1] = sum[1,d]−1.

If this is even, sum[1,d] is odd. The difference between triangular totals at
d and d−2 is2d−1, which is odd. Thus sum[1,d−2] is even. Consequently the
smaller root premise is an eligible instance of the original C.

## Exact scope and next mathematical obligation

The conditional claim covers only the top-deficit boundary with at most two
holes. It does not prove H for arbitrary N>d or arbitrary h, and it does not
settle C by induction alone. Old-repo duplication should be checked before
any formalization. A natural precise next use is a simultaneous no-first-win
induction that can actually reach this top boundary while controlling the
other upper/gap successors; that controlling implication is not supplied here.

The margin≥3 observation suggests extra complementary exact pairs, but I
found no valid route from their existence to safety. Two or more disjoint
exact blocks do not by themselves contradict loss; upper residual winners can
coincide. No claim that the margin conjecture is proved is made.
