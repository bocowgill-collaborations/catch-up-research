> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.ExactSumLossObstruction](../../CatchUp/ExactSumLossObstruction.lean).

# Arbitrary-hole exact-deficit dichotomy

Status: complete mathematical derivation; parent-owned Lean migration/checking
is separate. C and the dense nonloss invariant remain open. No game experiment
or Lean source was run/edited in this workstream.

No `co-math-config.json`, workstream instructions/status/log, or manuscript was
present in the assigned tree. This report uses strict justification throughout;
no manuscript or old approved source is changed. Applicable proof/research
skills were read. The only output is this owned notes directory.

## Precise setup and provenance

Write `V(S,d)` for the reference normalized current-player value. Counters in
`S` are positive distinct natural numbers. Let `I=[1,N]`, `S ⊆ I`, and
`holes=I\S`. Let `h,d,N` be natural numbers, with

    |holes| ≤ h,       2h+1 ≤ d ≤ N,       V(S,d)=loss.

No even-effective-total assumption is required for the result below.

The semantic lemma reused is
`Position.exists_winning_opening_gt_max_of_loss_of_exact_sum`, in
`scripts/catch_up/ExactSumLossObstruction.lean` at pinned other-repo commit
`bb10b8246c8f7b99de084865826150459e5627f1`. Its hypotheses are: nonempty positive
`B ⊆ S`, sum(B)=d, and V(S,d)=loss. Its conclusion supplies

    w ∈ S\B,   V((S\B)\{w},w)=loss,   max(B)<w.              (E)

The old source proof was inspected, including the block exchange argument
giving the strict final inequality. Its theorem in this report is a dependency,
not an external solver answer or an axiom. It has not been freshly rebuilt by
this notes-only workstream. The parent is arranging its kernel-checked reuse.

The `h=3` priority/exchange statements already exist in `DenseLossInjection.lean`.
The contribution here is the variable-hole statement and exact cost/scope.
The raw growing-hole induction is retired by the old campaign ledger:338–347;
this theorem does not revive it without a new closure argument.

## Theorem 1: a small exact block or a missing small deficit

Under the setup above, at least one of the following holds.

**Upper branch.** There are a nonempty set B and w such that

    B ⊆ S,  |B|≤2,  sum(B)=d,
    w∈S\B,  d<w≤N,  V((S\B)\{w},w)=loss.

**Lower branch.** There is t such that

    1≤t<h,  t∉S,  d−t∈S,
    V(S\{d−t},t)=loss.

The upper branch deletes at most three counters. It is an exact catching turn
B followed by the opponent's witnessing opening w. The lower branch is one
compulsory continuing pick by the current player; the perspective is preserved.

### Proof

1. **Handle an available target counter.** If d∈S, use B={d} in (E). The block
   is nonempty, positive since d≥1, exact, and has cardinality1. Its maximum is
   d, so (E) gives w>d. Since w∈S⊆I, w≤N. This is the upper branch.

2. **Find an intact complementary pair when d is missing.** Suppose d∉S. For
   each i∈{1,…,h}, consider the pair P_i={i,d−i}. Each pair lies in I: i≥1,
   i≤h<d≤N, and 1≤d−i≤N. Also i≤h and d−i≥h+1, by d≥2h+1. The pairs are
   pairwise disjoint: low members are distinct, high members are distinct by
   cancellation in d−i, and low/high members lie on opposite sides of h.
   None contains d, since i≥1 and i<d.

   If every pair were blocked, choose one missing member from each. Their
   disjointness gives h distinct holes, all distinct from the further hole d.
   That would imply |holes|≥h+1, contrary to |holes|≤h. Thus at least one pair
   is intact. This argument also handles h=0: there would be the hole d but no
   permitted holes, a contradiction, so the missing-target case cannot arise.

3. **Choose the first intact pair.** Let i be the least index in [1,h] with
   both i and d−i in S. Put B=P_i. Since i≤h<d−i, B has two members, positive
   total i+(d−i)=d, and maximum d−i. Apply (E) to obtain w∈S\B with
   w>d−i and V((S\B)\{w},w)=loss.

4. **Separate the upper and lower branches.** If w>d, the upper branch holds.
   Otherwise w≤d. Equality w=d is impossible because w∈S and d∉S. Hence
   w<d. Define t=d−w. It is positive. The inequality w>d−i gives t<i≤h,
   so 1≤t<h. We also have w=d−t∈S.

5. **Prove that the small deficit is missing.** If t∈S, the pair
   {t,d−t}={t,w} is intact. Its index satisfies 1≤t<i, contradicting the
   minimality of i. Therefore t∉S.

6. **Check the continuing-pick semantics.** The exact block B⊆S shows
   sum(S)≥d, so the starting state is catchable and nonempty. From a losing
   nonterminal state, every legal first move has losing move outcome; this is
   the `best` characterization of loss under win>draw>loss. Since w∈S and
   w<d, its move is a same-player continuation with state (S\{w},d−w).
   Its value is therefore loss without negation. Substitute w=d−t and d−w=t
   to obtain the lower branch. This completes the proof.

## A stronger optional variant: a true subset-sum gap

The upper-branch deletion cost can be traded for a stronger lower conclusion.
Under the same setup, choose B among **all** exact-d subsets of S to maximize
max(B). Such sets form a nonempty finite family by steps1–2 above. Write b=max(B).
The available singleton or complementary pair has maximum at least d−h, so

    b≥d−h,       sum(B\{b})=d−b≤h.                          (1)

Then either:

- (Upper) (E) yields w>d and a new loss after deleting B and w, with
  |B|≤h+1 and hence at most h+2 deletions; or
- (Gap) there is 1≤t<h, with d−t∈S and V(S\{d−t},t)=loss, and **no subset
  A⊆S has sum(A)=t**.

### Proof of the additional claims

Each member of B\{b} is at least1, so its cardinality is at most its sum≤h;
thus |B|≤h+1. Apply (E): w>b≥d−h. If w≤d, equality w=d is impossible:
it would put the singleton {d} among the exact-d sets, forcing b≥d and then
w>b≥d. Therefore w<d. Set t=d−w. As before 1≤t<h and the continuing successor
is a loss.

To prove the gap, suppose A⊆S has sum(A)=t. From d≥2h+1 and w>d−h we obtain
w≥h+2, while t≤h−1, so w>t. If w∈A, positivity would imply w≤sum(A)=t,
a contradiction. Thus w∉A, and A∪{w} is a subset of S with total t+w=d.
Its maximum is at least w>b, contradicting the defining maximality of b.
Consequently no such subset A exists.

For example, if the subsums of S cover every target1,…,h−1, only the upper
branch of this stronger variant remains. This does not yield a scalar ascent
proof: removal of B and w need not preserve that subsum condition or density.

## Edge cases and hostile checks

- h=0 and h=1 have no lower branch because no integer satisfies1≤t<h.
  Target availability/first-pair counting force the upper branch.
- No pair repeats its middle element: d≥2h+1 gives i<d−i for every i≤h.
- The extra hole d is distinct from all selected pair holes.
- The conclusion is about current-player loss; a continuing move does not
  negate. An exact block catches at equality, after which roles swap; the next
  witnessing opening swaps them again. These are the actual turn rules.
- No arbitrary tied-game nonloss premise is used; that premise is false.
- The threshold2h+1 is needed for the disjoint-pair argument. At d=2h,
  the pair indexed h repeats its element and is not a two-counter exact block.
- Evenness is unnecessary. If imposed by the density campaign, it is preserved
  along these legal transitions, but it supplies no additional closure here.
- At saturated density h=floor(N/3), the result addresses the high-deficit
  range d≥2h+1. It does not cover the entire dense boundary.

## Exact remaining obstruction

The theorem replaces a hypothetical high-deficit loss by either a strict higher
deficit with up to three extra holes, or a small missing-deficit loss after one
extra hole. It does not keep `3*holes≤N` invariant, and no recursive defense is
constructed. The stronger subset-sum-gap variant improves the description of
the lower branch but can delete up to h+2 counters in its upper branch.

Thus the outstanding implication is still a contradiction for these resulting
states **without uncontrolled hole growth**. No C proof, counterexample to C,
general proof-size lower bound, or new certified finite outcome is claimed.
