> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Full strategic closing: a terminal exclusion and a commutation obstruction

Notes-only focused round. F is NOT proved. No new game search, Lean edit,
or inference from a bounded table is made here. I inspected the saved full
witness results and processed their existing rows to identify the terminal
subcases; this is not a new solver job.

## Target F

S⊆[1,N] has at most h holes, 2h+1≤d≤N, and even effective total d+sumS.
B⊆S has sum d and contains the largest feasible member b of ANY exact-d
subset. There is w∈S\B with b<w<d such that opening w of the tied residual
S\B wins, equivalently V(C,w)=loss for C=S\(B∪{w}). Put t=d−w.
Maximality gives a true subsum gap t in S; in particular t≥1 and t∉S.

F asks for V(S\{w},t)≠loss. In a hypothetical counterexample both

    V(B∪C,t)=loss,       V(C,w)=loss

would hold. The sparse uniform even counterfamily proves that density cannot
be dropped. The old odd example proves parity cannot be dropped. Neither
obstruction settles this density-qualified implication.

## New arithmetic subcase elimination: residual cannot be terminal at N≥10

**Claim.** Under F's arithmetic hypotheses, if N≥10, then sumC≥w.
This claim does not require the residual's losing value, maximality beyond
the missing target t, or any general nonloss assertion.

### Proof

Let r=|S|. Since S⊆[1,N] and at most h counters are absent,

    r≥N−h,       2h+1≤N,       2r≥N+1.                    (1)

Define A by replacing the available counter w with the absent positive t:

    A=(S\{w})∪{t}.

Then A has exactly r distinct positive counters. It satisfies

    sumA = d+sumC+t.                                      (2)

Indeed S is the disjoint union of B,{w},C, so sumS=d+w+sumC;
removing w and inserting t yields (2).

Suppose sumC<w. By w+t=d, (2) gives

    sumA < d+w+t = 2d ≤ 2N.                              (3)

The least sum of r distinct positive integers is r(r+1)/2, so

    sumA ≥ r(r+1)/2.

For N≥12, (1) gives

    8 sumA ≥ (N+1)(N+3) > 16N,

where the strict inequality follows from
(N+1)(N+3)−16N=N(N−12)+3>0. This contradicts (3).

It remains to handle N10 or11. Equation (1) implies r≥6 and therefore
sumA≥21. Also

    sumS+d = sumA+2w,

so the effective-total evenness hypothesis implies even(sumA). Hence
sumA≥22, contradicting (3), since 2d≤2N≤22. This proves sumC≥w.

Thus at N≥10 the residual losing premise is necessarily a nonterminal
strategic loss, rather than an opening win caused simply by an uncatchable
remaining total. If sumC=w it would draw by `WholeTurn.sum_draw`; therefore
the losing premise further gives sumC>w. Finally the all-counters-one-turn
win test implies sumC≥w+maxC: if a last counter exceeded sumC−w, all other
counters could be taken while still behind, and that last counter would win.
This last step presumes the stated loss and nonempty C, already guaranteed.

### Scope and threshold diagnostic

The unconditional (no parity) replacement proof gives the uniform cutoff12.
Parity adds exactly the N10/11 cases. The cutoff10 cannot be lowered to9 for
this terminal-exclusion statement. A saved actual full witness is

    N9, S={2,3,4,6,8}, h4, d9,
    B={3,6}, b6, w8, t1, C={2,4}.

It has even effective total32, true gap1, global maximal exact member6, and
opening8 after B wins because sumC6<8. Thus it satisfies the full strategic
premise while its residual is terminal. It is NOT a counterexample to F:
the saved successor value is WIN.

The 95 saved full block witnesses contain seven terminal blocks at ambient
N5,6,7,9 (counts1,1,3,2), and none at N≥10. Remaining witness counts are
nonterminal: N9:2,N10:6,N11:14,N12:9,N13:20,N14:8,N15:19,N16:10.
These counts confirm the finite artifact's consistency with the arithmetic
proof but are not used as proof premises.

## Exact obstruction to a B-only strategy commutation

The second result explains why the known loss V(C,w) cannot simply be reused
by playing B in a different order from the low-gap position.

**Claim.** Start the ordinary post-opening game with support B∪C, acting
player P's score0 and opponent Q's score t>0. Suppose sumB=w+t, maxB<w,
and t is not a subsum of B. There is no legal play segment that consumes
exactly B, consumes no counter of C, and leaves support C at normalized
deficit w in EITHER orientation.

### Proof

Let A⊆B be the counters acquired by P in such a segment, and let α=sumA.
Q acquires B\A, total w+t−α. At the endpoint the fixed scores are

    P=α,       Q=t+(w+t−α)=w+2t−α,

so Q−P=w+2t−2α.

If P is behind by w, then α=t. This contradicts the subsum-gap hypothesis.

If Q is behind by w, then α=w+t=sumB. Positivity forces A=B and Q to have
acquired none of B. Since no C counter is consumed, Q has made no pick.
The rules allow no pass, so all B must have been consumed in P's initial
turn. That turn starts behind by t and has total w+t. Its final counter f
would have to satisfy

    sum(B\{f})=w+t−f<t,

hence f>w. This contradicts f≤maxB<w. This proves the claim.

The obstruction is not a failure of a proposed ordering: it excludes every
ordering and every ownership allocation using only B. It uses the actual
compulsory stopping rule and the true gap.

It does NOT imply that every valid defense for F must consume C. A defense
could reach a draw terminal or use a different deficit without ever returning
to (C,w). What fails is the direct black-box reuse of the GIVEN losing
position (C,w) by only reordering B. A simulation targeting that exact state
must involve additional C counters or a genuinely different strategy argument.

## Remaining mathematical obligation

After N≥10, a possible F counterexample must involve TWO nonterminal losses:
the low-gap position and the witnessed residual at deficit w. The terminal
shortcut is gone. The B-only commutation cannot connect them with the needed
orientation. A proof still needs a density-sensitive response using some
additional support geometry, or a new incompatibility theorem for these
two losses that respects all actual winning-opening/maximality premises.

Neither a response construction nor that incompatibility was proved in this
round. F, H and H3 remain open. The terminal-exclusion claim above is ready for
independent formalization if useful; the commutation claim is an exact scope
obstruction, not an impossibility theorem for all proof architectures.
