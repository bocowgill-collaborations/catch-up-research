# Next unbounded obligation: root-specific upper reentry

Status: w7 branch CLOSED in RootUpperReentry.lean; w8 branch OPEN.
The original reductions below are retained as historical pencil reasoning;
only the explicitly identified compiled components may be treated as proved.
Pinned game semantics and versions remain those in CHECKPOINT.md.

Let N>=11, Even(T_N), and Q=([2,N]\{6},5). Goal:
V(Q)=LOSS implies some 9<=w<=N satisfies
V([2,N]\{5,6,w},w)=LOSS.

The existing exact-block argument with B={5} supplies a genuine winning
opening w of the tied residual, with w>=7. A child with w>=9 reenters the
four-hole density threshold. The unproved issue is exclusion of w7 and w8;
keep the full parent LOSS premise. Generic upper-density preservation is not
available. This lemma alone would not prove H or C.

For w7, let C={2,3,4} union [8,N]. Its actual shadow has V(C,7)=LOSS.
The parent pick7 gives the opponent state (insert5 C,2). Every opponent whole
turn is a singleton because every remaining label>=2. A turn avoiding5 cannot
have total7, since counter7 is absent. PairEntranceShadow then gives a winning
reply5 for the original mover. The only reserved-counter turn {5} leaves the
original mover at (C,3). Thus V(C,3)!=LOSS suffices to refute this winning
opponent endpoint. The required nonloss premise has not been proved.

For w8, let C={2,3,4,7} union [9,N]. Its actual shadow has V(C,8)=LOSS.
The opponent state is (insert5 C,3). Every legal whole turn is either a
singleton >=3 or starts2 then finishes with one other counter. No turn has
total8: counter8 and partner6 are absent. Every turn avoiding5 has the generic
winning reserve reply. The two reserve-taking turns are {5} and {2,5}; their
original-mover endpoints are (C,2) and (C.erase2,4). Proving both NONLOSS would
close this case. Tied/terminal cases and the whole-turn quantifiers still
need explicit Lean assembly; no favorable principal variation suffices.

The stronger possible anchor statements allow any even-sum tail T, with
min(T)>=8 for A and >=9 for B, instead of requiring an interval tail:
A: V({2,3,4} union T,7)!=LOSS;
B: V({2,3,4,7} union T,8)!=LOSS.
These are conjectures. The weaker conditional reflections assume these very
shadows LOSS and seek the smaller-deficit NONLOSS endpoints above.

Evidence: original tests exhausted A1024 even tails from[8,18] and B512 from
[9,18]; zero shadows LOSS, hence both reflections passed vacuously. A separate
held-out batch202 widely spaced supports also has zero shadow LOSS (A88DRAW/
13WIN,B20DRAW/81WIN). All505 direct held-out values independently replayed by
literal scores. Actual labels up to83; no interval table. This does not prove
any anchor theorem, reflection, or root statement, and no nonvacuous conditional
test has yet occurred. All receipts are search/root_reentry_reflection_*.

Next action: seek an unbounded legal defense for the interval anchor states or
a diagnostic obstruction to the proposed stronger anchor rule. Use the whole-
turn API and reserved-counter theorem; resolve reserve-taking explicitly.
Do not use more finite residual-cardinality cases as a substitute for this
unbounded obligation. Preserve a smallest diagnostic if a generalization fails.

## Current verified boundary and next action

DeficitCrossing and RootUpperReentry now compile the w7 reflection and its
actual-parent composition. Actual interval parent LOSS yields genuine residual
winning opening w>=8 for allN>=7. DeficitCrossingEntry uniformly proves the
w8/low2 entry restriction: only first3 can be safe, and safety is equivalent
to NONWIN at ({2,4,7} union [9,N],1). This last property is OPEN.
All builds/freshsource/standard-only transitive audits and independent reviews PASS.

Pencil (unformalized) reduction: let E={4,7} union T. C8LOSS gives E3LOSS
by below-prefix{2,3}. If (C.erase2,4) loses, continuing3 gives E1LOSS.
If (C,2) loses, its pick3 forces D=(C.erase3,1) WIN. High C8LOSS continuing3
also gives (C.erase3,5) LOSS. Applying the generic forced-entry theorem with
l1,a2 and absent equality3 forces D's winning move to be2, hence E1LOSS.
Thus excluding E1/E3 doubleLOSS (with interval tail, or retaining full actual
shadow/parent assumptions) suffices for both reserve endpoints. The remaining
whole-turn w8 assembly must still explicitly cover singleton and [2,x] turns.

Bounded257-tail test found no doubleLOSS, including10genuine E3LOSS cases;
all11cases with eitherLOSS independently literal-replayed. This is evidence,
not proof. The old named sparse control E={4,7,9,10,12,15} has E1LOSS,E3WIN,
C8WIN; do not strengthen to unconditional E1NONLOSS. Old assumed shifted-tail
package is recorded false at16..19, and supplies no usable theorem.

Next: prove the interval-specific w8 defense or find a diagnostic counterexample
to its strengthened two-anchor kernel. No new finite cardinality ladder/table.

## Resolution of the stronger kernel and current interval obstruction

The unqualified even-tail E1/E3 separation is FALSE, now kernel certified by
TwoAnchorDoubleLossObstruction.lean (explicit9-tailcounterexample,source+JSON
sharedDAG). C8is certifiedWIN there, so the fullshadow premise matters.
RootUpperEightFrontier.lean is complete: actualparentLOSS yields either
w>=9 or actualC8LOSS&E1LOSS&E3LOSS on intervaltail. No doubleLOSS exclusion
for intervaltail has been proved. The original pencil reduction is now compiled.

The simple first4strategy on actualE_N failsN12 (only7safe), although it
passesN11,15,16,19,20. All51opponentendpoints independentlyliteralchecked;
noNextension. Do not repair with unexplained sample exceptions. Next is a
consecutive-tail preservation mechanism or a diagnostic against a precise
interval-specific rule. The arbitrary-tail proof route is retired.
