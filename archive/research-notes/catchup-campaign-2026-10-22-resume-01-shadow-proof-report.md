> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.ConsecutiveGuardDescent](../../CatchUp/ConsecutiveGuardDescent.lean), [CatchUp.ConsecutiveGuardBoundary](../../CatchUp/ConsecutiveGuardBoundary.lean).

# Resumed shadow proof: checkpoint of current open kernel

Status: research active; no new Lean theorem or certified counterexample here.
Ownership: this directory only. Existing frozen results are unchanged.

## Fixed shadow route

For T labels >=9 of even sum, C={2,3,4,7} union T, E={4,7} union T,
H={7} union T. Retain literal C8 LOSS and E1 LOSS. Existing results give E3
LOSS, hence H1 and H3 WIN.

A common winning pick q at H1/H3 is impossible if q-2 remains: its two
LOSS children have deficits q-1 and q-3, and singleton q-2 is their legal
midpoint turn. For an actual consecutive tail, common winning picks can only
be 7 or 10. This alone does not force overlap of the two winning-choice sets.
Cross-pick comparison reaches compatible WIN/LOSS states, not a contradiction.
No simple restatement was formalized.

Shared pick7 forces T4 and T6 LOSS and K={4} union T at4 and6 WIN. The
attempted consequence T8 NONLOSS was RETRACTED: its proof incorrectly assumed
that every tied-root T is nonlosing. That assumption is not available and is
explicitly retired in the campaign. The only valid pencil consequence is
C8 LOSS => [T8 NONLOSS OR root(T) LOSS]. Every K4 tail pick loses if T8 loses,
using reserve4 shadowing, but the remaining pick4 can win when tied T loses.
This disjunction is not a compiled theorem and does not close the branch.

## Refuted unit-deficit guard (2026-10-22 18:14 UTC checkpoint)

The candidate min R=2 and Even(sum R+1) => V(R,1) != LOSS is FALSE.
Parent reports independent exact and literal evaluation of
R={2,4,7,13,15,19,35,36,50,57,60,99}, deficit1: LOSS, with sum397
and every one of its twelve first picks losing. Parent owns the resulting
artifact and any subsequent Lean certification. This is a counterexample to
the proposed invariant, NOT to the interval Catch-Up conjecture.

Counter2 acts as a role-swapping pass at deficit1. A strategy-stealing proof
must handle the opponent spending2 later while behind >=3. When that makes
the actual player catch with margin1, the real and simulated turn identities
can diverge into the same remaining support at deficit1, both current movers
LOSS. This is compatible because counter2 has disappeared. Thus the naive
one-board simulation is incomplete.

The proposed stronger insertion invariant is also FALSE:
  min C>=3, Even(sum C+d), V(C,d)=LOSS => V(insert2 C,d)!=WIN.
It remains false when restricted to d>=2. Two diagnostics are:

* T={9,16,17,18,26,28,31,37}: T at0 LOSS, T at2 LOSS, insert2T at2 WIN.
  This also refutes the proposed boundary implication T0LOSS => T2NONLOSS.
  Parent artifact: ../guard_insertion_tied_diagnostic.json.
* C={4,7,13,19,36,37,50,57,60,99} at14 LOSS. All ten first picks lose.
  Its child after13 is E={4,7,19,36,37,50,57,60,99} at1 LOSS, an existing
  Lean-certified endpoint. Inserting2 gives a WIN via continuing13 then2.
  Parent is certifying the C14 diagnostic separately. The same C14 example
  refutes the near-deficit proposal that containing d-1 guarantees NONLOSS.

Copying a smaller game's chosen winning move also fails. For
S=E union{13,15}, S1 WIN has unique winning first pick15, while insert2S at1
is DRAW with only13 safe; choosing15 loses by opponent continuation[13,2].
These root maps are independent exact/literal evidence in adaptive_fixed.jsonl
and adaptive_fixed_literal.json, not yet all kernel-certified here.

## Exact surviving scope, without an arbitrary exception repair

The actual interval applications coincide. Let
U(N,b)=(Icc 2 N) minus {b,b-2}, for 5<=b<=N.
From lower pair deletion ((Icc1N).erase1).erase b at deficit b-1, the
continuing pick b-2 reaches U(N,b) at1. From the original opening b, the
two continuing picks b-2,1 reach exactly the same U(N,b) at1. The parity
hypothesis is inherited from eligible N in both cases. For b=5, U lacks3;
for b>=6, U retains3. Thus simply adding a '3 remains' hypothesis would
discard a real needed boundary. No universal U theorem has been proved.

The original C8 route reaches B(T)={2,3,4} union T at1, T labels>=9 with
even sum, by continuing7. The new counterexample does not directly refute
this anchored family, nor C8 itself, nor joint C8LOSS/E1LOSS. It also does
not prove any of them. The strongest currently justified next question is
the original anchored C8 family or actual consecutive-tail subfamily.

Proposed targeted diagnostic (NOT RUN HERE): use the new witness's
T={13,15,19,35,36,50,57,60,99}, sum384, and replace low7 by3 to evaluate
B(T)1. Evaluate full C(T)8 and E(T)1 if the result discriminates the
remaining original route. This preserves a meaningful structural anchor
instead of adding unrelated exceptions to the refuted unit guard.
Parent assigned this diagnostic to a different worker; do not duplicate it.

## Existing interval reductions audited read-only

No uniform fixed-b5 result was found in the current package or pinned other
repository ref bb10b8246c8f7b99de084865826150459e5627f1. In addition to
searching literal b5 targets, the audit read the actual source of
LowerRayExactDeficit, LowerRaySuccessor, LowerRayInteriorReduction,
LowerRayEndpoints, LowerRayTransfer, and DenseHoleReduction. The existing
endpoint theorems concern b near N, not fixed b5. Conditional transfer
premises are explicitly unproved.

For 5<=b<=N, U(N,b) has exactly the three holes {1,b-2,b} relative to Icc1N,
deficit1, retained2, and even effective total when N is eligible. Hence the
entire family is already covered conditionally by the old open
DenseThreeHoleNonloss invariant. Its compiled reduction to the original
conjecture exists in the other repository; neither that theorem nor the
new unit-guard idea proves its hypothesis. Repackaging this implication
would add no strategic information.

Precise high-value obligation left after the guard failure:
for eligible N>=11 and consecutive T=Icc9N,
  V({2,3,4,7} union T,8)=LOSS => V({4,7} union T,1)!=LOSS.
RootUpperEightCriterion.interval_reserve_nonwin_iff_core_nonloss makes this
sufficient to close the actual opening8 branch. RootUpperEightFrontier's
interval_parent_loss_frontier still leaves genuine residual openings w>=9;
even solving this conditional branch would not settle all lower-ray cases
or the original conjecture. Arbitrary sparse-tail diagnostics should be
used to test candidate mechanisms, not silently replace the consecutive
tail obligation.

## Earlier UnitGuard formalization status (superseded below)

Parent briefly authorized a conditional UnitGuard reduction module. Work
stopped immediately when UnitGuard was refuted. No production Lean file was
created, no new theorem passed full source replay, and no false-premise
conditional theorem was added to the build. All owned LeanProbe sessions
were explicitly closed. The attempted helper was the valid generic idea
'a LOSS remains LOSS while continuing with a subset whose sum is below the
deficit'; this is already supplied by PairEntranceShadow.loss_after_subsum.
There is no reason to duplicate that infrastructure after the target failed.

The narrow previous-witness H1/H3 literal calculations are in
old_witness_h_controls.json. They are computational evidence on two saved
supports only, not a new population or uniform proof.

User deadline relayed by parent: full checkpoint and pause by
2026-10-22 20:15 UTC (4:15pm America/New_York), wind-down from20:05 UTC.
No external process, Lean session, or solver owned by this proof worker.

## 18:43 UTC — uniform actual-interval theorem compiled

New `CatchUp.ConsecutiveGuardDescent` gives a substantive restriction for
A_N={3,4} union Icc9N at deficit1. If q>=14 is a winning first pick, then
there is a genuine winning opening w>=q+4 of A_N minus{q-1,q}; consequently
q+4<=N. The top four available tail labels q>=14 therefore cannot win.
No parity or eligibility assumption is required.

The hard step proves NONWIN for a small-deficit reserve position by covering
EVERY completed opponent TurnSet. Preparation can only be empty or, at
deficit4, the singleton3. Two legal midpoint turns handle choices consuming
the reserve; the existing shadow/reserve theorem handles all choices avoiding
it. This excludes residual openings q+1,q+2,q+3 in one uniform argument.

Five public theorems and four supporting private lemmas are in the 10,092-byte
module. Fresh source replay, `lake --wfail build`, and all public theorem plus
reference-bridge axiom audits PASS; only propext, Classical.choice, Quot.sound.
No sorry, native_decide, external solver result, or unfinished conjecture
dependency. Verification took 5.934s + 6.838s + 4.389s; cumulative child peak
RSS 5.523GB. Lean4.27.0 and pinned Mathlib unchanged. Complete commands/hashes
in `descent-verification.json`; rerun `verify_descent.py` from this directory
or with its full path. See `consecutive-descent.md` for the argument and scope.

The theorem does NOT promote w back into a winning move of original A_N,
does NOT establish A_N NONWIN, and does NOT prove C or a counterexample to C.
The exact next barrier is w=q+4: opponent turn [3,w-3] reaches equality with
the high shadow and defeats the fixed reserve reply. At q14,w18 this is
[3,15]. An adaptive second reply is needed before any stronger exclusion.
The separate change-of-support issue must be solved before claiming descent.

All proof construction sessions and verification processes are closed.
Independent generic source review PASS; specialization review requested.
No cryptid work or new numerical population search occurred in this round.
