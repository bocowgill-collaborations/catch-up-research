> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Verified mechanism: fourth-from-top endpoint

Started 2026-09-29 before formalization; updated after strict Lean verification
and independent semantic review. The production module is
`scripts/catch_up/LowerRayFourthEndpoint.lean`.

Put m=N-5 and L=[2,m]. The tied residual after the exact-deficit response
to Q_N(N-3) is R=L union {m+3,m+4,m+5}.

Use the existing exact-sum loss obstruction at each node: from a losing
(S,d), any positive exact-sum block A forces a losing post-opening state
(S minus A minus {w},w) with w>max A. Thus every branch below is forced
by a theorem; no particular opponent strategy is presumed. An exact block
containing max S is an immediate contradiction.

For m>=11, all displayed elements are distinct and available. The m=10
exception is treated by an explicit completed turn below.

* Opening m+5: choose {2,m+3}; only w=m+4 survives the strict bound.
  Remaining support [3,m], deficit m+4, has dominating block {4,m}.
* Opening m+4: choose {4,m}; w is m+3 or m+5.
  * w=m+5: dominating block {2,m+3}.
  * w=m+3: choose {5,m-2}; w is m-1 or m+5.
    * w=m+5: remaining [2,m-1] minus {4,5,m-2}, with dominating
      block {6,m-1}, deficit m+5.
    * w=m-1: choose {2,m-3}; only w=m+5 remains above the block.
      Remaining [3,m-4] minus {4,5}, deficit m+5, has dominating
      block {3,6,m-4}. This last leaf needs m>=11.
* Opening m+3: choose {3,m}; w is m+4 or m+5.
  * w=m+5: choose {6,m-1}; only w=m+4 is possible.
    Remaining [2,m-2] minus {3,6}, deficit m+4, has dominating
    block {2,4,m-2}.
  * w=m+4: choose {5,m-1}; only w=m+5 is possible.
    Remaining [2,m-2] minus {3,5}, deficit m+5, has dominating
    block {7,m-2}.

At m=10, replace the branch w=m-1 in the middle-opening tree. Its position
is ({2,3,6,7,15},9). Choose 2, then 6 (total preparation 8<9), then 15.
The opponent receives ({3,7},14), which is terminal and losing since 10<14.
This completed-turn repair is proved with the repository's subset criterion.

The tree uses no parity or smaller-instance outcome hypothesis. It proves
Q_N(N-3) nonloss for every N>=15. In the requested even-total range below 15,
only N=11,12 remain. The first/middle top openings at these two sizes are
verified by four `decide +kernel` calls through the existing safety classifier;
the last opening is covered symbolically for all N>=11.

The inspected N11 interval certificate uses native evaluation, which was not
imported into this new proof's axiom closure. No new outcome table was generated.
The four small checks cover at most eight remaining counters each.

Target A remains open. Two alternative equal-sum blocks force winners in
different supports, so uniqueness alone cannot compare them. The finite tree
above instead restricts each forced winner by the current support's maximum
and closes every branch separately. No cross-support uniqueness is asserted.

## Why the natural common-support diamond does not close A

Suppose A and B are disjoint exact-deficit blocks of sum d, and a forced
winning opening w of S minus A lies outside A union B and has w>d. Put
H=S minus (A union B). Deleting B from the losing post-opening state gives
the normalized state (H minus {w}, w-d). If the initial state can catch,
every B-prefix is a legal continuing preparation because sum(B)=d<w.
If it cannot catch, the resulting state is also terminal and losing by
subtracting d from both the available sum and deficit.

This makes w a winning catching move in (H,d), not a winning opening in
the tied state (H,0). Two such winners therefore do not contradict tied
uniqueness. For example, ({6,7,8},3), with even effective total 24, has
three winning catches. Their children are ({7,8},3), ({6,8},4), and
({6,7},5), each losing: both available picks catch and leave a singleton
strictly exceeding its deficit, which is winning for the next mover.

This diagnosis was independently reviewed. It is a paper-level explanation,
not a new formal theorem. The example is not asserted to have the ancestry
or interval geometry of Target A. The full upper-opening claim is unresolved.
