# Strategy transfers and couplings

This guide connects earlier transfer methods to the current library and archive. The Catch-Up conjecture remains
open. Before using an archived claim, inspect its evidence label and exact
statement in the [earlier finding ledger](legacy-findings.md).

## Which player and which obligation?

A fixed protected player keeps the same identity when the mover switches.
Normalized position values are relative to the current mover. A pick strictly
below the deficit continues that turn; a pick equal to or above it switches
players. A transfer proof must reconcile these two viewpoints explicitly.

One drawn opening suffices for a tied-root draw by the existing draw-opening
criterion, but a proposed N→N+4 transfer must still prove the needed safety for
both protected players at the same specified opening. A root draw does not by
itself identify opening one as drawn. See CU-L004, CU-L009 and CU-L021.

## Four-counter simulations

The earlier work records small/large states, new counters, persistent ownership
differences and ghost moves. General simulation soundness is useful once its
relation is instantiated and closed under every actual opponent transition.
Neither a bookkeeping identity nor a favorable product path supplies that
closure. See CU-L016–CU-L020 and the current earlier-work guide.

## Completed margins and score debt

At early termination, notionally giving every remaining counter to the trailing
player preserves the winner. Signed ownership entries then telescope to a
completed protected-player margin. Under the stated even-total hypotheses, a
two-point comparison with a winning shadow can imply actual nonloss.

This comparison is a sufficient terminal certificate. The causal strategy and
ability to secure any promised repayment remain separate obligations. A local
parametric terminal repair is retained in the earlier library; a two-pick repair
handles another specific reached branch. See CU-L024–CU-L027.

## The finite adjacent-hole controller

The archived mandatory instance uses

```text
actual: ({2,5,6,9,10,11}, deficit 1, p1)
shadow: ({2,5,6,7,10,11}, deficit 1, p1).
```

The controller chooses which game advances before observing an adversarial
choice. It must cover every actual-opponent pick and every strict-win-preserving
reply of the supplied shadow strategy, keep at most two unmatched remaining
counters per side after each atomic pick, and finish both games with
`completedMargin(actual) ≥ completedMargin(shadow)−2`.

CU-L026 records a completed finite controller in that exact language. The
[supported replay bundle](../computation/experiments/earlier-campaign/two-buffer/)
checks its 87 nodes and 17 terminal histories against the retained full record.
It covers all five actual second picks and both branches after `[2,11]`. The
archived Lean protocol proof remains separate from this computational replay;
an unbounded translator is still open.

## Failures that constrain a new transfer

- The natural adjacent-hole counter correspondence can copy every nonlosing
  shadow move to a losing actual move. Repair is needed before an exceptional
  counter is necessarily selected (CU-L022).
- A reserved counter three and common-counter copying can fail when equality
  changes ownership. The size-eight witness has a drawn shadow root, so it is
  not a counterexample to a supplied-winning-strategy conditional (CU-L028).
- Shifted reply graphs are not tied-root reply graphs. A cycle span or a
  maximum companion rule does not automatically migrate a winning reply
  (CU-L029–CU-L030).
- The prepaid reserve envelope has a paper preservation argument but cannot
  initialize at the first-pair root beyond its stated small case (CU-L031).

## The remaining mathematical task

A useful next invariant needs a structural description, fixed player identities,
causal scheduling, legal turns up to their first catch, well-founded progress,
and closure under every opponent response. It may use actual interval geometry
or restrictions inherited from a hypothetical loss, but those restrictions must
be proved preserved. Defining the relation by the desired outcome or by the
existence of the desired strategy only renames the missing result.

Use the [current route guide](research-routes.md) for the active first-pair,
lower-ray and dense interval obligations. Numerical successes, a local repair,
or this finite controller do not establish the uniform transfer.
