# Earlier two-buffer controller replay

This supported bundle replays the complete retained policy for the fixed
adjacent-hole instance `N=11,b=4,y=8`. It does not run controller synthesis or
extend any outcome table. Python 3.9 or later is sufficient; no extra package is
needed. Run from the repository root:

```sh
python3 computation/experiments/earlier-campaign/two-buffer/check.py
python3 computation/experiments/earlier-campaign/two-buffer/replay.py
python3 computation/experiments/earlier-campaign/two-buffer/replay.py --full
```

The first command checks all 87 policy nodes and 17 terminal histories, compares
every stored state and its legal child values with the repository's independently
written score recurrence, matches the complete archived replay, and rejects
corrupted policies. The other commands print the two special `[2,11]` histories
or every history, including persistent counter ownership. Assertions are part of
the checker; optimized Python execution is explicitly rejected.

## Exact controller language

Player zero (`p1` in Lean) is protected and keeps that identity. The roots are

```text
actual U: remaining {2,5,6,9,10,11}, scores (0,1), player 0 to move
shadow V: remaining {2,5,6,7,10,11}, scores (0,1), player 0 to move.
```

At each paired node the recorded action commits to one nonterminal game before
the next opponent or supplied-strategy choice is observed:

- At an actual protected turn, the policy chooses one legal counter.
- At an actual opponent turn, the edges must cover every legal counter.
- At a shadow opponent turn, the policy chooses one legal counter.
- At a shadow protected turn, edges cover every legal reply preserving its strict
  win, as evaluated by a separate absolute-score recurrence. This set must be nonempty.

Every step removes one counter; no waiting step is permitted. At every atomic
step, the two raw remaining sets differ by at most two counters on either side.
The ledger is protected actual margin minus protected shadow margin, with owners
fixed at pick time. A tie switches the mover. A pick below the deficit retains
the mover. Early completion awards the entire remainder to the trailing player
and does not silently erase those counters from the buffer test.

Both games must terminate and every leaf must satisfy
`completedMargin(U) >= completedMargin(V)-2`. The fixed policy covers all five
actual second picks and both terminal branches after actual prefix `[2,11]`.
It covers every admissible supplied winning shadow strategy, rather than one
favorable choice of that strategy's replies.

## Evidence and scope

This is a computational replay of a fixed finite artifact. A later
[formal-controller port](../../../../results/two-buffer-controller.md) adds the
archived Lean protocol and mandatory-instance proof to the maintained library,
without changing these replay sources or certificate bytes. No unbounded
adjacent-hole translator or interval draw theorem follows. Shadow outcome
queries validate the allowed supplied-
strategy filter; they are not a structural repayment invariant.

After building `CatchUp.TwoBufferMandatory`, run
`python3 scripts/check_controller_policy.py --lean` from the repository root to
match the actual Lean table to all reachable replay states. The table has 76
rows and 74 distinct normalized keys; the two repeated keys have identical
actions. The JSON additionally retains the full ownership histories.

`reference.py` extracts only the old fixed-player score recurrence and ownership
state. `replay.py` retains the old checker and mutation controls, changing imports,
the default input path and the explicit optimized-execution guard. Neither imports
the synthesis solver. `policy.json` and `historical-replay.json` preserve the
archived bytes. The [source manifest](../../../../verification/two-buffer-replay.json)
and [reconstruction check](../../../../scripts/check_two_buffer_sources.py) document
these changes, including source mutation controls.

See [strategy transfers](../../../../results/strategy-transfers.md), finding
[CU-L026](../../../../results/legacy-findings.md#cu-l026--full-mandatory-causal-two-buffer-controller),
and the [campaign archive](../../../../archive/campaigns/).
