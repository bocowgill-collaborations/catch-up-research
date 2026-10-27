# Lower-ray endpoints and reachable traps

Three archived modules now provide 12 maintained public theorem declarations.
They add an endpoint and parametric diagnostics, not a solution of Catch-Up.
See [provenance and checking](../verification/endpoint-atlas-ports.md).

## Exact-pair defense and the penultimate endpoint

[LowerRayEndpoints](../CatchUp/LowerRayEndpoints.lean) proves nonloss when distinct
available counters `a,c` sum to the deficit, `c>0`, and every counter left after
deleting them is strictly smaller than `c`. Taking `a` continues the same turn:
`a<a+c`. The child has deficit `c`, with `c` available as a maximum, so the
existing maximum-deficit theorem excludes loss. The original contract does not
require `a>0`. For positive blocks this overlaps the existing
[dominating-block defense](../CatchUp/ExactSumLossObstruction.lean); no existing
declaration is replaced or weakened.

Using `{3,m}`, the module proves `Position([2,m],m+3)` nonlosing for `m>=4`.
The endpoint theorem is

```text
N >= 7  ==>  value(Q_N(N-1)) != loss,
Q_N(b) = Position(I_N \ {1,b}, b-1).
```

A hypothetical endpoint loss has exact deficit `N-2` available. The forced larger
residual opening can only be `N`; its post-opening state is
`Position([2,N-3],N)`. The tail theorem contradicts its forced loss. No parity
or smaller-instance draw premise is needed. This is endpoint nonloss, not
first-pair draw or uniform lower-ray nonloss. See the [endpoint catalog](lower-ray-endpoints.md).

## Adjacent-pair shortcuts fail parametrically

[AdjacentPairGeometryObstruction](../CatchUp/AdjacentPairGeometryObstruction.lean)
proves these current-mover-relative statements:

- For `a>=4`, `Position({a,a+2,a+3},a-1)` wins. A smallest orphan is not
  automatically a nonwinning reserve.
- For `a>=6`, `Position({a,a+2,a+3,a+4},5)` loses, with every legal pick covered.
- For `a>=6`, picking `a+1` from `Position([a,a+5],1)` loses. The opponent can
  answer with `a+5`, leaving that losing quadruple. A separate theorem checks
  availability, catching and nonterminality.

The last statement concerns one pick, not the entire six-counter position's
value. A first pick from this state is not the special opening of an initial
interval. These failures do not settle arbitrary odd-pair nonloss or Catch-Up.

## A winning five-counter endgame can be reached legally

[FiveConsecutiveTrap](../CatchUp/FiveConsecutiveTrap.lean) proves that a tied game
on `[a,a+4]` wins for its opener when `a>=4`. The normalized state
`Position([a,a+4],d)` also wins for `a>=6` and `d<=a+1`, including `d=0`.

For every `k>=2`, opening `3` in `I_(4k)` admits a legal history reaching

```text
remaining = [4k-4,4k], deficit = 0, player to move = p1.
```

After opening, player two takes `1`, then `2`. Equality ends that turn, leaving
tied support `[4,4k]` with player one moving. From a tied tail starting at `l`,
the successive picks `l,l+1,l+3,l+2` remove its bottom four counters and return
to a tie with the same player moving. Each pick catches at its own step,
including the final equality: this is not one four-pick turn. Repeating the
quartet `k-2` times leaves the top five. Every intermediate step is proved legal,
not merely equal as a final score update.

The reached state wins for player one. The quantifier is **there exists a legal
history**. Player one is not proved able to force that history, and optimal play
is not proved to enter the trap. This is not an initial-interval counterexample.

## What remains

These ports complete the small endpoint/trap batch. They neither prove first-pair
draw nor supply a family preserved against all opponent replies. CU-L039's
packing argument remains informal. Larger imports should serve a concrete proof
need; see the [handoff](../docs/research-handoff.md). Original reports and
certificates are unchanged. No new outcome tables or large searches are introduced.
