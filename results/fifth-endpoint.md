# Fifth-from-top lower-ray nonloss

For every natural `N≥23`, put `I_N={1,…,N}` and
`Q_N(b)=(I_N \ {1,b}, b−1)`, with value from the player to move,
who is behind by the displayed deficit. Then **Q_N(N−4) is nonlosing**:
the remaining counters are `I_N \ {1,N−4}` and the deficit is `N−5`.
There is no parity premise, smaller-instance draw premise, or appeal to the
unfinished Catch-Up conjecture.

```lean
theorem CatchUp.pair_deletion_position_fifth_from_top_value_ne_loss
    (N : ℕ) (hN : 23 ≤ N) :
    (CatchUp.pairDeletionPosition N 1 (N - 4)).value ≠ .loss
```

The theorem is in [LowerRayFifthEndpoint](../CatchUp/LowerRayFifthEndpoint.lean),
imported by the default mathematics library. This settles one member of the lower
ray, not every `b`, a draw for this position, or the initial interval conjecture.
Applying it at an odd-triangular size does not make that initial game a draw.

## How the proof works

Put `m=N−6≥17`. A hypothetical lower-ray loss forces a losing post-opening state
on the tied residual

```text
F(m,4) = [2,m] union {m+3,m+4,m+5,m+6},
```

with opening among the four displayed upper counters. The already verified
[winning-opening bound](../CatchUp/Earlier/DeficitWinningBound.lean) supplies
that restriction. The four symbolic upper-opening theorems prove that none
of these post-opening states loses.

The reusable [exact-sum residual interface](../CatchUp/ExactSumResiduals.lean)
says: if a positive block `A⊆S` sums exactly to deficit `d` and contains `c`, it
suffices that every post-opening state on `S\A` with opening `w>c` is nonlosing.
Otherwise the existing exact-sum obstruction produces a losing opening strictly
above `max A≥c`, a contradiction. Positivity, subset membership, exact sum and
every potentially forced residual opening remain explicit obligations.

The upper-opening proofs enumerate every structurally permitted witness,
including lower intruders. Their symbolic branches terminate with arithmetic
contradictions. They use no outcome table, external solver or native evaluation.
The archived 35-node/14-leaf description is historical context, not an additional
Lean count theorem of this port.

The bound `m≥17` is unchanged. At `m=16`, one archived block would repeat
counter 11 because `m−5=11`; a set cannot count the same counter twice.
This is a boundary of that certificate, not a counterexample to a weaker-bound
game-value claim. No sharpness assertion for `N≥23` is made.

## Reuse and remaining work

- Import `CatchUp.LowerRayFifthEndpoint` and apply the headline theorem with `23≤N`.
- Import `CatchUp.ExactSumResiduals` for the generic interface on other supports.
- The interface is extracted from the archived fourth-endpoint module. Its other
  results were not ported or newly checked here; a future port should import this
  interface rather than redeclare it.
- Arbitrary upper-tail length, the full lower ray and a uniform interval strategy
  remain open. The existing [upper-only descent obstruction](../CatchUp/Earlier/UniformExactSumDescentObstruction.lean)
  still applies to its specified proof language.

This is a port of earlier research, not a discovery claim. See
[CU-L037](legacy-findings.md#cu-l037--fifth-endpoint-and-four-tail-forcing-forest)
for its historical context, [source provenance](../verification/fifth-endpoint-port.json)
for exact hashes and transformations, and [verification](../verification/fifth-endpoint.md)
for fresh checks. Archived files retain historical status; only the named port
receives the fresh assurance described there.
