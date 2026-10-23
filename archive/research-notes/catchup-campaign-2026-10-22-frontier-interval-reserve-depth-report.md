> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.IntervalReserveDepth](../../CatchUp/IntervalReserveDepth.lean).

# Interval reserve closure-depth barriers

Status: ready for independent review. Source frozen at SHA-256
`0c779ee454ce512f99779e651beed08b86f5907ea8b89ed7a7ca3f14935b60dd`.

## Proved statements and relevance

Let `R = insert 7 (Icc 9 N)`, choose **any** `y ∈ R`, and start at the
normalized endpoint `(R.erase y, y-3)`, with either player to act. There is no
parity assumption. The permitted opponent choice seven is included.

1. For every `N ≥ 12`, **no legal completed TurnSet** takes the exact balanced
   quota `2 * sum A = sum S + d` (`no_one_turn_balance`). This rejects the
   proposed one-turn score-sum repair uniformly on the actual interval family,
   rather than only on a finite list or a static reserve abstraction.
2. For `N ≥ 8`, every legal `TurnDepth.TurnChain` with final counters `finals`
   that reaches `after.sum ≤ after.deficit` obeys
   `T_N ≤ 26 + 2 * (y + finals.sum)` (`chain_mass_barrier`). Hence, with
   `k = finals.length`,
   `N*(N+1) ≤ 52 + 4*N*(k+1)` (`chain_depth_barrier`).
3. Distinctness of the erased counter and all final counters sharpens this to
   `T_N ≤ 26 + (k+1)*(2*N-k)` (`chain_depth_sharp`). The expression uses natural
   subtraction; the proof establishes `k+1 ≤ N` before replacing it.
4. At `N=11,y=11`, a legal turn preparing seven and ending on ten does balance
   the quota (`eleven_balanced_turn`). The support is `{7,9,10}`, the deficit
   is eight, the chosen sum is seventeen, and the residual singleton nine has
   deficit nine. Thus the uniform threshold twelve cannot be replaced by
   eleven.

These are restrictions on a concrete proof/strategy mechanism. They do not
prove a defensive strategy, settle the interval endpoint's value, establish
any lower bound on formal proof size, or settle Catch-Up. They do not assert a
conversion from arbitrary raw atomic paths into completed-turn chains.

## Proof and dependencies

The elementary interval identity is `sum S + y + 29 = T_N`; also `d+3=y`.
The existing `WholeTurn.balanced_turn_total_bound`, which enforces strict
preparation below the deficit and the actual final pick, gives
`sum S < d+2N` for a balanced legal turn. Therefore
`T_N < 2y+2N+26 ≤ 4N+26`. An induction proves `4N+26 ≤ T_N` for all `N≥12`,
contradiction. This quantifies over all legal chosen sets and final picks.

For a chain, existing `TurnDepth.TurnChain.conservation` gives
`sum S + after.deficit = d + 2*rise + after.sum`. Its leaf inequality yields
`sum S ≤ d+2*rise`, and existing `rise_le_finals_sum` bounds rise by final
counter mass. Substituting the two interval identities gives the mass bound.
The coarse depth bound uses `finals_sum_le`, `y≤N`, and the proved interval
sum formula. The sharp bound uses `finals_nodup`,
`finals_subset_remaining`, and `TurnDepth.interval_subset_sum_bound` on the
distinct interval set represented by `y::finals`. Erasing `y` prevents it
from reappearing as a final counter.

New supporting mathematics is included in the source count: interval-tail
mass identity, interval growth inequality, and the custom endpoint's
distinctness/subset lemmas. Existing WholeTurn and TurnDepth dependencies
are reused without edits. All six public theorem dependency audits contain
only `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`, custom
axiom, compiler-trust axiom, or invocation of the unfinished conjecture.

## Checks and benchmark

Run from `research/catchup`:

```sh
python3 campaign_2026_10_22/frontier/interval-reserve-depth/verify.py
```

The full source first passed LeanProbe without sorry. Production checks:

| Check | Wall seconds | Result |
|---|---:|---|
| `lake --wfail build CatchUp.IntervalReserveDepth` | 7.294 | PASS |
| Fresh source, warnings as errors | 4.348 | PASS |
| Six public axiom audits plus explicit y=7 and interval-y coverage examples | 4.441 | PASS |

All checks had 120-second wall limits and none timed out. The bounded runner
records cumulative child peak RSS of 5,499,617,280 bytes on macOS 26.6.2
arm64; the sandbox prevents querying CPU model and installed RAM. Lean is
4.27.0; Mathlib is pinned at
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. Source: 190 lines, 8,409 bytes.
Olean: 562,808 bytes, SHA-256
`a18bdd9455130f1f0cd0e0d0275902c8f1687d592d67a2d8e0235e3c65b624e9`.
This is a direct parametric proof, with no external search or certificate
generation. No Turing-machine change or state count is involved.

`verification.json`, `checks.json`, the three logs, `audit.lean`, and
`verify.py` preserve the receipt. During runner setup, an incorrect package
directory failed before compilation, then was corrected; the initial
metadata read of hardware RAM was sandbox-denied after all three checks
passed. The runner now records unavailable hardware fields and regenerates
metadata without repeating completed checks via `--metadata-only`.

## Self-check and next obligation

Signs and constants: excluded low-label mass is `36-7=29`; converting
`d=y-3` yields `29-3=26`; doubling the mass bound yields constant 52.
The strict turn inequality remains strict, and equality before a pick is
governed by the existing TurnSet theorem, not an assumed sum criterion.
`N≥8` supports the exact mass identity, while the one-turn contradiction
uses `N≥12`. The y=7 case and N11 sharpness are kernel checked in the audit.
The chain result allows zero-length chains and arbitrary player frames.

The remaining mathematical obligation is a genuinely adaptive unbounded
interval defense through multiple completed turns. A finite-depth quota
repair cannot be presumed sufficient; the proved depth bound grows with N.

Independent review found only a docstring terminology error: twenty-nine is
omitted low-label mass, not a count of omitted labels. Corrected that
docstring; all theorem statements and proof bodies are unchanged. All three
production gates were rerun and passed on the final hash above. Prior receipts
and report remain under `before-docstring-fix/`.
