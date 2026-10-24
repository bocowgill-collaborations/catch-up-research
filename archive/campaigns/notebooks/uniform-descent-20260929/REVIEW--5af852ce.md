> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent adversarial review

Date: 2026-09-29.
Scope: `LowerRayFifthEndpoint.lean`, its statement/axiom audit, and
`INDEPENDENT_IDEA.md`. Production sources are read-only for this reviewer.

## Acceptance ledger

The reviewer owns only this file, so this ledger stays here rather than in a
second `GATES.md` file.

- [x] R1: The formal endpoint has exactly the requested support, deficit, and range.
  EVIDENCE: LowerRayFifthEndpointAudit.lean:30 states the exact set-difference theorem with only N : Nat and 23 ≤ N. The endpoint reduction uses m = N - 6 and b = N - 4.
- [x] R2: Move polarity, equality, exact blocks, all witness branches, and terminal exclusion are valid.
  EVIDENCE: All 35 exchange nodes and 14 leaves were reviewed against the exact-sum lemma. The lower-witness branch m-1 is retained. The boundary block {11,m-5} is {11,12} at m=17. Details below.
- [x] R3: A warning-strict affected-scope build and transitive axiom audit succeed.
  CHECK: lake --wfail build catch_up.LowerRayFifthEndpointAudit
  EXPECT: Build completed successfully
  EVIDENCE: Reviewer rerun from HISTORICAL_TMP/catchup-score-debt-20260928, zsh launcher/direct child process, exit 0, expected token matched, no warning. SHA256(stdout+stderr)=e06143e42bffc889cb8e65c4c77d95bc06874bb5fbecff19fb9ff325745eedd6, 1126 bytes, 1963 ms. Lake replayed current artifacts; the parent completed the original elaboration. All six audit declarations have exactly propext, Quot.sound, Classical.choice.
- [x] R4: The independent obstruction statements are valid within their explicitly restricted proof grammar.
  EVIDENCE: Reviewed all three sections, including m=6, q=3, the separation m≥2k+2, and the m=9 support transformation. These remain informal proofs, not Lean results.

## Verdict

PASS for the stated fifth-from-top endpoint and PASS for the informal
restricted-grammar obstructions. No substantive mathematical error was found.
All four review gates are met; none is abandoned.

This does not prove the whole Catch-Up conjecture, the whole lower ray, a
uniform theorem in the number of upper counters, or the separate first-pair
target. No production source or other contributor's file was edited.

## Exact theorem and dependency boundary

The requested proposition is exactly:

```lean
∀ N : ℕ, 23 ≤ N →
  Position.value ⟨Finset.Icc 1 N \ {1, N - 4}, N - 5⟩ ≠ .loss
```

`LowerRayFifthEndpointAudit.set_difference_form` states it directly. No
parity, lower-interval draw, inductive conjecture, reachability, or other
unstated premise is present. The support identity in the audit is the
ordinary equivalence between deleting two elements and subtracting their
two-element set. Natural subtraction is reconciled by `Nat.sub_sub`.

For the bridge, `pairDeletionPosition N 1 (N-4)` has deficit
`(N-4)-1=N-5`. Its available deficit is removed by the existing upper-residual
rule, leaving `[2,N-6] ∪ {N-3,N-2,N-1,N}`. Thus `m=N-6≥17` and the four
required upper openings are exactly `m+3,m+4,m+5,m+6`.

The new proofs depend on `Position.value_ne_loss_of_exact_sum_residuals`
and `pair_deletion_position_value_ne_loss_of_upper_residuals`, not on the
previous fourth-endpoint theorem's conclusion. The former wraps the
exact-sum obstruction; the latter uses the available-deficit obstruction.
Both ultimately use the actual normalized game evaluator.

The audit calls `Lean.collectAxioms` on all four opening theorems, the
endpoint theorem, and the exact set-difference theorem, and rejects every
axiom outside `{propext, Quot.sound, Classical.choice}`. The successful
output reports exactly those three for every declaration. In particular,
there is no transitive `sorryAx`, native-evaluation axiom, or custom axiom.
The imported main conjecture remains a `sorry` declaration in
`CatchUpConjecture.lean:790`; the axiom audit confirms it is not used here.

## Move semantics, equality, and terminal rules

`Position.value` and `Position.moveOutcome` preserve the player's
perspective precisely when the picked counter is strictly smaller than the
deficit. Otherwise they negate the child value. Equality therefore ends
the turn and swaps players; it is not treated as a continuing pick.

In the exact-sum obstruction, all but a positive maximum counter form a
strict sub-deficit prefix. Their picks preserve a hypothetical loss.
Taking the final maximum counter makes the scores equal and passes the
turn, so the tied residual is winning, not losing. A winning opening of
that tied residual has a losing post-opening value. The exchange argument
correctly proves that its counter must exceed the deleted block maximum.

The recursive wrapper needs only a chosen member `c` of the exact block:
every witness above the true maximum is also above `c`. It consequently
asks the candidate to handle a possibly larger set of witnesses, never a
smaller one. The candidate handles all such witnesses.

No move is applied beyond the immediate-cannot-catch terminal rule. At
every exact-block application, the block's containment and exact sum imply
`sum remaining ≥ deficit`, and its positive membership implies that the
position is nonempty. The prefix and exchange proofs establish the same
conditions at their intermediate positions. At a candidate leaf, the
universal witness obligation is contradictory because the residual has no
counter above the selected pivot. This is an exact-sum domination argument,
not an unsupported declaration that the residual game itself is terminal.

## Blocks and full witness coverage

The four trees contain respectively 12, 15, 5, and 3 exchange nodes,
with respectively 5, 6, 2, and 1 leaves. The largest number of exchange
blocks on a branch is five. Every exact block is positive, has distinct
members, remains available after all previous deletions, and sums to its
current deficit.

The critical branch in the second opening theorem is:

| Current deficit | Exact block | Next selected permitted witness |
| --- | --- | --- |
| `m+4` | `{4,m}` | `m+3` |
| `m+3` | `{5,m-2}` | `m-1` |
| `m-1` | `{2,m-3}` | `m+5` |
| `m+5` | `{9,m-4}` | `m+6` |
| `m+6` | `{11,m-5}` | none |

In particular, the lower intruder `m-1` is explicitly covered at
`LowerRayFifthEndpoint.lean:252`. It has not been incorrectly discarded by
assuming that every witness is upper. The alternative upper-witness
branches at that node are also handled. At the final boundary block,
`m=17` gives `{11,12}`, with sum 23 and both counters still present.
At `m=16` the displayed block would collapse to the singleton `{11}`;
the proof's threshold is therefore substantive. This is not a claim that
the game theorem fails below the threshold.

All small block entries are at most 11. Every affine pivot is at least
`m-5≥12`. This separates the small constants from the moving pivots
throughout the stated range. Each source membership/distinctness/sum
obligation is independently kernel-checked for all `m≥17`; the numerical
check below is only supplemental evidence.

## Informal obstruction review

1. **Upper-only closure:** PASS within the stated grammar. For `m≥6`,
   the first upper-only exact block after opening `m+4` must contain `m`
   and hence is `{4,m}`. The structurally permitted witness `m+3` leaves
   lower maximum `m-1`, but no available subset can supply its required
   complement 4. The text correctly distinguishes a structurally permitted
   witness from a witness known independently to lose. Additional semantic
   branch exclusions or other terminal lemmas are outside this grammar.
2. **Sharp packing:** PASS. Every finite exact-q block lies in
   `{2,...,q-2,q}`, of total weight `q(q-1)/2`. Disjointness gives at most
   `floor((q-1)/2)` blocks. `{q}` plus the unordered complementary pairs
   reaches the bound, including `q=3`. In the application,
   `m≥2k+2` ensures the last moving pivot is at least `k+3>q=k+2`;
   therefore small complements do not consume later pivots. The descending
   upper branch requires k disjoint complements and cannot close in that
   normal form.
3. **Repair support:** PASS. For `m≥9`, the three displayed blocks are
   distinct and available along the displayed branch. Their deletion,
   together with the three opening deletions, leaves exactly
   `([2,m-4] \ {2,4,5}) ∪ [m+5,m+k+2]` before the next upper opening.
   The widened gap and the consumed complement 2 prevent repetition of
   this identical local repair without additional structure.

These statements have not been formalized in Lean. They refute restricted
certificate grammars, not Catch-Up, and do not supply a closed parametric
replacement. The note itself respects that boundary.

## Supplemental reproducible arithmetic check

The following JavaScript was run via `node -e` from the repository root.
It reads the existing `quad_trees.json` and checks each exact block, all
deletions, and equality of the encoded child list with the *full* set of
structurally permitted witnesses. Source review separately matched the
JSON trees to the Lean branches; this script does not parse Lean.

```javascript
const fs = require("fs");
const trees = JSON.parse(fs.readFileSync(
  "research/uniform-descent-20260929/quad_trees.json", "utf8"));
let nodes = 0, leaves = 0, maxDepth = 0;
function check(t, m, S, d, depth) {
  const A = [...t.small_block, m + t.pivot_offset];
  const a = new Set(A);
  if (t.deficit_offset + m !== d || a.size !== A.length ||
      A.some(x => x < 2 || !S.has(x)) ||
      A.reduce((s, x) => s + x, 0) !== d)
    throw Error(`bad block at m=${m}, d=${d}`);
  const T = new Set([...S].filter(x => !a.has(x)));
  const witnesses = [...T].filter(x => x > m + t.pivot_offset)
    .sort((a, b) => a - b);
  const encoded = t.children.map(([w]) => m + w)
    .sort((a, b) => a - b);
  if (JSON.stringify(witnesses) !== JSON.stringify(encoded))
    throw Error(`bad witness set at m=${m}, d=${d}: ${witnesses} != ${encoded}`);
  if (m === 17) {
    nodes++;
    if (!t.children.length) leaves++;
    maxDepth = Math.max(maxDepth, depth);
  }
  for (const [w, ch] of t.children) {
    const U = new Set(T);
    U.delete(m + w);
    check(ch, m, U, m + w, depth + 1);
  }
}
for (let m = 17; m <= 100; m++) {
  for (const root of trees) {
    const S = new Set(Array.from({length: m - 1}, (_, i) => i + 2)
      .concat([m + 3, m + 4, m + 5, m + 6]));
    S.delete(m + root.opening_offset);
    check(root.tree, m, S, m + root.opening_offset, 1);
  }
}
console.log(JSON.stringify({
  status: "all blocks and full witness sets verified for 17<=m<=100",
  nodesPerM: nodes, terminalLeavesPerM: leaves, maxDepth
}));
```

Result: all checks passed; 35 nodes, 14 leaves, maximum depth 5.
Reported tool wall time was 0.1 seconds, comfortably below one second.
This is a bounded arithmetic certificate check, not a computation of
game outcomes and not the justification for the all-m theorem. It is the
only new mathematical computation performed by this reviewer.

## Snapshot and limitations

Reviewed branch: `codex/catchup-uniform-descent-20260929`.
Base commit: `faad9dccf6723b46fc252cbdaebf337427809044`.

SHA-256 digests at final source inspection:

- `LowerRayFifthEndpoint.lean`:
  `22343ed0e5e90a6a524c59f5e41c785a21a3e09cc5ae6c95565cc6aa0e5dc71b`
- `LowerRayFifthEndpointAudit.lean`:
  `63cd40b3556e0c3633557511fbd2fd4cedfaad226b0ad6cce3d8bef00d376755`
- `INDEPENDENT_IDEA.md`:
  `128c5796fa94e9738bc0cb22a79518d775704aa88cd158e1d90b08059e8736f8`

Only the affected target was built. No whole-project build, new proof,
external publication, branch change, commit, or production edit was made
by this reviewer. The theorem concerns nonloss, not necessarily a draw.

Nonblocking presentation issue: several new Lean docstrings contain doubled
LaTeX backslashes, for example `\\ge` rather than `\ge`; these may render
incorrectly. This does not affect the Lean statement or proof.
