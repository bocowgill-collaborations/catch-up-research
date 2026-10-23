> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# Actual consecutive-tail defense diagnostic

The six prescribed roots were R_N={2,3,4} union [9,N] at deficit1,
for N=11,12,15,16,19,20. This does not assert a uniform theorem.

All six roots are DRAW computationally. Counter2 is the only anchor among
2,3,4 safe in all six. Every root choice was retained:

| N | Root value | Safe first choices |
|---|---|---|
| 11 | DRAW | 2, 9, 11 |
| 12 | DRAW | 2, 3, 4 |
| 15 | DRAW | 2, 3, 9, 10, 11, 12, 13 |
| 16 | DRAW | 2, 3, 4 |
| 19 | DRAW | 2, 3, 4, 9, 10, 11, 12, 13, 14, 16 |
| 20 | DRAW | 2, 3, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20 |

After choosing2, the opponent acts on {3,4} union [9,N] at deficit1.
Every remaining pick ends that turn, so the57 legal opponent picks are
exactly all possible opponent turns. The run evaluated the resulting57
friendly positions and retained every friendly safe choice, not just one
principal variation. All57 endpoints are nonlosing under exact evaluation.

Independent literal-score evaluation matched all six root values and their
63 moves, and all57 policy endpoints and their550 moves.
Thus every selected policy endpoint and all of its choices received the
requested independent calculation. These are experimental results; no Lean
certificate or unbounded strategy theorem is claimed.

## Adjacent reply diagnostic

The policy allowing only y=x-1 or y=x+1 fails at these seven endpoints.
Absent boundary counters are recorded separately from legal losing moves:

| N | Opponent pick x | Deficit | Adjacent choices (outcome) | All safe choices |
|---|---|---|---|---|
| 11 | 3 | 2 | 2: absent, 4: LOSS | 9, 10, 11 |
| 11 | 4 | 3 | 3: LOSS, 5: absent | 9, 10, 11 |
| 11 | 9 | 8 | 8: absent, 10: LOSS | 3, 4, 11 |
| 11 | 11 | 10 | 10: LOSS, 12: absent | 9 |
| 15 | 3 | 2 | 2: absent, 4: LOSS | 9, 10, 14 |
| 15 | 4 | 3 | 3: LOSS, 5: absent | 9, 10, 11, 12 |
| 19 | 3 | 2 | 2: absent, 4: LOSS | 9, 10, 11, 14 |

The smallest failure overall is N=11 and opponent pick3: remaining
{4,9,10,11}, deficit2 is WIN, but adjacent reply4 loses. All safe choices
are9,10,11. The smallest failure involving a tail pick is N=11 and opponent9:
remaining{3,4,10,11}, deficit8 is DRAW, but adjacent reply10 loses;
all safe choices are3,4,11. At the upper boundary N=11 and opponent11,
only9 is safe; predecessor10 loses and successor12 is absent.

No boundary exception or repaired policy was fitted. A proof of choosing2
for the actual family still needs a uniform defense for these full endpoint
families; the adjacent-only rule does not provide it. Passing the other
finite endpoints is not evidence of universal closure sufficient for Lean.

## Reproduction and trust boundary

The frozen ExactSlots evaluator was reused unchanged. It accepts at most14
counters; N=20 has15. The wrapper therefore evaluates each of that root's15
first children with ExactSlots (each child has14 counters) and takes the
exact ternary maximum with the usual role swap. The independent literal
calculation checks that root and every choice. No unsupported constructor
argument or silent evaluator limit change was used.

Inputs and the rule selecting the smallest common safe anchor were saved
before evaluation. The endpoint input list was saved before its separate
run. Each native run had15-second CPU and30-second wall limits. Total
observed time including compilation and all literal checks was
5.017s; peak child RSS high-water was105611264 bytes.
All planned cases completed. There are no unprocessed inputs or active jobs.

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/actual-three-guard/consecutive/run.py
```

`results.json` retains every move value and all literal checks; `plan.json`
records the six original roots and the conditional policy selection rule.
The highest-value next obligation is a structural explanation of why pick2
remains safe on these actual consecutive tails, covering both anchor replies
and every tail reply. The failed adjacent policy is an obstruction to one
simple proposed explanation, not a counterexample to Catch-Up.
