> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current results guide](../../results/README.md).

# The actual c=5 equality diagnostic did not reach its premise

For q=14,...,20 and N=q+4,...,23, the21 nonempty parameter cases were
saved before evaluation. For q=20 there is no permitted N. Set
A={3,4} union [9,N], b=q-1, w=q+4, C=A minus{b,q,w}.
Every C has at most14 counters, within the unchanged frozen evaluator.

All21 queried values V(C,w) completed:14 WIN,7 DRAW,0 LOSS. Every one of
these roots' 259 first-choice values is retained. Among the11 cases
with eligible N, the results are4 WIN and7 DRAW. The other10 cases have
ineligible N and are marked separately; they cannot refute a statement
requiring eligible N.

| q | N | Eligible N? | C at w |
|---|---|---|---|
| 14 | 18 | no | WIN |
| 14 | 19 | yes | WIN |
| 14 | 20 | yes | WIN |
| 14 | 21 | no | WIN |
| 14 | 22 | no | WIN |
| 14 | 23 | yes | DRAW |
| 15 | 19 | yes | WIN |
| 15 | 20 | yes | DRAW |
| 15 | 21 | no | WIN |
| 15 | 22 | no | WIN |
| 15 | 23 | yes | DRAW |
| 16 | 20 | yes | WIN |
| 16 | 21 | no | WIN |
| 16 | 22 | no | WIN |
| 16 | 23 | yes | DRAW |
| 17 | 21 | no | WIN |
| 17 | 22 | no | WIN |
| 17 | 23 | yes | DRAW |
| 18 | 22 | no | WIN |
| 18 | 23 | yes | DRAW |
| 19 | 23 | yes | DRAW |

The conditional equality endpoint was
R=insert b (C minus{3,b+2}), deficit b. It would only be queried after
C at w was LOSS. No such premise occurred, so R and the original parent
S=A minus{q} at deficit b were NOT queried. In particular, this run
provides no successful test of the proposed conditional equality repair:
its premise failed in every tested case. It does not prove the premise
impossible uniformly.

The first, middle and last completed C controls (case IDs1,11,21) received
independent literal-score evaluation of their roots and all37 first
choices. All matched. No other literal checks were performed because no
CLOSS/R context was reached. The exact native calculations and these literal
controls remain experimental evidence; there is no new Lean theorem here.

All21 planned cases completed, with no active jobs, unprocessed inputs or
literal checks pending. Total time including compilation and literal checks
was1.997s; native cumulative CPU was
0.031290s. Peak child RSS high-water was
106823680 bytes. The native15sCPU/30swall and total30sCPU/60swall
budgets were not approached. No larger N, generic mutation or new solver was
introduced.

Reproduce from workspace root:

```sh
python3 research/catchup/campaign_2026_10_22/resume_01/gap-five-diagnostic/run.py
```

The proof work must still handle the symbolic high-CLOSS assumption directly,
or prove its impossibility from actual geometry. This finite experiment does
not distinguish those approaches and does not justify a broader search by
itself. The full-parent SLOSS hypothesis may still be essential.
