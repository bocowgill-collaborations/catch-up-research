> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.DenseTwoResidual](../../CatchUp/DenseTwoResidual.lean).

# Uniform exclusion of nonterminal two-counter residuals

`CatchUp/DenseTwoResidual.lean` proves a positive nonterminal subcase and
composes it with the finished terminal result. No earlier proof source
was edited, and no new game search or external game-value table is used.

## Exact uniform statements

The setup is S contained in [1,N], actual hole count h, `2*h+1<=d<=N`,
and even effective total `sum(S)+d`. B is a subset of S summing to d,
with b in B. The maximality premise quantifies over **all** exact-d
subsets D of original S and all their members x: x<=b. The opening
counter w belongs to S minus B and satisfies b<w<d. The target d-w is
unrepresentable as a sum of any subset of original S.

`nonterminal_two_residual_impossible` assumes additionally that
`C=(S minus B).erase w` has exactly two counters, `sum(C)>=w`, and the
actual normalized residual opening `afterOpening (S minus B) w` loses.
It proves False. No parent-loss assumption or target-missing substitute
for the full subsum gap is used.

`small_residual_successor_nonloss` assumes instead `card(C)<=2` and the
same actual residual-opening loss. It proves that the continuing successor
`(S.erase w,d-w)` is nonlosing. For terminal C this invokes the unchanged
uniform `DenseTerminalNonloss` result. For zero or one counter, a losing
residual must be terminal. For two nonterminal counters, the new impossibility
theorem applies. Thus a counterexample to this full gap-closure subcase
requires residual cardinality at least three.

## Proof kernel

A catchable losing pair at deficit w, with w absent, must have both counters
strictly above w. If a counter u were below w, taking it would strictly
continue to a singleton whose counter is at least the new deficit w-u.
That singleton is drawn or winning, contradicting the losing child
required by the exact move semantics. Equality u=w is excluded by absence.
The general pair helper proves precisely this necessary fact.

The existing large-exact-member lemma supplies b>=d-h. `DenseBlockMass`
then gives card(B)<=4 and N<=13. Remove b to obtain the tail A. Its
cardinality is at most three, and its sum is at most h, while density
gives `h<=card(B)+2`. Hence `sum(A)<=card(A)+3` and every tail member
is a positive counter at most six. The exact possible tails are:

```
{}, {1}, {2}, {3}, {4}, {1,2}, {1,3}, {1,4}, {2,3}, {1,2,3}.
```

`tail_classification` checks this tiny arithmetic assertion in the kernel.
Write the residual as ordered counters w<u<v and reconstruct
`S=insert w (insert b A) union {u,v}`, with `d=b+sum(A)`.
The bounded arithmetic theorem enumerates N<=13, b in [1,N], these ten
tails, w in [b+1,d-1], u in [w+1,N], and v in [u+1,N]. It checks the
original density, parity, full exact-block maximality, and original-S
subsum gap. No configuration survives. This is a compact arithmetic
classification, not a game search or a proof from a sampled list.

The main proof maps every arbitrary input into this classifier. In
particular, it proves the support reconstruction, ordered residual,
tail inclusion, and all bounds; none are assumed merely because N is small.
The classifier ranges over all exact-d subsets when checking maximality.
It does not restrict that family by block cardinality.

## Verification and scope

From `research/catchup`:

```
lake --wfail build CatchUp.DenseTwoResidual
lake env lean campaign_2026_10_22/frontier/two-residual/audit.lean
```

`build.log` and `axioms.log` retain the final checks. The bounded arithmetic
classifier's isolated initial LeanProbe check took 16.375 seconds at
default budgets. The final warning-strict build took 25.056 seconds wall
time (22 seconds reported for the module); the audit took 4.989 seconds.
The source has 217 lines, 9,912 bytes, six theorems, two definitions, and
one decidability instance. Six headline transitive axiom audits are restricted to
`propext`, `Classical.choice`, and `Quot.sound`. There is no native proof
evaluation, custom axiom, `sorry`, unsafe definition, or raised budget.
`source-check.json` records source size, counts, hash, and prior-source
preservation, including the finished terminal module and mass module.
`PairProbe.lean` retains the independently checked local helper; no
production module imports campaign scratch files.

The pencil proof in `density_proof/high-deficit/full-strategic/small-residual.md`
motivated this elimination. The Lean proof uses the bounded arithmetic
classification in place of individually formalizing its tail subcases.
The parent owns independent statement review. Residuals of cardinality
three or more, general closure of density/subsum assumptions, H, and C
remain open.
