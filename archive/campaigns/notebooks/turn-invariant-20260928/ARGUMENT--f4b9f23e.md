> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# A prepaid gap reserve: candidate and initialization obstruction

This is a complete paper argument submitted for independent review. The endpoint
conjecture is not claimed. The invariant is sound under its hypotheses, but the
proposed immediate initialization is impossible for every N > 7.

## 1. Actual two-phase certificate

All counters are distinct positive integers. Fix a protected player. At an
opponent-turn boundary, let L >= 0 be the protected player's actual score lead.
Partition the remaining support as P disjoint-union B. Partition P into unequal
pairs. Write D for the sum of the absolute pair gaps and W=sum(B). Require

    D + W <= L;
    L + D + W <= x for every x in P.                 (R)

The unrefined candidate is B empty. The only refinement permits arbitrary B.
No bound is imposed on its cardinality. Pair assignments are fixed in advance
for this certificate; they are not changed after observing an opponent choice.
The two inequalities mean respectively that all unfavorable pair orientations
and all unpaired counters are prepaid, and that paired counters remain large
enough to end the opponent's turn as soon as one is selected.

The protected-turn phase consists of an actual opponent completed turn from R:
some T subset B followed by one x in P. Retain T, x, and its available mate z.
The protected deficit is x+t-L, where t=sum(T); the prescribed reply is z.
This phase is arithmetic/history data, not a game-outcome predicate.

## 2. Legality and closure

If P is nonempty, D >= 1 because every pair has distinct integer endpoints.
Consequently W < L. The opponent cannot catch using only B. Every paired
counter is at least L+D+W, hence strictly greater than L. The first selected
paired counter ends the turn, regardless of which subset T of B preceded it.
There cannot be a second paired counter in that turn. Before this counter, the
preparation total t <= W < L; thus all preparation prefixes remain below L.
Availability is literal, and the paired counter ensures catchability throughout.

Put delta=z-x and g=|delta|. The protected reply catches, since

    L-t+delta >= L-W-g >= D-g >= 0.

Thus z >= x+t-L. It is available and this inequality also ensures the protected
state has not already terminated through inability to catch. Equality switches
players, as required by the repository rules.

After the reply remove the pair and T and update

    L' = L-t+delta, D' = D-g, W' = W-t.

The lower slack changes by

    L'-D'-W' = L-D-W + delta+g >= L-D-W.

The upper expression changes by

    L'+D'+W' = L+D+W - 2t + delta-g <= L+D+W.

Every remaining paired counter therefore satisfies the upper inequality and
the lower inequality also persists. Each macro deletes a pair, so termination
is well-founded. If P becomes empty, the protected lead is at least W. Awarding
all remaining counters to the opponent leaves protected margin L-W >= 0.
This covers early termination and equality; the protected player need not make
another move. If L=0 in a certified opponent state, the lower inequality forces
D=W=0 and there are no counters. No nonterminal tied turn is hidden in the proof.

This proves a restricted strategy theorem by induction on the number of pairs.
It uses no outcome calculations, shadow game, or conjecture premise. It does
not assert that (R) holds on all safe states or on the desired roots.

## 3. Necessary numerical envelope

For any genuine pairing, |P| <= 2D: there are |P|/2 pairs, each with gap >= 1.
We relax the certificate by forgetting the pairs entirely and retaining only

    B subset S; P=S\B; D a natural number; |P| <= 2D;
    D+sum(B) <= L;
    L+D+sum(B) <= x for all x in P.                 (E)

This is a necessary envelope, NOT a sufficient strategy certificate. Showing
that even E cannot initialize excludes all actual pairings, including the
best initial pairing. It does not rule out other strategy languages.

## 4. Parametric initialization obstruction

Take N>=7 and any first pick a in {3,...,N}. The actual child has opponent to
move, support S={3,...,N}\{a}, and protected lead L=a-1. Suppose E holds.

First P cannot be empty. Otherwise S=B and sum(S)<=a-1. If a<N, S contains N,
so sum(S)>=N>a-1. If a=N, S contains distinct 3 and N-1; its sum is at least
N+2>a-1. Both cases contradict the lower inequality.

Let m be the minimum of P. Since P is nonempty and |P|<=2D, D>=1. The upper
inequality gives

    a+W <= m, where W=sum(B).

As m belongs to S, m!=a, so m>=a+1. If m>=a+2, the integer m-1 belongs to S,
is below every element of P, and therefore belongs to B. Thus W>=m-1, forcing
a+m-1<=m, or a<=1, a contradiction. Hence m=a+1.

If a>3, the integer 3 belongs to S and lies below m, so W>=3. But a+W<=a+1
gives W<=1. Therefore a=3 and m=4. Again W<=1, while every counter in B is at
least 3, so B is empty. The upper inequality becomes 2+D<=4, so D<=2. Finally

    N-3 = |S| = |P| <= 2D <= 4,

giving N<=7. With the assumed N>=7, equality holds.

The bound is sharp: N=7, a=3, B empty, pairs {4,5},{6,7}, L=D=2 satisfy R.
No parity assumption was used in the obstruction. In particular it covers
every admissible N>7 in the research target.

## 5. Exact conclusion and stopping point

The route fails at INITIALIZATION, not at the algebraic preservation step.
Adding arbitrary unpaired counters does not repair it. One could try to reach
the reserve region later, but no strategy forcing such entry is supplied here.
Calling that entry routine would reintroduce the original strategic difficulty.
This does not prove every safe strategy must violate either inequality, since
other certificates and later entry remain possible. It proves that no direct
opening-based proof using this prepaid envelope can cover N>7.

The obstruction uses the whole interval below the least paired counter, not
only parity or a local available neighbor. It identifies why charging all
future pair errors against a lead while keeping the opponent outside the paired
reserve is too expensive at the interval's low end.
