> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Independent conceptual result: lower intruders are necessary

Status: exact failure of two natural exchange-closure classes. No uniform
upper-tail nonloss theorem is claimed. These are mathematical arguments about
proof closure, not computed outcome tables or counterexamples to Catch-Up.

Write

\[
F(m,k)=[2,m]\cup[m+3,m+k+2].
\]

The only game-theoretic premise used below is the established exact-sum
obstruction: from a loss at `(S,d)` and a nonempty positive exact block
`A ⊆ S`, `sum A = d`, one obtains a losing post-opening state with a witness
`w ∈ S \ A` satisfying `w > max A`.

## 1. No upper-only closure, even with upper consumption

Assume `m >= 6`, `k >= 2`. Consider the hypothetical loss after opening
`m+4`. An **upper-only exchange** means that every witness permitted solely by
membership and the strict maximum bound is in the original upper interval:

\[
\{w\in S\setminus A:w>\max A\}\subseteq[m+3,m+k+2].
\]

Claim: no exact-sum forcing tree using only upper-only exchanges can close
this opening. This remains true when the chosen exact blocks can be arbitrary
positive subsets, not just pairs.

Proof:

1. The deficit is `m+4`; that counter has been removed. No available upper
   counter can belong to an exact block. The only smaller upper is `m+3`,
   and its required complement is `1`, which is absent. Every other upper
   exceeds the deficit.
2. Consequently an exact block contains only lower counters. If its maximum
   were below `m`, then the still-available `m` would be a permitted lower
   witness. Thus an upper-only block must contain `m`.
3. The rest of the block must sum to `4`. Among distinct integers at least
   `2`, the sole such subset is `{4}`: two distinct elements already sum
   to at least `2+3=5`. Thus the first block is forced to be `{4,m}`.
4. The witness `w=m+3` remains structurally permitted. Its descendant has
   deficit `m+3`, remaining lower maximum `m-1`, and counter `4` absent.
   Its remaining upper counters, if any, all exceed the deficit.
5. At this descendant, an upper-only exact block must contain `m-1`, for
   the same maximum argument. Its remaining elements must again sum to
   `4`. This is impossible because `4` was removed and every distinct
   pair of positive available counters has sum at least `5`.

This proves failure of the upper-only certificate class. It does **not**
assert that the specific witness in step 4 actually loses. A hypothetical
loss supplies some witness; a proof using only the structural bound must
handle every witness permitted by that bound. A separate semantic theorem
excluding `m+3` would be additional information outside this closure class.

In particular, increasing `m`, adding more upper counters, or replacing pair
complements by arbitrary subsets does not repair this obstruction. A proof
must permit a lower witness, exclude a permitted branch by an additional
semantic argument, or use a different proof step.

## 2. Sharp budget obstruction to consecutive lower pivots

For any integer `q >= 3`, the maximum number of pairwise disjoint subsets of
the integers at least `2`, each summing to `q`, is

\[
\left\lfloor\frac{q-1}{2}\right\rfloor.
\]

For the upper bound, every used number is at most `q`, and `q-1` cannot
occur: its required positive remainder would be `1`. Therefore all blocks
lie in `{2,...,q-2,q}`, whose total sum is

\[
\sum_{a=2}^{q-2}a+q
=\frac{(q-2)(q-1)}2-1+q
=\frac{q(q-1)}2.
\]

If there are `r` disjoint blocks, `rq <= q(q-1)/2`, proving the bound.
It is attained by the singleton `{q}` and the pairs `{a,q-a}` for
`2 <= a < q/2`.

Apply this with `q=k+2`, `k>=2`, and, for clean separation, `m>=2k+2`.
Suppose a forcing scheme always chooses the current lower maximum as pivot,
never consumes an upper counter inside its exact block, and permits no
lower witness. The descending structurally permitted opening branch is

\[
y_j=m+k+2-j,\qquad j=0,\ldots,k-1.
\]

At step `j`, the lower maximum is `m-j`; the required small complement is

\[
y_j-(m-j)=k+2=q.
\]

The complements must be disjoint because exact blocks are deleted. Closing
the whole branch requires `k` such blocks, but at most
`floor((k+1)/2) < k` exist. This refutes even arbitrary-subset versions of
the consecutive-lower-pivot normal form for every `k>=2`.

This is stronger than a repeated-singleton objection. No amount of unused
lower reserve above `q` can contribute to a block of sum `q`.

## 3. What the existing lower-intruder repair actually does

The first obstruction is repaired in the known three-upper proof by lowering
the second pivot by one extra position. For `m>=9`, the relevant forced
branch is:

\[
\begin{array}{c|c|c}
\text{deficit}&\text{exact block}&\text{selected permitted witness}\\
m+4&\{4,m\}&m+3\\
m+3&\{5,m-2\}&m-1\\
m-1&\{2,m-3\}&\text{a remaining upper counter}.
\end{array}
\]

All three displayed sums are exact. After the third block, every remaining
lower counter is at most `m-4`, while the block maximum is `m-3`; hence the
next witness is necessarily upper. The support at this return is

\[
([2,m-4]\setminus\{2,4,5\})\cup[m+5,m+k+2],
\]

before deleting that next upper opening. Thus the repair pays for one lower
intruder by deleting four lower top counters and the small reserve
`{2,4,5}`, while removing the first two upper counters.

This is not closure of the original two-hole family. It widens the gap from
two counters to eight counters and creates three small holes. The other
upper-witness branches at the second exchange have different supports and
must also be handled separately. No shared winning-opening uniqueness is
available across them.

The repeatability issue is explicit: the displayed lower-intruder branch
uses the exact complement `2`. Once `2` is gone, no nonempty subset of the
remaining distinct integers at least `3` can replace that complement.
Repeating this same local repair is therefore invalid. A genuine uniform
induction needs a different lower-intruder subsystem or a proved additional
resource invariant; merely recording the widened gap and the number of
holes does not supply one.

## Scope and handoff

The search did not find a closed parametric replacement. The strongest clean
deliverable is the upper-only obstruction in Section 1, together with the
sharp packing lemma in Section 2 and the exact support transformation in
Section 3. No new exact outcome computations were run. No production Lean
file, report, or other agent's file was changed.
