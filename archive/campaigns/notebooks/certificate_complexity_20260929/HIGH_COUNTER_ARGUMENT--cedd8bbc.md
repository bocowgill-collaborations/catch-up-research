> **Historical campaign record.** This is a sanitized archival version, outside the verified build. Claims of compilation, exact values, novelty and review below describe the original run. Consult the [finding ledger](../../../../results/legacy-findings.md) and current route guide for present assurance; source hashes and all versions are in `verification/legacy-sources.json`. Old commands and CHECK lines are inert historical text.

# Stronger version: track only counters above half the maximum

This refines the same target-set-cover mechanism in ARGUMENT.md. It replaces the
O(sqrt(N)) total-deletion budget by a constant budget for large counters. It does
not claim to solve Catch-Up or to lower-bound mathematical proof length.

**Theorem.** Let N>=16, t be natural, and 12t+2<=N. Every full valid nonloss
certificate from `(I_N,0,p1)`, protecting either player, has at least 2^t nodes.
In particular, conditional on existence,

`D_p(N) >= 2^floor((N-2)/12)`.

Thus the proposed conditional exponential certificate-size conjecture follows,
for example with c=1/24 and N0=28, since floor((N-2)/12)>=N/24 for N>=28.
The statement holds for all N in this range when the relevant certificate exists,
so restricting to the admissible even-total sizes does not weaken it.

## Proof

Let L={floor(N/2)+1,...,N}. Every x in L satisfies 2x>N, and |L|=ceil(N/2).
Reachable deficits are at most N, as proved in the original argument.

1. **Two-large-counter nonterminal criterion.** Any reachable state retaining two
   distinct elements x,z of L has remaining sum at least x+z>N>=deficit. It is
   nonempty and therefore nonterminal. No lower bound on the number or sum of its
   small counters is needed.

2. **Protected-turn large-counter budget.** An uninterrupted completed turn contains
   at most two members of L. Its proper preparation prefix has total strictly below
   the initial deficit (unless empty). Two elements of L already sum to more than
   N, so at most one can lie in the preparation prefix. Its final pick can add at
   most one more. At zero deficit there is only the final pick. Equality ends the
   turn and cannot be followed by another preparation pick.

3. **Entry.** In a p2 certificate, the root is already adversarial. In a p1
   certificate, follow its prescribed opening to the p2 adversary state. Let S0
   be the elements of L still present at that entry, and r0=|S0|. Then
   `r0>=ceil(N/2)-1>=6t`, and r0>=7 for N>=16. This entry is nonterminal.

4. **Force deletion of any t-subset T of S0.** At an adversary node select a
   currently present target. If it is below the deficit, the adversary still moves
   and the macro costs one large counter. If it catches, follow the certificate's
   protected picks through the next switch. By step 2 this costs at most two
   additional large counters. These are actual covered atomic transitions; the
   representation is not being extended with macro leaves.

   Each macro deletes a new target; adaptive protected picks can delete additional
   targets and finish the task sooner. At most t macros delete T, at a cost of
   at most 3t elements of S0 (or of L). Since 6t<=r0, at least ceil(r0/2)>=4
   elements of S0 remain throughout. In particular the two-large-counter criterion
   excludes terminal states at every prefix. To avoid a circular reading, after j
   completed macros and within the next protected turn, at most 3j+1+2<=3t
   large counters have been removed: no uninterrupted prefix can contain three
   large picks, because the second such pick must already have caught. If the
   protected turn used only small counters forever it would violate finite strict
   remaining-cardinality progress; the valid certificate supplies each actual pick.
   Equivalently, use the existing completed-turn existence argument along the
   certificate: a noncatching pick preserves nonterminality, and cardinality strictly
   decreases. The resulting completed turn satisfies step 2.

   Stop at the adversary node after all targets are gone, completing the last
   protected turn if needed. At t=0 take the entry node itself.

5. **Cover count.** Project certificate nodes onto deleted large subsets
   `A=S0\remaining`, retaining those with |A|<=3t. Let C be this family. Each
   t-subset T of S0 is contained in at least one member of C. Therefore

   `binom(r0,t) <= |C| binom(3t,t) <= (#nodes) binom(3t,t)`.

   Since r0>=6t, the falling-factorial comparison gives
   `binom(r0,t)>=2^t binom(3t,t)`. Cancel the positive factor. Distinct histories
   are not counted as distinct states; many targets may merge and are explicitly
   charged against the binomial coverage capacity of the merged node.

All protected moves are those of the arbitrary fixed certificate. The argument
uses neither optimal replies, the Catch-Up conjecture, nor the existence of any
particular uniform strategy. Terminal safety is not needed beyond the full
certificate's correct terminal/branch shape. Small-counter deletion can be huge;
it cannot erase the tracked large counters or make a state terminal while two
such counters remain. This is the specific interval geometry used by the proof.
