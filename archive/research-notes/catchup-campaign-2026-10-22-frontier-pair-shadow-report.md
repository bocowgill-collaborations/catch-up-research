> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [CatchUp.PairEntranceShadow](../../CatchUp/PairEntranceShadow.lean).

# An unbounded reserved-counter shadow contract

Let C be any finite remaining support, let b∉C be a reserved counter, and put
w=b+c. Assume V(C,w)=LOSS. The opponent plays an arbitrary legal complete turn
Y from(insertbC,c), avoidingb, and y=sumY. The actual next position is

    (insert b (C\Y), y−c).

The compiled theorem proves the exact reply rule:

    moveOutcome(b) = LOSS if y=w, and WIN otherwise.

It also proves the actual endpoint is WIN whenever y≠w, with an explicit
catchability check ruling out a hypothetical reply at a terminal node.
The ordered CompletedTurn wrapper covers arbitrary preparation lengths,
not one chosen ordering or a bounded list of cases. Every opponent whole
turn avoidingb is included. No finite |C| or |Y| bound is imposed.

The result is stronger than the requested positive-counter specialization:
it needs neither positivity of C nor0<c<b. Those assumptions were unused and
were removed instead of hidden behind underscore names. It holds for finite
Nat supports and arbitrary naturalb,c under the displayed semantic premises.
Actual positive-counter Catch-Up states are therefore covered unchanged.

## Exact statements

```lean
theorem reserve_reply_outcome
    (C Y : Finset ℕ) (b c final : ℕ) (hb : b ∉ C)
    (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final) (hbY : b ∉ Y) :
    (⟨insert b (C \ Y), Y.sum (fun x ↦ x) - c⟩ : Position).moveOutcome b =
      if Y.sum (fun x ↦ x) = b + c then .loss else .win
```

```lean
theorem reserve_reply_after_completed_turn
    (C : Finset ℕ) (b c final : ℕ) (preparation : List ℕ) (after : GamePosition)
    (hb : b ∉ C) (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (trace : CompletedTurn ⟨⟨insert b C, c⟩, .p1⟩ (preparation ++ [final]) after)
    (hbY : b ∉ insert final preparation.toFinset) :
    after.toPosition.moveOutcome b =
      if (preparation ++ [final]).sum = b + c then .loss else .win
```

The genuine endpoint winning statement is:

```lean
theorem endpoint_win_of_total_ne
    (C Y : Finset ℕ) (b c final : ℕ) (hb : b ∉ C)
    (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final) (hbY : b ∉ Y)
    (hne : Y.sum (fun x ↦ x) ≠ b + c) :
    (⟨insert b (C \ Y), Y.sum (fun x ↦ x) - c⟩ : Position).value = .win
```

The authoritative production file is `CatchUp/PairEntranceShadow.lean`.
No paper/manuscript was edited.

## Mathematical proof and reuse

If y<w, every member of Y belongs to C and the total lies below the shadow
deficit. The existing private `Position.loss_after_erasing_subsum` gives
V(C\Y,w−y)=LOSS when the shadow is catchable. The new helper
`loss_after_subsum` separately handles a terminal shadow: sumC<w implies
sum(C\Y)<w−y, and the reference terminal equation gives LOSS directly.
It never claims that an already terminal shadow executes illegal picks.

The actual deficit is y−c<b. Pickingb therefore catches, swaps perspectives,
and leaves that losing shadow state to the opponent: reply outcome WIN.

If y≥w, Y is a legal completed shadow turn at deficitw. Its actual final
counter is reused; the preparation belowc is also beloww, and singleton
turns are explicitly allowed by TurnSet. From a losing position, every
completed-turn endpoint must be WIN for the new mover. The proof derives
this directly from the existing `value_ne_loss_iff_exists_turn_set`: a
nonwinning endpoint would supply a nonlosing legal turn and contradict LOSS.
No general game-theory framework or duplicate trace induction was added.

For y>w, the actual deficit y−c exceedsb. Pickingb continues without negation
and reaches the shadow winning endpoint at deficity−w. For y=w, the actual
deficit equalsb. Pickingb ties and swaps, so the shadow WIN at deficit0 is
negated to LOSS. This is precisely the equality obstruction observed in the
independent N13 diagnostic.

`reserve_endpoint_eq` identifies the literal actual endpoint, usingb∉Y.
The ordered wrapper uses the existing `CompletedTurn.turn_set`,
`CompletedTurn.after_eq_endpoint`, nodup and sum-to-finset theorems. The
additional winning-endpoint theorem checks reserve availability and total
catchability before applying the reference minimax recursion.

## Checks and costs

From `research/catchup`:

```
lake --wfail build CatchUp.PairEntranceShadow
lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/pair-shadow/audit.lean
lake env lean -DwarningAsError=true campaign_2026_10_22/frontier/pair-shadow/lean/Main.lean
```

All passed. Build6.095seconds;7transitive axiom audits3.948seconds;
import shim3.623seconds. All audited theorems depend only on propext,
Classical.choice,Quot.sound. No placeholder proof, custom axiom, native-only
computation, or external solver answer occurs. This is a uniform symbolic
proof and requires no bounded game computation.

Lean4.27.0/mathliba3a10db0e9d66acbebf76c5e6a135066525ac900 were checked
and preserved. PlatformmacOS26.6.2arm64; exact CPU model is unavailable.
Darwin cumulative child peakRSS across the build/audit/shim sequence was
5,456,986,112bytes, not isolated per-theorem memory. Interactive proof-generation
time was not separately instrumented. Commands, source hash and timing receipts
are retained in `checks.json` and logs. The lean/ folder provides a pinned
path-dependency wrapper/import shim; the existing package is authoritative.

New source8915bytes/192lines,7public theorems,SHA256
`05dd3412e801ad0706a8b6e891f98a6bfa70044017b549165038e189e5dfd97f`.
The local import closure has8files/108727sourcebytes, including99812bytes of
existing support. Mathlib is separately pinned and excluded from that byte
count. This is source accounting, not a serialized kernel-proof size or a
claim of minimality. `dependencies.json` records each local source hash.

## Exact remaining controller obligations

This settles every b-avoiding, non-equality opponent branch uniformly,
including the299 such branches in the saved bounded study. It also explains
why blindb fails at equality. It does not prove a safe alternative at equality,
and says nothing about opponent turns that takeb. It does not justify entering
through the minimum block element, which the saved exact diagnostics refute.
No claim about actual endpoint value is made at equality: it may still draw
or win despite the losingb reply. C,H,and the full nonterminal density claim
remain unresolved. Parent fresh source replay4.323s/seven transitive audits4.019s and independent
source review PASS; see pair_shadow_replay.json and REVIEW.md.
