> **Historical research note, October 2026.** This preserves an earlier result and its
> experimental context. Check formal statements in the current sources linked below;
> a related source link does not certify every numerical observation in this note.
> numerical observations and old checking times describe retained runs, not a fresh replay.
> An old “next step” may have been completed or refuted: consult the [current route guide](../../results/research-routes.md).
> Historical novelty/frontier phrases are not adopted; see the [source guide](../../docs/sources.md).
> Commands and artifact names below refer to the original research layout, not a standalone
> reproduction bundle. Use the [current verification instructions](../../verification/README.md).

Current sources: [current cryptid and component status](../../cryptid/README.md).

# Retired routes in the compatibility/reuse session

1. Directly kernel-reducing `CodeDAG.compile Program.program` to obtain the
   row count and binary length failed: `decide +kernel` could not close the
   kernel reduction, and `rfl` hit recursion depth 32768. Native candidates
   were 204 rows and34815 bits; these were never accepted on native authority.
   We changed representation to a literal204-row table, reused the existing
   proved topology checker, and proved exact source reconstruction by `rfl`.
   Stack length is kernel counted; the codec-length theorem yields bit length.
   This route succeeds without trusting the compiler or evaluating its cache
   in the kernel.

2. Lean4.35 changes to implicit transparency prevented the old `Part.bind`
   simplification proofs from matching. The same compatibility option already
   used by the reused backend, `backward.isDefEq.respectTransparency false`,
   restored elaboration; the last list proof needed `List.nil_append`.
   Other port edits rename deprecated/moved imports, lemmas and tactics.
   `verify.py` rejects any other difference from the frozen old files.

3. Keeping the concrete bit array irreducible while trying to identify two
   separately expanded initializer expressions triggered expensive definitional
   equality and recursion-depth errors. The final machine uses one named bit
   array, proves generated halting before local opacity, and composes symbolic
   count/initialization lemmas after opacity. No semantic definition changed.

4. The first positive-branch fixture reached its200000-step bound. Its source
   semantics predicts termination, so this was recorded as an incomplete run.
   Raising this single fixture's bound to450000 observed halting at228984steps;
   independent physical replay agrees. The loop fixture remains bounded at
   200000steps, with no nonhalting conclusion drawn from that observation.

5. Independent review caught an overly strict whole-checkout HEAD requirement:
   another chat committed unrelated Chess work during verification. All80
   reused sources and320 compiled artifacts were unchanged. The verifier now
   checks the actual Git source blobs at the pinned commit plus content/cache
   hashes, allowing unrelated HEAD changes. The corrected check was replayed
   against the advanced checkout without changing the mathematical inputs.
