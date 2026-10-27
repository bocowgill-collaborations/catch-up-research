# Structural ports: provenance and verification

Port date: 27 October 2026. Base: `166cb5f453f074fa87789756d5244a2dfbf22929`.
The [manifest](structural-ports.json) pins each archived source by source ID,
original path, Git blob, observed commit and SHA-256, together with its adapted
fingerprint and exact public theorem inventory. The
[result guide](../results/structural-descent.md) explains statements and remaining gaps.

| Module | Public theorems | Adapted dependency |
| --- | --- | --- |
| [EffectiveTotalDescent](../CatchUp/EffectiveTotalDescent.lean) | 5 | `CatchUp.Reference` |
| [DenseLossInjection](../CatchUp/DenseLossInjection.lean) | 4 | `CatchUp.ExactSumLossObstruction` |
| [PrefixBlockedDenseEndpoints](../CatchUp/PrefixBlockedDenseEndpoints.lean) | 6 | `CatchUp.DenseLossInjection` |
| [LowerRayInteriorReduction](../CatchUp/LowerRayInteriorReduction.lean) | 3 | `CatchUp.Earlier.DeficitWinningBound`, `CatchUp.Earlier.LowerRayExactDeficit` |

Only five import-reference mappings and removal of repository `category`/AMS
indexing attributes are permitted. All mathematical hypotheses, definitions,
statements, proofs and original docstrings remain verbatim. The
[reconstruction checker](../scripts/check_structural_ports.py) rejects changed
contracts and proofs, a weakened positive-deficit premise and replacement of
the required first-pair draw with mere nonloss. It is included in collection CI.
All 18 public theorem declarations are named transitive-axiom endpoints; the
default library now has 114 cataloged mathematics modules.

## Reproduce

With the pinned Lean 4.27.0 dependencies available, from the repository root:

```sh
lake --wfail build CatchUp.EffectiveTotalDescent CatchUp.DenseLossInjection CatchUp.PrefixBlockedDenseEndpoints CatchUp.LowerRayInteriorReduction
lake --wfail build CatchUp
python3 scripts/check_structural_ports.py
python3 scripts/check_axioms.py
python3 scripts/check_collection.py
python3 computation/check_semantics.py
python3 scripts/check_controller_policy.py --lean
lake env lean -DwarningAsError=true --run computation/CheckEarlier.lean
```

[structural-checks.json](structural-checks.json) records the checks actually run,
exit codes, timings, source hashes, log fingerprints, the full mathematics axiom
audit and preservation comparison. The only permitted transitive axioms are
`propext`, `Classical.choice` and `Quot.sound`; a deliberate `sorryAx` control
must fail. The full public theorem count includes generated declarations and
is not a count of distinct new mathematical results.

No existing proof module, original report, archived source/certificate, reference
rule, dependency pin or old receipt is changed. The new manifest and receipt
supplement the historical evidence. The cryptid package is unchanged and is not
rebuilt locally for this port batch. No expanded outcome tables or new search
was needed. Hosted CI has its own results, separate from local checks.

The mathematical audit is a constructive and hostile self-review, not a new
independent human review. Strict descent is arithmetic, the dense-loss results
retain their density/parity bounds and losing-parent hypotheses, and interval
closure remains conditional on first-pair draw and every interior/boundary
obligation. None of the four modules assumes the general conjecture.
