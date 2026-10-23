# Retained finite certificate artifacts

These three JSON files preserve the search serialization behind the corresponding kernel-checked Lean instances:

| Artifact | Bytes | Nodes | Checked Lean instance |
| --- | ---: | ---: | --- |
| [Near-deficit guard](near-deficit-guard.json) | 42,400 | 72 | [NearDeficitGuardObstruction](../../CatchUp/NearDeficitGuardObstruction.lean) |
| [Unit guard](unit-guard.json) | 128,926 | 219 | [UnitGuardObstruction](../../CatchUp/UnitGuardObstruction.lean) |
| [Odd-pair root](odd-pair-root.json) | 71,174 | 121 | [OddPairRootObstruction](../../CatchUp/OddPairRootObstruction.lean) |

Each node records its remaining support, deficit, ternary value, and child edges. The cutoff is seven counters. Small leaves are solved directly in the Lean proof; selected earlier checked nodes can be reused by name. Above the cutoff, the emitted proof supplies the necessary witnessing choices or all adversarial replies, with a strictly decreasing remaining-cardinality dependency.

The JSON is an archival **untrusted search artifact**. Fields such as `literal_leaf_pass` do not establish truth. Lean does not automatically import these files: the linked modules contain the actual proof declarations and kernel computations. Rebuilding those modules checks the mathematical claims. The hashes bind the retained serializations, not a general theorem about accepting arbitrary JSON certificates.

Certificate serialization size, Lean proof-source size and the full supporting library are different quantities. [Benchmarks](../../verification/benchmarks.json) record selected measurements and their scope. The small emission timings exclude the earlier game search.
