"""Account for all128 deletions of the one fixed witness; no game queries."""
from pathlib import Path
import collections
import hashlib
import json

P = Path(__file__).resolve().parent
T0 = (19, 36, 37, 52, 57, 62, 101)
source = P/"root_alternating_gap_results.json"
old = json.loads(source.read_text())
assert tuple(old["first_loss"]["T"]) == T0
assert old["first_loss"]["literal_root_and_all_first_picks_pass"]
assert old["first_loss"]["value"] == -1
records = []
for mask in range(1 << len(T0)):
    T = tuple(x for i, x in enumerate(T0) if mask & (1 << i))
    failures = []
    if not T:
        failures.append("empty_tail")
    if T and min(T) < 9:
        failures.append("minimum_below9")
    if list(T) != sorted(set(T)):
        failures.append("not_strictly_sorted")
    mismatches = [i for i, x in enumerate(T)
                  if x % 2 != (1 if i % 2 == 0 else 0)]
    if mismatches:
        failures.append("rank_parity_mismatch")
    if sum(T) % 2:
        failures.append("odd_tail_sum")
    records.append({"deletion_mask": mask,
                    "retained_original_indices_zero_based": [i for i in range(len(T0)) if mask & (1 << i)],
                    "T": T, "E": (4, 7) + T, "deficit": 1,
                    "sumT": sum(T), "admissible": not failures,
                    "predicate_failures": failures,
                    "rank_parity_mismatches_zero_based": mismatches,
                    "objective_key": (len(T), max(T, default=0), sum(T), T),
                    "query_status": "awaiting_schedule_approval" if not failures else "predicate_skip"})
admissible = sorted((a for a in records if a["admissible"]), key=lambda a: a["objective_key"])
result = {
    "scope": "Fixed128 deletion subsets of literal-confirmed T0 only; generator performs no game queries",
    "T0": T0,
    "predicate": "nonempty,min>=9,strictly increasing,rank parities odd/even startingodd,Even(sumT)",
    "source": str(source), "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "total_deletion_subsets": len(records),
    "admissible_count": len(admissible),
    "admissible_counts_by_cardinality": dict(collections.Counter(len(a["T"]) for a in admissible)),
    "predicate_skip_count": sum(not a["admissible"] for a in records),
    "failure_reason_counts_nonexclusive": dict(collections.Counter(z for a in records for z in a["predicate_failures"])),
    "objective_order": "(cardT,maxT,sumT,T lexicographic)",
    "ordered_admissible_masks": [a["deletion_mask"] for a in admissible],
    "phase1_game_query_schedule": "pending parent approval; none executed",
    "records": records,
    "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
assert len(records) == 128
(P/"root_alternating_gap_shrink_seeds.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({k: v for k, v in result.items() if k != "records"}, indent=2))
print("ADMISSIBLE_TAILS", json.dumps([a["T"] for a in admissible]))
