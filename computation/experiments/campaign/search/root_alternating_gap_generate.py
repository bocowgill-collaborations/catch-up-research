"""Generate the single authorized alternating-tail batch; no game evaluation."""
from pathlib import Path
import collections
import hashlib
import itertools
import json
import math

P = Path(__file__).resolve().parent
BASE = (18, 33, 35, 36, 52, 56, 62, 74, 100)
SIZES = (3, 4, 7, 8)


def round_tail(original):
    """Coordinatewise least upward strict odd/even/odd/... rounding."""
    original = tuple(original)
    assert list(original) == sorted(set(original))
    out, steps = [], []
    previous = 0
    for i, x in enumerate(original):
        target_parity = 1 if i % 2 == 0 else 0
        q = max(x, previous + 1)
        before_parity_adjustment = q
        q += int(q % 2 != target_parity)
        assert q >= x and q > previous and q % 2 == target_parity
        # The only smaller candidate meeting the lower bounds is q-1,
        # and it has the opposite parity (or is below a lower bound).
        assert q == max(x, previous + 1) or q == max(x, previous + 1) + 1
        steps.append({"rank_zero_based": i, "original": x,
                      "previous_rounded": previous,
                      "strict_lower_bound": previous + 1,
                      "before_parity_adjustment": before_parity_adjustment,
                      "target_parity": target_parity, "rounded": q})
        out.append(q)
        previous = q
    return tuple(out), steps


all_by_tail = {}
raw = []


def add(label, original, do_round, kind, subset_indices=None):
    original = tuple(original)
    tail, steps = round_tail(original) if do_round else (original, [])
    assert len(tail) in SIZES and tail[0] >= 9
    assert list(tail) == sorted(set(tail))
    assert all(x % 2 == (1 if i % 2 == 0 else 0)
               for i, x in enumerate(tail))
    assert sum(tail) % 2 == 0
    E = (4, 7) + tail
    assert len(E) <= 10 and len(E) == len(set(E))
    provenance = {"label": label, "kind": kind,
                  "original_tail": original, "rounding_applied": do_round,
                  "rounded_tail": tail, "steps": steps}
    if subset_indices is not None:
        provenance["base_subset_indices_zero_based"] = subset_indices
    raw.append(provenance)
    all_by_tail.setdefault(tail, []).append(provenance)


for k in SIZES:
    for indices in itertools.combinations(range(len(BASE)), k):
        original = tuple(BASE[i] for i in indices)
        add("base_" + "_".join(map(str, indices)), original, True,
            "base_subset_rounded", indices)

add("named_old4_rounded", (9, 10, 12, 15), True, "named_rounded")
add("named_old8_rounded", (9, 16, 17, 18, 26, 28, 31, 37), True,
    "named_rounded")
add("literal_control4", (9, 10, 13, 16), False, "literal_control")
add("literal_control8", (9, 16, 17, 18, 27, 28, 31, 38), False,
    "literal_control")
for N in (11, 12, 15, 16):
    add(f"interval_9_to_{N}", range(9, N + 1), False, "interval_control")

cases = []
for i, tail in enumerate(sorted(all_by_tail, key=lambda t: (max(t), len(t), sum(t), t)), 1):
    cases.append({"id": i, "T": tail, "E": (4, 7) + tail,
                  "deficit": 1, "sumT": sum(tail),
                  "sort_key": (max(tail), len(tail), sum(tail), tail),
                  "provenance": all_by_tail[tail]})

metadata = {
    "objective": "Seek LOSS in E={4,7} union T at deficit1 for fixed alternating even-sum tails; stop at first LOSS; no uniform inference from a pass",
    "predicate": "T strictly increasing, minT>=9, odd/even/odd/... rank parity, Even(sumT)",
    "rounding_encoding": "q=max(original[i],previous_rounded+1); q+=int(q%2 != (1 if i%2==0 else 0))",
    "base_tail": BASE, "subset_sizes": SIZES,
    "raw_base_seed_count": sum(math.comb(9, k) for k in SIZES),
    "raw_seed_count_including_controls": len(raw),
    "raw_base_counts_by_size": {k: math.comb(9, k) for k in SIZES},
    "unique_case_count": len(cases),
    "unique_counts_by_size": dict(collections.Counter(len(a["T"]) for a in cases)),
    "unique_base_rounded_count": len({tuple(x["rounded_tail"]) for x in raw if x["kind"] == "base_subset_rounded"}),
    "deduplicated_provenance_count": len(raw)-len(cases),
    "controls": [x for x in raw if x["kind"] != "base_subset_rounded"],
    "sort": "(maxT, cardT, sumT, T lexicographic)",
    "primary_E_max_labels": max(len(a["E"]) for a in cases),
    "max_actual_label": max(max(a["E"]) for a in cases),
    "arithmetic_assertions_passed": True,
    "solver_execution_authorized_after_encoding_approval_only": True,
    "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "frozen_sources_sha256": {
        str(f.relative_to(P.parents[3])): hashlib.sha256(f.read_bytes()).hexdigest()
        for f in (P.parents[1]/"seven_pairs"/"slots.hpp", P.parents[1]/"verify.py")},
    "cases": cases,
}
(P/"root_alternating_gap_seeds.json").write_text(json.dumps(metadata, indent=2)+"\n")
(P/"root_alternating_gap_seeds.txt").write_text("".join(
    f"{a['id']} {len(a['T'])} " + " ".join(map(str, a['T'])) + "\n" for a in cases))
print(json.dumps({k: v for k, v in metadata.items() if k not in ("cases", "controls")}, indent=2))
print("NAMED_AND_INTERVAL_CONTROL_PROVENANCE", json.dumps(metadata["controls"]))
