"""Literal-score replay of the stopped fixed batch's witness and controls."""
from pathlib import Path
import collections
import hashlib
import json
import resource
import sys
import time

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from verify import absolute

P = Path(__file__).resolve().parent
start = time.monotonic()
seeds = json.loads((P/"root_alternating_gap_seeds.json").read_text())
rows = [json.loads(line) for line in (P/"root_alternating_gap_probe.log").read_text().splitlines()]
checkpoint = next(a for a in rows if a["kind"] == "checkpoint")
primary = [a for a in rows if a["kind"] == "primary"]
assert [a["id"] for a in primary] == list(range(1, checkpoint["completed_primary"] + 1))
assert len(primary) + checkpoint["unprocessed_primary"] == len(seeds["cases"]) == 229
seedby = {a["id"]: a for a in seeds["cases"]}
for a in primary:
    s = seedby[a["id"]]
    assert a["support"] == s["E"] and a["T"] == s["T"] and a["deficit"] == 1
    a["provenance"] = s["provenance"]
witnesses = [a for a in primary if a["value"] == -1]
assert len(witnesses) <= 1
witness = witnesses[0] if witnesses else None
assert (witness is not None) == (checkpoint["stop_reason"] == "first_loss")
controlrows = [a for a in rows if a["kind"] == "control"]
controlspec = json.loads((P/"root_alternating_gap_controls.json").read_text())
assert len(controlrows) == len(controlspec) == 8
for row, spec in zip(controlrows, controlspec):
    assert row["id"] == spec["id"] and row["T"] == spec["T"]
    row["control_provenance_label"] = spec["label"]
contexts = [a for a in rows if a["kind"].startswith("witness_")]
literal_complete = False
maxcache = 0
literal_root_count = 0
literal_move_count = 0


def save():
    result = {
        "objective": seeds["objective"],
        "authorized_primary_case_count": 229,
        "completed_primary_case_count": len(primary),
        "unprocessed_primary_cases": seeds["cases"][len(primary):],
        "native_primary_outcome_counts": dict(collections.Counter(a["value"] for a in primary)),
        "native_checkpoint": checkpoint,
        "completed_primary_cases": primary,
        "first_loss": witness,
        "witness_contexts": contexts,
        "eight_control_provenances": controlrows,
        "six_distinct_control_supports": len({tuple(a["T"]) for a in controlrows}),
        "literal_complete": literal_complete,
        "literal_root_replays": literal_root_count,
        "literal_first_pick_replays": literal_move_count,
        "max_literal_cached_states": maxcache,
        "literal_source_sha256": hashlib.sha256((P.parents[1]/"verify.py").read_bytes()).hexdigest(),
        "seconds": time.monotonic() - start,
        "max_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "scope": "Only the approved 229-tail fixed batch, stopped on first loss; witness/controls replay uses no further support. Optional witness contexts are not interval/root counterexamples.",
        "tail_gap_scope": "Alternating ranks imply even-length omissions between adjacent tail labels and from9 to minT. The bridge7 to odd minT has an odd number of omitted labels; full E does not have only even gaps.",
    }
    (P/"root_alternating_gap_results.json").write_text(json.dumps(result, indent=2)+"\n")
    return result


def check(row):
    global maxcache, literal_root_count, literal_move_count
    if time.monotonic()-start >= 25:
        save()
        print("LITERAL_CAP_PARTIAL", literal_root_count, literal_move_count, flush=True)
        raise SystemExit(3)
    S, d = tuple(row["support"]), row["deficit"]
    absolute.cache_clear()
    value = absolute(S, 0, d)
    assert value == row["value"], (row["kind"], row["id"], value, row["value"])
    maxcache = max(maxcache, absolute.cache_info().currsize)
    actualmap = {}
    for x in S:
        C = tuple(z for z in S if z != x)
        # A pick below d leaves the same player active. A catch swaps roles.
        actualmap[str(x)] = absolute(C, x, d) if x < d else -absolute(C, d, x)
        maxcache = max(maxcache, absolute.cache_info().currsize)
    assert actualmap == row["moves"], (row["kind"], row["id"], actualmap, row["moves"])
    assert max(actualmap.values()) == value
    row.update({"literal_root_value": value, "literal_first_pick_map": actualmap,
                "safe_choices": [int(x) for x, v in actualmap.items() if v >= 0],
                "literal_root_and_all_first_picks_pass": True})
    literal_root_count += 1
    literal_move_count += len(S)
    absolute.cache_clear()
    save()
    print("LITERAL_PASS", row["kind"], row["id"], "value", value,
          "all_moves", len(S), "safe", row["safe_choices"], flush=True)


if witness is not None:
    check(witness)
# All eight requested provenance entries are checked, including the two pairs
# that have equal rounded/literal supports. Keep their identities in the log.
for a in controlrows:
    check(a)
    if a["control_provenance_label"] in ("named_old4_rounded", "literal_control4"):
        a["previously_supplied_control_safe_choices"] = [4, 10]
    if a["control_provenance_label"] in ("named_old8_rounded", "literal_control8"):
        a["previously_supplied_control_safe_choices"] = [7, 9, 17]
    if "previously_supplied_control_safe_choices" in a:
        a["previously_supplied_control_set_complete"] = (
            a["safe_choices"] == a["previously_supplied_control_safe_choices"])
for a in contexts:
    check(a)
literal_complete = True
r = save()
print("COMPLETE_LITERAL_WITNESS_CONTROLS_CONTEXTS", "roots", literal_root_count,
      "first_picks", literal_move_count, "seconds", r["seconds"],
      "rss", r["max_rss_bytes"], flush=True)
