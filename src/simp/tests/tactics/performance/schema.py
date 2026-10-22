"""Strict TASK18 stage protocol on maintained source/path isolation."""
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
TESTS = HERE.parents[1]
_old_path = list(sys.path)
sys.path.insert(0, str(TESTS / "fragments"))
import run_fragments as fragments
sys.path[:] = _old_path
paired = fragments.paired
require = paired.require
SIZES = (0, 8)
OPERATIONS = ("simp", "asm", "full", "rev", "no_strip_full",
              "no_strip_rev", "global", "global_req", "conv", "rule", "asm_rule")
STAGES = ("construct", "reuse", "complete")
LABELS = tuple(op + "_" + stage for op in OPERATIONS for stage in STAGES)
KEYS = tuple(f"{label}.{n}" for n in SIZES for label in LABELS)
EVIDENCE = "TASK18-tactic-performance-v1"
METRICS = ("cpu", "wall", "nongc_cpu", "gc_cpu", "user_cpu", "system_cpu")


def fixed_iterations(values):
    require(isinstance(values, dict) and set(values) == set(KEYS),
            "schedule must contain exactly all 66 workload keys")
    require(all(type(v) is int and 0 < v <= 1073741824
                for v in values.values()), "invalid fixed iteration count")
    return {key: values[key] for key in KEYS}


def unique(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def load_fixed(path):
    raw = path.read_bytes()
    return (fixed_iterations(json.loads(raw, object_pairs_hook=unique)),
            dict(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest()))


def selected_keys(keys=None):
    if keys is None:
        return KEYS
    require(isinstance(keys, (list, tuple)) and len(keys) > 0 and
            len(keys) == len(set(keys)) and all(k in KEYS for k in keys),
            "invalid row filter")
    require(tuple(keys) == tuple(k for k in KEYS if k in keys),
            "row filter must preserve matrix order")
    return tuple(keys)


def timing(text, samples, fixed, keys=None):
    return timing_events(fragments.payload(text), samples, fixed, keys)


def timing_events(events, samples, fixed, keys=None):
    fixed = fixed_iterations(fixed)
    keys = selected_keys(keys)
    require(type(samples) is int and samples >= 3, "at least three samples")
    cursor, total = 0, 0

    def take(prefix):
        nonlocal cursor
        require(cursor < len(events), "missing timing event")
        event = events[cursor]
        require(event[:len(prefix)] == prefix and len(event) == 3,
                "wrong ordered timing event: " + repr(prefix))
        cursor += 1
        return event

    def integers(text, n):
        return fragments.integers(text, n)

    def metrics(fields, count):
        nonlocal total
        require(len(fields) == 9, "wrong metric arity")
        try:
            raw = [float(v.replace("~", "-")) for v in fields[:8]]
        except ValueError as exc:
            raise paired.InvalidRun("invalid timing metric") from exc
        require(all(math.isfinite(v) and v >= 0 for v in raw) and
                raw[0] > 0, "invalid timing metric")
        require(integers(fields[-1], 1) == [count], "unconsumed result")
        total += count
        wall, usr, sys_, gu, gs, cu, cs, gc = raw
        require(abs(cu - usr - gu) < .02 and abs(cs - sys_ - gs) < .02
                and abs(gc - gu) < .02, "invalid timer accounting")
        return dict(wall=wall/count, cpu=(usr+sys_+gu+gs)/count,
                    nongc_cpu=(usr+sys_)/count, gc_cpu=(gu+gs)/count,
                    user_cpu=(usr+gu)/count, system_cpu=(sys_+gs)/count,
                    iterations=count, raw=raw)

    metrics(take(["observation", "timer.accounting"])[2].split(","), 5)
    take(["check", "timer accounting", "pass"])
    results = {}
    for n in SIZES:
        for label in LABELS:
            key = f"{label}.{n}"
            if key not in keys:
                continue
            count = fixed[key]
            rows = []
            for phase, i in [("calibration", 0)] + [
                    ("batch", i) for i in range(samples)]:
                fields = take(["observation", phase + "." + key])[2].split(",")
                prefix = [i, count] if phase == "batch" else [count]
                require(integers(",".join(fields[:len(prefix)]), len(prefix))
                        == prefix, "wrong sample/count")
                row = metrics(fields[len(prefix):], count)
                stages = take(["observation", "stages." + phase + "." + key])[2]
                stage = label.rsplit("_", 1)[1]
                require(integers(stages, 3) ==
                        {"construct": [count, 0, 0],
                         "reuse": [0, count, count],
                         "complete": [count, count, count]}[stage],
                        "wrong construction/application/validation counts")
                take(["check", phase + " results " + key, "pass"])
                if phase == "batch":
                    rows.append(row)
            results[key] = rows
    require(take(["observation", "sink"])[2] == str(total), "wrong total sink")
    take(["observation", "complete", EVIDENCE])
    require(cursor == len(events), "extra timing events")
    return events, results
