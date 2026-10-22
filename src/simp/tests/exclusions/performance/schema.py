"""Strict TASK17 fixed-schedule protocol on maintained path isolation."""
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
SIZES = (0, 10, 1000, 10000)
LABELS = ("empty_list", "missing", "matching", "batched", "qualified",
          "partial", "literal_namespace", "literal_exact", "dproc_only",
          "mixed", "replay")
KEYS = tuple(f"{label}.{n}" for n in SIZES for label in LABELS)
EVIDENCE = "TASK17-exclusion-performance-v1"
METRICS = ("cpu", "wall", "nongc_cpu", "gc_cpu", "user_cpu", "system_cpu")


def fixed_iterations(values):
    require(isinstance(values, dict) and set(values) == set(KEYS),
            "schedule must contain exactly all 44 workload keys")
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


def timing(text, samples, fixed):
    return timing_events(fragments.payload(text), samples, fixed)


def timing_events(events, samples, fixed):
    fixed = fixed_iterations(fixed)
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
            count = fixed[key]
            rows = []
            for phase, i in [("calibration", 0)] + [
                    ("batch", i) for i in range(samples)]:
                fields = take(["observation", phase + "." + key])[2].split(",")
                prefix = [i, count] if phase == "batch" else [count]
                require(integers(",".join(fields[:len(prefix)]), len(prefix))
                        == prefix, "wrong sample/count")
                row = metrics(fields[len(prefix):], count)
                callbacks = take(["observation", "callbacks." + phase +
                                  "." + key])[2]
                require(integers(callbacks, 2) ==
                        ([n*count, count] if label == "replay" else [0, 0]),
                        "wrong maker/collector counts")
                take(["check", phase + " results " + key, "pass"])
                if phase == "batch":
                    rows.append(row)
            results[key] = rows
    require(take(["observation", "sink"])[2] == str(total), "wrong total sink")
    take(["observation", "complete", EVIDENCE])
    require(cursor == len(events), "extra timing events")
    return events, results
