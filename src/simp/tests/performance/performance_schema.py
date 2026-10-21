"""Complete performance protocol; process/path checks live in run_paired."""
import math

LABELS = (
    "rewrites_1000", "merge_frags_1000", "compile_1000",
    "delete_missing_1000", "project_1000", "construct_traverse_1000",
    "empty_add_1000", "simp_installed_1000", "raw_reuse_1000",
    "projection_apply_1000", "compile_apply_1000",
)
CONSUMED = dict.fromkeys(LABELS, 1)
CONSUMED.update(rewrites_1000=1000, merge_frags_1000=1000, compile_1000=2,
                delete_missing_1000=2, empty_add_1000=3)
FIELDS = ("wall", "nongc_usr", "nongc_sys", "gc_usr", "gc_sys",
          "cpu_usr", "cpu_sys", "check_gc_user", "consumed")
STORAGE = ("rules", "base", "fragment", "simpset", "anchor", "union",
           "compiled_increment", "historical_increment", "fragment_anchor",
           "fragment_union", "fragment_increment")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def numbers(value, count):
    fields = value.split(",")
    require(len(fields) == count, "wrong metric arity")
    # SML writes negative exponents with ~ rather than -.
    result = [float(v.replace("~", "-")) for v in fields]
    require(all(math.isfinite(v) and v >= 0 for v in result),
            "invalid/nonfinite/negative metric")
    return result


def timing(value, prefix=0):
    data = numbers(value, len(FIELDS) + prefix)
    ts = dict(zip(FIELDS, data[prefix:]))
    for key in ("usr", "sys"):
        difference = ts["cpu_" + key] - ts["nongc_" + key] - ts["gc_" + key]
        require(-0.00001 <= difference < 0.02, "CPU accounting mismatch")
    require(abs(ts["check_gc_user"] - ts["gc_usr"]) < 0.02,
            "GC accounting mismatch")
    require(ts["wall"] > 0 and ts["consumed"] > 0 and
            ts["consumed"].is_integer(), "unconsumed result or empty batch")
    ts["cpu"] = ts["cpu_usr"] + ts["cpu_sys"]
    ts["gc"] = ts["gc_usr"] + ts["gc_sys"]
    return data[:prefix], ts


def validate(events, samples, seconds):
    es = [e for e in events if e[0] in ("observation", "check", "exception")]
    index = 0

    def take(kind, key, value=None):
        nonlocal index
        require(index < len(es), "incomplete performance observations")
        e = es[index]
        index += 1
        require(len(e) == 3 and e[:2] == [kind, key] and
                (value is None or e[2] == value),
                "wrong ordered performance event: " + repr(e))
        return e[2]

    _, accounting = timing(take("observation", "timer.accounting"))
    require(accounting["gc_usr"] > 0, "GC control did not exercise GC")
    require(accounting["consumed"] == 5, "wrong GC control consumption")
    total_consumed = accounting["consumed"]
    take("check", "timer accounting", "pass")
    take("check", "workload inputs", "pass")
    storage = []
    for n in (0, 10, 100, 1000):
        data = numbers(take("observation", "storage"), len(STORAGE))
        require(all(v.is_integer() for v in data), "fractional graph words")
        row = dict(zip(STORAGE, map(int, data)))
        require(row["rules"] == n and
                row["union"] - row["anchor"] == row["compiled_increment"] and
                row["fragment_union"] - row["fragment_anchor"] ==
                row["fragment_increment"], "invalid storage subtraction")
        storage.append(row)
        take("check", "retained graphs", "pass")
    workloads = {}
    for label in LABELS:
        calibrations = []
        n = 1
        while True:
            value = take("observation", "calibration." + label)
            (actual,), ts = timing(value, 1)
            require(actual == n, "non-doubling calibration")
            require(ts["consumed"] == CONSUMED[label] * n,
                    "wrong calibration result consumption")
            total_consumed += ts["consumed"]
            calibrations.append(dict(iterations=n, **ts))
            if ts["wall"] >= seconds:
                break
            n *= 2
            require(n <= 1073741824, "unbounded calibration")
        batches = []
        for i in range(samples):
            value = take("observation", "batch." + label)
            (sample, actual), ts = timing(value, 2)
            require(sample == i and actual == n, "wrong batch index/count")
            require(ts["consumed"] == CONSUMED[label] * n,
                    "wrong batch result consumption")
            total_consumed += ts["consumed"]
            require(ts["wall"] >= seconds / 2, "batch too short; recalibrate")
            batches.append(dict(sample=i, iterations=n, **ts))
            take("check", "results " + label, "pass")
        workloads[label] = dict(calibration=calibrations, batches=batches)
    sink, = numbers(take("observation", "sink"), 1)
    require(sink == total_consumed and sink.is_integer(),
            "missing/inconsistent sink consumption")
    require(index == len(es), "extra performance observation/exception")
    return es, dict(timer_accounting=accounting, storage=storage,
                    workloads=workloads, sink=int(sink))
