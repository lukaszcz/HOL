"""TASK29B decision rule over exact allocation counts; no allowance.

Per cell, phase and metric: if the baseline/baseline control is not exactly
identical across all processes the result is inconclusive; otherwise pass if
every paired candidate-minus-baseline difference is <= 0, else fail. The
control is the baseline of every candidate pair together with both sides of
the baseline/baseline pairs, so a drifting baseline cannot hide in the pairs.
Adjacent per-rule slopes and size-zero constants follow the same rule.
Nothing is removed, thresholded or subtracted. startup, empty and canary are
published only (the canary is checked exactly by the protocol parser).
Counts are words; the same distinct values are also published as bytes.
"""
from collections import Counter

import allocation_schema as s

GATED = s.PHASES


def series(observations, phase, metric):
    """Per-process lists of per-run exact values, one entry per repeat."""
    return [[s.per_run(phase, d[metric], o["steady"])
             for d in o["phases"][phase]] for o in observations]


def distinct(values):
    return {str(k): n for k, n in sorted(Counter(values).items())}


def distinct_bytes(values):
    return distinct(s.to_bytes(v) for v in values)


def identical(rows):
    """Repeat by repeat, across all processes: exactly one value each."""
    return all(len({row[k] for row in rows}) == 1
               for k in range(len(rows[0])))


def control_identical(pairs, control, phase, metric):
    """Baseline of the candidate pairs and both sides of the baseline/
    baseline pairs, every process, repeat by repeat: exactly one value."""
    rows = (series([p["baseline"] for p in pairs], phase, metric) +
            [row for side in ("baseline", "control")
             for row in series([p[side] for p in control], phase, metric)])
    return identical(rows)


def decide(identical, differences):
    if not identical:
        return "inconclusive"
    return "pass" if all(d <= 0 for d in differences) else "fail"


def cell(pairs, control, steady):
    """pairs/control: lists of {side: observation}; returns the cell record.

    candidate pairs have sides baseline/candidate, control pairs
    baseline/control (the same baseline sources in a second directory)."""
    s.require(len(pairs) >= 2 and len(pairs) == len(control),
              "need an AB and a BA pair in each experiment")
    s.require(all(o["steady"] == steady for p in pairs + control
                  for o in p.values()), "wrong steady count")
    out = dict(phases={}, published={})
    for phase in GATED:
        out["phases"][phase] = {}
        for metric in s.METRICS:
            base = series([p["baseline"] for p in pairs], phase, metric)
            cand = series([p["candidate"] for p in pairs], phase, metric)
            diffs = [c - b for bs, cs in zip(base, cand)
                     for b, c in zip(bs, cs)]
            same = control_identical(pairs, control, phase, metric)
            ctrl = [v for p in control for side in p.values()
                    for v in series([side], phase, metric)[0]]
            out["phases"][phase][metric] = dict(
                decision=decide(same, diffs),
                control_identical=same,
                baseline=distinct(v for r in base for v in r),
                candidate=distinct(v for r in cand for v in r),
                control=distinct(ctrl),
                difference=distinct(diffs),
                bytes=dict(
                    baseline=distinct_bytes(v for r in base for v in r),
                    candidate=distinct_bytes(v for r in cand for v in r),
                    control=distinct_bytes(ctrl)),
                # Per repeat index across processes: steady repeats that
                # differ from each other but reproduce are not nondeterminism.
                deterministic=dict(baseline=identical(base),
                                   candidate=identical(cand)))
    for phase in s.PUBLISHED:
        out["published"][phase] = {}
        for metric in s.METRICS:
            base = [p["baseline"]["phases"][phase][0][metric] for p in pairs]
            cand = [p["candidate"]["phases"][phase][0][metric] for p in pairs]
            ctrl = [side["phases"][phase][0][metric] for p in control
                    for side in p.values()]
            by = [p["control"]["phases"][phase][0][metric] -
                  p["baseline"]["phases"][phase][0][metric] for p in control]
            out["published"][phase][metric] = dict(
                baseline=distinct(base), candidate=distinct(cand),
                control=distinct(ctrl),
                # Candidate minus baseline, and the control's copy minus
                # its baseline, per pair: published, never subtracted.
                difference=distinct(c - b for b, c in zip(base, cand)),
                control_difference=distinct(by),
                bytes=dict(baseline=distinct_bytes(base),
                           candidate=distinct_bytes(cand),
                           control=distinct_bytes(ctrl)))
    return out


def flat(observations, phase, metric):
    """Fixed (process, repeat) layout shared by every size of one case."""
    return [v for row in series(observations, phase, metric) for v in row]


def slopes(case_cells, sizes, data):
    """Adjacent per-rule slopes as exact rationals, both sides.

    case_cells: {size: cell record}; data: {size: (pairs, control)}.
    Process j of one size is compared with process j of the next."""
    result = {}
    for phase in GATED:
        for metric in s.METRICS:
            rows = []
            for lo, hi in zip(sizes, sizes[1:]):
                span = hi - lo
                rate = {}
                for side in ("baseline", "candidate"):
                    a = flat([p[side] for p in data[lo][0]], phase, metric)
                    b = flat([p[side] for p in data[hi][0]], phase, metric)
                    s.require(len(a) == len(b), "mismatched repeat layout")
                    rate[side] = [(y - x) / span for x, y in zip(a, b)]
                same = all(case_cells[n]["phases"][phase][metric]
                           ["control_identical"] for n in (lo, hi))
                diffs = [c - b for b, c in zip(rate["baseline"],
                                               rate["candidate"])]
                rows.append(dict(
                    sizes=[lo, hi], decision=decide(same, diffs),
                    control_identical=same,
                    baseline=distinct(rate["baseline"]),
                    candidate=distinct(rate["candidate"])))
            result.setdefault(phase, {})[metric] = rows
    return result


def constants(case_cells):
    """Size-zero constants: the size-0 cell decisions, both sides."""
    zero = case_cells[0]["phases"]
    return {phase: {metric: dict(
        decision=zero[phase][metric]["decision"],
        baseline=zero[phase][metric]["baseline"],
        candidate=zero[phase][metric]["candidate"])
        for metric in s.METRICS} for phase in GATED}


def status(decisions):
    values = set(decisions)
    return ("fail" if "fail" in values else
            "pass" if values == {"pass"} else "inconclusive")


def case_decisions(record):
    """All gate decisions of one case record (cells and slopes)."""
    found = []
    for c in record["cells"].values():
        for phase in c["phases"].values():
            found += [m["decision"] for m in phase.values()]
    for phase in record["slopes"].values():
        for rows in phase.values():
            found += [r["decision"] for r in rows]
    return found
