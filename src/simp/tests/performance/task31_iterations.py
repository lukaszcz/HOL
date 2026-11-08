#!/usr/bin/env python3
"""The predeclared steady counts of the TASK31 allocation grid, and what the
grid costs.

`python3 task31_iterations.py` writes allocation_iterations_task31.json;
`--estimate` prints the projected wall time. The counts are fixed from the
case, the size and the per-operation costs of the baseline cost survey
(OPERATION below), never from a measurement of the grid: the same rule for
both sides and every pair.

Rule (the TASK30 size rule, bounded by the cost of the operation):
  1. steady = 32 for size <= 100, 16 for 1000, 8 for 10000;
  2. halve it while steady x repeats x (seconds of one operation) exceeds
     BUDGET, down to MINIMUM.
Only the heavy tactic cells at 1000 and the asm cells at 10000 are cut: one
operation of the other cells is under 10 ms.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import task31_cases as cases

OUTPUT = HERE / "allocation_iterations_task31.json"
REPEATS = 4
BUDGET = 100.0   # seconds of steady operations in one process, at most
MINIMUM = 4
RULE = ("TASK30 size rule (<=100 -> 32, 1000 -> 16, 10000 -> 8), halved "
        "down to 4 while steady x repeats x the seconds of one operation "
        "exceeds 100; operation costs from the baseline cost survey; fixed "
        "before any matrix observation, identical for both sides, never "
        "calibrated")

# Seconds of one reuse/complete application (the apply of a tactic, a
# conversion call) at the baseline, from the cost survey (q1_table.md: the
# timed operation); a construct cell's operation is a constant 0.03-2000 us
# and its apply (verify, the work phase's use) costs the same as the family's
# reuse. Families and sizes not listed cost under 10 ms.
APPLY = {
    ("supplied", 1000): 0.004, ("supplied", 10000): 0.39,
    ("installed", 1000): 0.004, ("installed", 10000): 0.39,
    ("asm", 1000): 0.011, ("asm", 10000): 0.95,
    ("full", 1000): 2.1, ("reverse", 1000): 2.2,
    ("no_strip_full", 1000): 2.0, ("no_strip_reverse", 1000): 2.2,
    ("global", 1000): 5.6, ("req0", 1000): 5.6, ("reqd", 1000): 5.6,
    ("req0_reqd", 1000): 5.7, ("reqd_req0", 1000): 5.7,
    ("dependency_full", 1000): 1.9, ("dependency_reverse", 1000): 2.2}
# Seconds of a process before its workload: the compile of the private
# closure and the shared heap (the survey's 17-26 s for a trivial cell).
STARTUP = 22.0
JOBS = 8
PROCESSES = 40   # 10 pairs x 2 experiments x 2 sides


def family_of(case):
    """The (family, stage) of a tactic case; None for a traversal case."""
    if not case.startswith("tactic_"):
        return None
    body = case[len("tactic_"):]
    for stage in cases.STAGES:
        if body.endswith("_" + stage):
            return body[:-len(stage) - 1], stage
    raise ValueError(case)


def apply_cost(case, size):
    found = family_of(case)
    return 0.0 if found is None else APPLY.get((found[0], size), 0.0)


def steady(case, size):
    count = 32 if size <= 100 else 16 if size == 1000 else 8
    operation = apply_cost(case, size) if case.endswith(
        ("_reuse", "_complete")) else 0.0
    while count > MINIMUM and count * REPEATS * operation > BUDGET:
        count //= 2
    return count


def process_seconds(case, size, count):
    """Model of one process: startup, the setup (one apply, two for a
    construct stage), the operations (first, steady, and the work phase's
    two runs and use) and the verification."""
    apply, stage = apply_cost(case, size), (family_of(case) or ("", ""))[1]
    if stage == "construct":
        return STARTUP + 4 * apply
    return STARTUP + (5 + REPEATS * count) * apply if apply else STARTUP


def counts(keys):
    return {"%s-%d" % k: steady(*k) for k in keys}


def document(keys):
    return dict(schema="task29b-iterations-v1", repeats=REPEATS, rule=RULE,
                steady=counts(keys))


def estimate(keys):
    """Hours of the full grid: the processes of every cell, JOBS at a time
    (perfect scaling; the smoke's wall per process refines STARTUP)."""
    total = sum(PROCESSES * process_seconds(c, n, steady(c, n))
                for c, n in keys)
    return total / JOBS / 3600.0


def keys_of_task():
    import allocation_matrix as m
    return m.keys(m.TASKS["task31"])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--estimate", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args(argv)
    keys = keys_of_task()
    if args.estimate:
        print("%d cells, %.1f hours" % (len(keys), estimate(keys)))
        return 0
    args.output.write_text(
        json.dumps(document(keys), indent=1, allow_nan=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
