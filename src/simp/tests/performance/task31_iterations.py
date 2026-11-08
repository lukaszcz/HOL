#!/usr/bin/env python3
"""The predeclared steady counts of the TASK31 allocation grid.

`python3 task31_iterations.py` writes allocation_iterations_task31.json. The
counts are a policy of the case and the size, never a measurement of the
grid: the same rule for both sides and every pair.

Rule (the TASK30 size rule, cut for the cells whose application is
costly):
  1. steady = 32 for size <= 100, 16 for 1000, 8 for 10000;
  2. the reuse and complete stages of the families in CUT_8 are halved
     once at size 1000 (to 8), and those of CUT_4 twice (to 4), to fit the
     process timeout.
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
# The families whose reuse and complete cells at 1000 assumptions are cut.
CUT_8 = ("full", "reverse", "no_strip_full", "no_strip_reverse",
         "dependency_full", "dependency_reverse")
CUT_4 = ("global", "req0", "reqd", "req0_reqd", "reqd_req0")
CUT_SIZE = 1000
RULE = ("TASK30 size rule (<=100 -> 32, 1000 -> 16, 10000 -> 8); the reuse "
        "and complete stages of the families full, reverse, no_strip_full, "
        "no_strip_reverse, dependency_full and dependency_reverse at 1000 "
        "are halved to 8, those of global, req0, reqd, req0_reqd and "
        "reqd_req0 to 4, to fit the process timeout; fixed before any "
        "matrix observation, identical for both sides, never calibrated")


def family_of(case):
    """The (family, stage) of a tactic case; None for a traversal case."""
    if not case.startswith("tactic_"):
        return None
    body = case[len("tactic_"):]
    for stage in cases.STAGES:
        if body.endswith("_" + stage):
            return body[:-len(stage) - 1], stage
    raise ValueError(case)


def steady(case, size):
    count = 32 if size <= 100 else 16 if size == 1000 else 8
    found = family_of(case)
    if size == CUT_SIZE and found is not None and \
            found[1] in ("reuse", "complete"):
        if found[0] in CUT_8:
            return 8
        if found[0] in CUT_4:
            return 4
    return count


def counts(keys):
    return {"%s-%d" % k: steady(*k) for k in keys}


def document(keys):
    return dict(schema="task29b-iterations-v1", repeats=REPEATS, rule=RULE,
                steady=counts(keys))


def keys_of_task():
    import allocation_matrix as m
    return m.keys(m.TASKS["task31"])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args(argv)
    args.output.write_text(json.dumps(document(keys_of_task()), indent=1,
                                      allow_nan=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
