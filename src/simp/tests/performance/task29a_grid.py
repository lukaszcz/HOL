#!/usr/bin/env python3
"""TASK29A full-grid rerun under the equivalence policy.

The policy owner replaced the superiority gate (upper CI <= 1) by a 3%
equivalence margin on inclusive CPU and wall; GC is reported, not gated
(acceptance.EQUIVALENCE_POLICY). task29_gate.py and its archives stay
unchanged so the historical grid still replays under its own policy.

Every process in a cell runs the same predeclared batch count. Counts come
from develop-only processes of the historical grid, before any new
candidate observation, so neither side can select its own count.

The grid itself (timing_grid.py) is shared with other tasks. This module is
the TASK29A table, the earlier code seals its recorded runs need, and
the policy owner's disposition of its two-stage result. Its functions
delegate to the shared engine and keep the names the TASK29A tests and
archives use.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task29_gate as gate
import timing_grid as tg
# Re-exported: the TASK29A tests and the disposition name them here.
from timing_grid import CONTROL, MAX_PAIRS, TARGET

# The protocol minimum is ten pairs and three samples. On a shared host the
# per-pair spread needs more of both to resolve a 3% margin; the chosen
# values are fixed on the command line and recorded before any cell runs.
PAIRS, SAMPLES = 10, 3
# Calibration targets 0.3 s on a loaded host. Doubling the largest develop
# count keeps a quieter rerun above the driver's own wall-time floor.
HEADROOM = 2
COUNTS = a.HERE / "task29a_iterations.json"
# Earlier drivers whose runs still replay: 6f62229c0 (before canonical
# comparison and replay --partial), 224219893 (before --layout-seed) and
# 3ef5b380b (before --resume and the second stage), cb71be0ce (before
# resume across a changed driver or acceptance) and 9ee8d00bd (before
# dispose).
DRIVERS = [dict(bytes=12534, sha256="234da42ca599122645b9f578b1ddd37c"
                                    "6ffb70d83764d6e91e045ac4ffc4bd97"),
           dict(bytes=13917, sha256="664c632deb187a1ea9c3b59445676253"
                                    "c0872627884b2f664b0626da43d817ee"),
           dict(bytes=14854, sha256="ad4c81fb5b22fc8a5878bebcc5081dee"
                                    "c28a2b67d0b350b9cb34a857d13a787c"),
           dict(bytes=22914, sha256="dd16fa8da12bf1b9f9c3fe9f41037a9a"
                                    "5f1eee263973a9ced20d0159a681c927"),
           dict(bytes=24168, sha256="75d3e9df941a47f6a742eb57d8e8543f"
                                    "c9ad42053cf05e34e9dddfebd0387e8e")]
# acceptance.py before --layout-seed; runs without a seed analyze the same.
ACCEPTANCE = [dict(bytes=37287, sha256="343dfc5d009e8851f0db990bc484bdb2"
                                       "ed1dce3e85efac2416b1335854080b97")]
# acceptance.py with --layout-seed but its lock still in /tmp (3ef5b380b).
LAYOUT_ACCEPTANCE = [dict(bytes=37709,
                          sha256="ad4a4392e24295fff3901b3540115f86"
                                 "86e72d24f08826220a6f0811bc647807"),
                     # The same with the matrix command in a function
                     # (294bb61c3); runs recorded after the lock move.
                     dict(bytes=37897,
                          sha256="2ddffc08c6ef5e931688822d593308f5"
                                 "652b0232e37c0b3d94dae246663b5ee1")]
# Header fields naming the code; a resume may change them (see begin).
CODE = ("driver", "acceptance")
# The engine is not sealed here: the recorded runs predate it.
TABLE = tg.Table(
    "task29a", "TASK29A", gate.CASES, __file__, COUNTS, pairs=PAIRS,
    samples=SAMPLES, headroom=HEADROOM, drivers=DRIVERS,
    acceptance=ACCEPTANCE, layout_acceptance=LAYOUT_ACCEPTANCE,
    engine=False, require_seed=False,
    allocation="TASK29B scope; not part of this timing gate")
# Steps looked up here at call time (see timing_grid.Hooks).
STEPS = ("check_header", "replay_rows", "measure", "summary", "replay_grid",
         "begin", "check_report", "combined", "extension_pairs",
         "extension_plan", "extension_inventory", "status_code",
         "unpack_report", "predeclare", "run", "extend", "replay")
ENGINE = tg.Grid(TABLE)
ENGINE.h = tg.Hooks(sys.modules[__name__], ENGINE)
checkpoint = tg.checkpoint
canonical = tg.canonical
status_code = tg.status_code


def predeclare(grid):
    """Per-cell counts from the historical B/B (develop/develop) processes."""
    return ENGINE.predeclare(grid)


def check_report(folder, report, baseline, candidate, seconds, case, size,
                 iterations, pairs=PAIRS, samples=SAMPLES, layout_seed=None):
    """Recompute a report under the policy it recorded."""
    return ENGINE.check_report(folder, report, baseline, candidate, seconds,
                               case, size, iterations, pairs, samples,
                               layout_seed)


def summary(reports):
    return ENGINE.summary(reports)


def unpack_report(root, row, scratch):
    return ENGINE.unpack_report(root, row, scratch)


def replay_rows(root, inventory):
    """Recompute every archived cell of one inventory."""
    return ENGINE.replay_rows(root, inventory)


def begin(root, inventory, resume):
    """A fresh output, or the same experiment after an infrastructure
    failure (timing_grid.Grid.begin)."""
    return ENGINE.begin(root, inventory, resume)


def measure(root, inventory, cells, args, reports):
    """Measure (case, size, pairs) cells in order; checkpoint every row."""
    return ENGINE.measure(root, inventory, cells, args, reports)


def run(args):
    return ENGINE.run(args)


def extension_pairs(report, pairs):
    """Pairs for a cell's remeasurement, or None when the cell is final."""
    return ENGINE.extension_pairs(report, pairs)


def extension_plan(reports, pairs):
    return ENGINE.extension_plan(reports, pairs)


def check_header(inventory):
    return ENGINE.check_header(inventory)


def replay_grid(root):
    """A complete first-stage grid and its recorded decisions."""
    return ENGINE.replay_grid(root)


def extension_inventory(grid, root, inventory):
    return ENGINE.extension_inventory(grid, root, inventory)


def combined(stage1, stage2, plan, inventory):
    return ENGINE.combined(stage1, stage2, plan, inventory)


def extend(args):
    return ENGINE.extend(args)


def replay(args):
    return ENGINE.replay(args)




# Policy-owner disposition of a complete two-stage grid (2026-10-30). It
# leaves the measured decisions unchanged and classifies the cells that
# stayed inconclusive. A cell whose B/B control is still outside the window
# after the second stage cannot resolve the margin on the measuring host; it
# is listed and does not block. The attributed cells were examined one by
# one (TASK_29A, "Attribution and policy-owner disposition") and accepted.
# A fail, a protocol failure, a retained-scaling miss or any other
# inconclusive cell still blocks.
DISPOSITION = dict(
    schema="task29a-disposition-v1", decided="2026-10-30",
    unresolvable="B/B control outside the window after the second stage",
    attributed={
        "frag_named_merge-10000":
            "heap-growth mode mix; within-band CPU +1.2%/+2.5%",
        "frag_merge-100": "median +1.2%; 20 pairs; no bimodality",
        "frag_typebase-0": "median +1.2%; 20 pairs; no bimodality",
        "frag_update-0": "median +0.6%; 90 pairs; no bimodality",
        "frag_create-10": "CPU pass; wall median -0.5%; 20 pairs"})


def dispose(decisions):
    """Final TASK29A gate status of a two-stage grid's decisions."""
    a.require("remeasured" in decisions, "disposition needs a second stage")
    cells = {k: [] for k in ("pass", "unresolvable", "attributed",
                             "blocking", "fail")}
    for row in decisions["workloads"]:
        name = "%s-%d" % (row["case"], row["size"])
        kind = tg.classify_row(row)
        kind = dict(protocol="blocking", control_limited="unresolvable",
                    inconclusive=("attributed" if name in
                                  DISPOSITION["attributed"] else
                                  "blocking")).get(kind, kind)
        cells[kind].append(name)
    a.require(sorted(cells["attributed"]) ==
              sorted(DISPOSITION["attributed"]), "stale attribution")
    scaling = decisions["retained_scaling"]
    if scaling is not None and (scaling["status"] != "measured" or any(
            r["words_per_rule"]["decision"] != "pass"
            for r in scaling["adjacent_intervals"]
            if r["selection"] == "candidate")):
        cells["blocking"].append("retained_scaling")
    status = ("fail" if cells["fail"] else
              "blocked" if cells["blocking"] else "pass")
    return dict(DISPOSITION, status=status, cells=cells,
                counts={k: len(v) for k, v in cells.items()})


def disposition(args):
    """Replay a two-stage grid, then record or check its disposition."""
    root = args.output.resolve()
    replay(argparse.Namespace(output=root, partial=False))
    result = dispose(a.load(root / "decisions.json"))
    path = root / "disposition.json"
    if args.record:
        a.save(path, result)
    a.require(result == a.load(path), "changed TASK29A disposition")
    print("TASK29A disposition: %s %s" % (result["status"],
                                           json.dumps(result["counts"])))
    return {"pass": 0, "fail": 1}.get(result["status"], 2)


def main(argv=None):
    def configure(parser):
        parser.add_argument("--output", type=Path, required=True,
                            help="complete second stage")
        parser.add_argument("--record", action="store_true",
                            help="write disposition.json instead of "
                            "checking")
    return ENGINE.main(argv, extra=dict(dispose=(configure, disposition)))


if __name__ == "__main__":
    sys.exit(main())
