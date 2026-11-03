#!/usr/bin/env python3
"""TASK30 timing gate: the exclusion and history cases, paired and layout
randomized, under the confirmed equivalence policy.

This is the TASK30 table for timing_grid.py (read that module, and the
"Shared timing grid and the TASK30 table" section of PROTOCOL.md, for the
method): 24 matrix cases at six sizes, 144 cells. Nothing here changes the
policy: a 3% margin on inclusive CPU and wall, GC reported and not gated, no
outlier removal, a second stage whose pair counts come from the
develop/develop control alone.

Pairs (20), samples (5) and the layout seed are fields of the table below;
`predeclare` copies them into the counts file and `run` refuses a file or a
value that differs. Every cell runs a predeclared batch count from
task30_iterations.json. That file is produced from a develop-only pilot
(`pilot`, then `predeclare`) and committed before any candidate observation;
it names the baseline, the seals of the pilot and of the sealed files, and
each cell's batch seconds. The ten direct deletions are tiny operations;
their batches are calibrated to a longer time. A cell the first grid rejected
as "fixed calibration too short" may have its count rescaled in a new file
(`predeclare --revises PREVIOUS --rescale CELL ...`), and a change that alters
what is measured, such as a fixture bug, needs a fresh pilot
(`predeclare --revises PREVIOUS --repilot REASON`); both are listed in the
table's revisions, and then the whole grid is run again at a new candidate
commit. A candidate whose source files on the path of these operations (see
task30_cases.SOURCES) differ from the baseline's never passes, unless the file
is a reviewed difference pinned in task30_pins.PINNED, which the counts are
not bound to. `run`, `extend` and `replay` take the pilot the counts derive
from (`--pilot DIR`, derived again in full); every run is recorded in the
table's attempts ledger, `.agent-files/evidence/task30/attempts.jsonl` below
the checkout it was made in (a grid and its retries stay in that one
checkout; `replay` and `close` may read the ledger of another with
`--ledger FILE`). The checkout is configured, built and stamped by `prepare`
(`poly < tools/smart-configure.sml`, then the real `bin/build --stdknl`, which
Holmake judges), and every measuring command compares the tree outside the
performance area and the contents of bin/hol, bin/hol.state0, bin/Holmake,
sigobj and the theory data files and sources with the stamp.
`pilot`, `run` and `extend` take an output below `.agent-files/evidence/` (or
outside the repository), for the tree must be clean when they end.

The exit status is zero only when every cell passes (1: a cell failed; 2:
the grid is not conclusive). Failed, inconclusive, control-limited and
protocol-failed cells are listed separately and none is excused here; a
disposition, if one is ever made, is a separate reviewed decision. A command
that is refused, or ends with an error that decided nothing, prints one
REFUSED line on the standard error (after a traceback, if the error is not a
refusal) and exits 3.

  prepare     configure, build and stamp the checkout    (takes the lock)
  pilot       develop-only cells for the counts          (needs a window)
  predeclare  counts file from a pilot, or a revision of the last file
              (--revises PREVIOUS --rescale CELL [CELL ...], or
              --revises PREVIOUS --repilot REASON)
  verify-counts  the counts file against its pilot
  run         first stage (--pilot)                      (needs a window)
  extend      second stage for the cells the control left open (--pilot)
  replay      recompute every archived decision offline (--pilot)
  close       replay the timing grid and the allocation grid, require one
              candidate and one harness, print the single closing verdict
              (--grid, --pilot, --allocation, [--ledger])
"""
import argparse
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task30_cases as cases
import task30_pins as pins
import timing_grid as tg

# As the TASK29A run used: 20 pairs of 5 samples per cell. `predeclare` writes
# these and the layout seed into the counts file; a second run under the same
# settings is a new draw, recorded in the attempts ledger (see PROTOCOL.md).
PAIRS, SAMPLES = 20, 5
LAYOUT_SEED = "task30-layout-1"
SECONDS, LONG_SECONDS = 0.3, 1.0
COUNTS = a.HERE / "task30_iterations.json"
# The files installed into the private directories of every process
# (run_paired.install_fixtures: the paired sources and their Holmakefile, the
# Matrix fixtures, the runtime metrics and the signature check), the
# installer itself and the case ledger, with the data and helpers the
# harness reads. A change to one between the pilot and a run alters what is
# measured, so the counts are bound to them. Names are relative to the
# performance directory. The paired files are listed by the installer's own
# rule, and a test installs the fixtures and compares.
PAIRED = a.HERE.parent / "compatibility" / "paired"
INSTALLED = (
    "MatrixPerformance.sml", "MatrixSupport.sml", "RuntimeMetrics.sml",
    "review-20261021/abicheck.sml", "../compatibility/run_paired.py",
    "matrix.json") + tuple(
    "../compatibility/paired/" + p.name for p in sorted(PAIRED.iterdir())
    if p.suffix == ".sml" or p.name == "Holmakefile")
SEALED = ("task30_cases.py", "task29_gate.py", "matrix_schema.py",
          "performance_schema.py", "evidence_bundle.py") + INSTALLED
# The code the first-stage grid and the pilot of this table were measured by,
# 63ac28189 (before the warmup schedule): the seals of the files that commit
# changed, which an inventory recorded then still names. The table declares
# the ramp schedule (the default of a new table is warmup), so its counts,
# grid and ledger replay as they did.
DRIVERS = (dict(bytes=9634,
                sha256="b958adae97df21cbcd5b1b72b5d47fa5"
                       "455854aec6f45c133f042fb0e883586f"),)
ENGINES = (dict(bytes=131311,
                sha256="b32f98ecee9fd2dbbebf5c21ca2ca053"
                       "7442b3ba1b070861fe00a68910cd7d49"),)
ACCEPTANCE = (dict(bytes=38678,
                   sha256="108a0d0827ec6848a0c1e2e6987f9f80"
                          "02591ac24498c7119cf5f58f14725b83"),)
SEALED_HISTORY = {
    "MatrixPerformance.sml": (dict(
        bytes=4954, sha256="b805611bc816a19bf7e17734b10a40cb"
                           "65996086366be5e34078266dc010c13c"),),
    "performance_schema.py": (dict(
        bytes=10528, sha256="ca6d11ba99b59e43313c8b1da2ee0dc6"
                            "c12b9289bd8c7761bbd8bf322eb11516"),),
    "../compatibility/run_paired.py": (dict(
        bytes=48705, sha256="81baeb647f95850f267e3f72b333cc2a"
                            "4921e342070c92a951a1e34583738dac"),)}
TABLE = tg.Table(
    "task30", "TASK30", cases.CASES, __file__, COUNTS, seconds=SECONDS,
    seconds_by_case={c: LONG_SECONDS for c in cases.DELETIONS},
    fixed_seconds=True, schedule="ramp", pairs=PAIRS, samples=SAMPLES,
    seed=LAYOUT_SEED, baseline=a.BASE, engine=True, engines=ENGINES,
    drivers=DRIVERS, layout_acceptance=ACCEPTANCE,
    sealed_history=SEALED_HISTORY, tree="src", sealed=SEALED,
    sources=cases.SOURCES, pinned=pins.PINNED, pin_file="task30_pins.py",
    pin_history=pins.PIN_HISTORY, require_seed=True,
    allocation="the separate gate of allocation_matrix.py --task task30, "
    "all 24 cases at six sizes")
ENGINE = tg.Grid(TABLE, doc=__doc__)


def verdict(grid, allocation, repo, pilot, ledger=None):
    """Replay both gates, require that they measured one candidate with one
    harness, and return the closing line and the exit status. Nothing is
    excused: any status but pass in either gate is not a pass here. The
    cheap comparisons of the two inventories come before the replays."""
    import allocation_matrix as am
    a.require((allocation / "decisions.json").exists(),
              "the allocation grid is partial: it has no decisions")
    timing = a.load(grid / "inventory.json")
    counted = a.load(allocation / "inventory.json")
    harness = counted.get("harness", {})
    a.require(counted.get("task") == "task30",
              "the allocation grid is not a TASK30 grid")
    a.require(timing["candidate"] == counted["candidate"],
              "the timing grid measured %s, the allocation grid %s"
              % (timing["candidate"], counted["candidate"]))
    a.require(timing["baseline"] == counted["baseline"],
              "the two grids have different baselines")
    a.require(
        timing["checkout"]["head"] == harness.get("head") and
        timing["checkout"]["tree_outside_performance"] ==
        harness.get("tree_outside_performance") and
        harness.get("dirty") is False,
        "the two grids ran in different harnesses (head %s and %s)"
        % (timing["checkout"]["head"], harness.get("head")))
    timing_code = ENGINE.replay(argparse.Namespace(
        output=grid, partial=False, repo=repo, pilot=pilot, ledger=ledger))
    for line in tg.class_report(TABLE.label, a.load(grid / "decisions.json")):
        print(line)
    allocation_code = am.replay(argparse.Namespace(output=allocation))
    total, mine = ENGINE.ledger_counts(argparse.Namespace(
        repo=repo, ledger=ledger), timing["candidate"])
    states = [a.load(grid / "decisions.json")["status"],
              a.load(allocation / "decisions.json")["status"]]
    code = max(timing_code, allocation_code)
    result = "pass" if code == 0 else "not pass"
    return ("%s closing verdict: %s (timing %s, allocation %s; candidate %s, "
            "harness %s; attempts %d in the ledger, %d of the candidate)"
            % (TABLE.label, result, states[0], states[1],
               timing["candidate"], harness["head"], total, mine), code)


def close(args):
    line, code = verdict(args.grid.resolve(), args.allocation.resolve(),
                         args.repo, args.pilot.resolve(), args.ledger)
    print(line)
    return code


def commands():
    """The actions of this task besides the engine's: `close`."""
    def configure(parser):
        parser.add_argument("--grid", type=Path, required=True,
                            help="the timing grid, its second stage where "
                            "there is one")
        parser.add_argument("--pilot", type=Path, required=True,
                            help="the pilot the counts derive from")
        parser.add_argument("--allocation", type=Path, required=True,
                            help="the output of allocation_matrix.py "
                            "run --task task30")
        parser.add_argument("--repo", type=Path, default=a.HERE.parents[3])
        parser.add_argument("--ledger", type=Path,
                            help="read this attempts ledger, of the "
                            "checkout the timing grid was made in")
    return dict(close=(configure, close))


def main(argv=None):
    return ENGINE.main(argv, extra=commands())


if __name__ == "__main__":
    sys.exit(main())
