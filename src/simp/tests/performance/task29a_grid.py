#!/usr/bin/env python3
"""TASK29A full-grid rerun under the equivalence policy.

The policy owner replaced the superiority gate (upper CI <= 1) by a 3%
equivalence margin on inclusive CPU and wall; GC is reported, not gated
(acceptance.EQUIVALENCE_POLICY). task29_gate.py and its archives stay
unchanged so the historical grid still replays under its own policy.

Every process in a cell runs the same predeclared batch count. Counts come
from develop-only processes of the historical grid, before any new
candidate observation, so neither side can select its own count.
"""
import argparse
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import evidence_bundle as bundle
import task29_gate as gate
from performance_schema import batch_iterations, layout_seed

# The protocol minimum is ten pairs and three samples. On a shared host the
# per-pair spread needs more of both to resolve a 3% margin; the chosen
# values are fixed on the command line and recorded before any cell runs.
PAIRS, SAMPLES = 10, 3
# Calibration targets 0.3 s on a loaded host. Doubling the largest develop
# count keeps a quieter rerun above the driver's own wall-time floor.
HEADROOM = 2
COUNTS = a.HERE / "evidence/task29a/iterations.json"
# Earlier drivers whose runs still replay: 6f62229c0 (before canonical
# comparison and replay --partial) and 224219893 (before --layout-seed).
DRIVERS = [dict(bytes=12534, sha256="234da42ca599122645b9f578b1ddd37c"
                                    "6ffb70d83764d6e91e045ac4ffc4bd97"),
           dict(bytes=13917, sha256="664c632deb187a1ea9c3b59445676253"
                                    "c0872627884b2f664b0626da43d817ee")]
# acceptance.py before --layout-seed; runs without a seed analyze the same.
ACCEPTANCE = [dict(bytes=37287, sha256="343dfc5d009e8851f0db990bc484bdb2"
                                       "ed1dce3e85efac2416b1335854080b97")]


def predeclare(grid):
    """Per-cell counts from the historical B/B (develop/develop) processes."""
    inventory = a.load(grid / "inventory.json")
    table = {}
    with tempfile.TemporaryDirectory(prefix="task29a-counts-") as scratch:
        for row in inventory["runs"]:
            case, size = row["case"], row["size"]
            archive = a.safe_child(grid, row["archive"])
            a.require(a.seal(archive) == row["seal"], "changed archive")
            folder = Path(scratch) / row["archive"]
            a.require(bundle.unpack(archive, folder) == row["files"],
                      "changed archive file count")
            control = folder / ("%s-%d-control" % (case, size))
            counts = set()
            for path in sorted(control.glob("pair-*.json.gz")):
                receipt = a.load(path)
                if receipt["fixture"] != "performance":
                    continue
                stages = receipt["measurements"]["workloads"][case]
                counts.add(stages["calibration"][-1]["iterations"])
            a.require(len(counts) >= 1, "no develop calibration counts")
            table["%s-%d" % (case, size)] = batch_iterations(
                HEADROOM * max(counts))
    a.require(set(table) == {"%s-%d" % k for k in gate.keys()},
              "incomplete predeclared counts")
    return dict(schema="task29a-iterations-v1", source=inventory["driver"],
                baseline=inventory["baseline"], headroom=HEADROOM,
                rule="HEADROOM * max develop calibration count in B/B",
                iterations=table)


def checkpoint(path, value):
    """Rewrite the inventory after every cell; a crash keeps finished rows."""
    partial = path.with_name(path.name + ".partial")
    partial.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    partial.replace(path)


def canonical(value):
    """Compare as stored. Analyses key rows by integer pair, an archived
    report by string; with more than ten pairs sort_keys orders them
    differently ("10" < "2")."""
    return json.dumps(json.loads(json.dumps(value, allow_nan=False)),
                      sort_keys=True)


def check_report(folder, report, baseline, candidate, seconds, case, size,
                 iterations, pairs=PAIRS, samples=SAMPLES, layout_seed=None):
    """Recompute a report under the policy it recorded."""
    if not report["success"]:
        a.require(report.get("failure") or report.get("blocked"),
                  "unexplained incomplete experiment")
        return
    policy = report["policy"]
    a.require(policy == a.EQUIVALENCE_POLICY, "unexpected TASK29A policy")
    results = {}
    for selection in ("control", "candidate"):
        results[selection] = a.analyze(
            folder / ("%s-%d-%s" % (case, size, selection)),
            case=case, size=size, baseline=baseline,
            candidate=baseline if selection == "control" else candidate,
            pairs=pairs, samples=samples, seconds=seconds,
            iterations=iterations, policy=policy, layout_seed=layout_seed)
    for name, value in results["candidate"]["metrics"].items():
        a.apply_control(value, results["control"]["metrics"][name])
    a.require(canonical([results]) == canonical(report["workloads"]),
              "changed point analysis")
    scaling = a.retained_scaling([results]) if case == "storage_graph" else None
    a.require(canonical(scaling) == canonical(report["retained_scaling"]),
              "changed slope analysis")


def summary(reports):
    result = gate.summary(reports)
    exits = [row["exit"] for row in result["workloads"]]
    scaling = result["retained_scaling"]
    if scaling is not None and scaling["status"] == "measured":
        exits += [{"pass": 0, "fail": 1}.get(
            r["words_per_rule"]["decision"], 2)
            for r in scaling["adjacent_intervals"]
            if r["selection"] == "candidate"]
    elif scaling is not None:
        exits.append(2)
    result.update(
        schema="task29a-grid-v1", policy=a.EQUIVALENCE_POLICY,
        status=("pass" if set(exits) == {0} else
                "fail" if 1 in exits else "inconclusive"),
        allocation="TASK29B scope; not part of this timing gate")
    return result


def status_code(decisions):
    return {"pass": 0, "fail": 1}.get(decisions["status"], 2)


def run(args):
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=False)
    counts = a.load(args.iterations)
    a.require(counts["schema"] == "task29a-iterations-v1",
              "wrong predeclared counts")
    inventory = dict(schema="task29a-experiment-v1", baseline=args.baseline,
                     candidate=args.candidate, seconds=args.batch_seconds,
                     pairs=args.pairs, samples=args.samples,
                     outliers="none removed",
                     policy=a.EQUIVALENCE_POLICY, iterations=counts,
                     iterations_seal=a.seal(args.iterations), runs=[],
                     driver=a.seal(__file__), acceptance=a.seal(a.__file__))
    if args.layout_seed is not None:
        inventory["layout_seed"] = layout_seed(args.layout_seed)
    reports = {}
    keys = gate.keys()
    if args.only:
        keys = [k for k in keys if "%s-%d" % k in args.only]
        a.require(len(keys) == len(args.only), "unknown --only cell")
    with a.serial_lock(args.repo) as fds:
        import os
        old = os.environ.get("HOL4_PERF_LOCK_FDS")
        os.environ["HOL4_PERF_LOCK_FDS"] = ",".join(map(str, fds))
        try:
            for case, size in keys:
                gate.get_case(case, size)
                name = "%s-%d" % (case, size)
                count = counts["iterations"][name]
                print("START %s N=%d" % (name, count), flush=True)
                with tempfile.TemporaryDirectory(prefix="task29a-") as scratch:
                    folder = Path(scratch) / name
                    options = argparse.Namespace(
                        pairs=args.pairs, samples=args.samples,
                        batch_seconds=args.batch_seconds,
                        batch_iterations=count, timeout=args.timeout,
                        baseline=args.baseline, candidate=args.candidate,
                        authorize_measurements=True, case=[case],
                        size=[size], output=folder, mode="isolated",
                        repo=args.repo, build_manifest=None,
                        layout_seed=args.layout_seed)
                    report = a.run(options)
                    archive = root / (name + ".json.xz")
                    files = bundle.pack(folder, archive)
                    restored = Path(scratch) / "roundtrip"
                    a.require(bundle.unpack(archive, restored) == files,
                              "transport count mismatch")
                    for path in folder.rglob("*"):
                        if path.is_file():
                            a.require(a.seal(path) == a.seal(
                                restored / path.relative_to(folder)),
                                "transport changed original bytes")
                    reports[case, size] = report
                    inventory["runs"].append(dict(
                        case=case, size=size, iterations=count,
                        archive=archive.name, seal=a.seal(archive),
                        files=files, exit=a.report_exit_status(report),
                        protocol=report["success"]))
                    checkpoint(root / "inventory.json", inventory)
                    check_report(folder, report, args.baseline,
                                 args.candidate, args.batch_seconds,
                                 case, size, count, args.pairs, args.samples,
                                 args.layout_seed)
                    print("END %s exit=%d protocol=%s" % (
                        name, a.report_exit_status(report),
                        report["success"]), flush=True)
        finally:
            if old is None:
                del os.environ["HOL4_PERF_LOCK_FDS"]
            else:
                os.environ["HOL4_PERF_LOCK_FDS"] = old
            checkpoint(root / "inventory.json", inventory)
    if args.only:
        return 2
    decisions = summary(reports)
    a.save(root / "decisions.json", decisions)
    return status_code(decisions)


def replay(args):
    root = args.output.resolve()
    inventory = a.load(root / "inventory.json")
    a.require(inventory["driver"] in [a.seal(__file__)] + DRIVERS,
              "changed driver")
    a.require(inventory["acceptance"] in [a.seal(a.__file__)] + ACCEPTANCE,
              "changed acceptance")
    seed = inventory.get("layout_seed")
    a.require(seed is None or inventory["acceptance"] == a.seal(a.__file__),
              "layout seed needs the current acceptance")
    a.require(inventory["policy"] == a.EQUIVALENCE_POLICY, "changed policy")
    a.require(inventory["iterations"] == a.load(COUNTS),
              "changed predeclared counts")
    reports = {}
    for row in inventory["runs"]:
        key = row["case"], row["size"]
        a.require(key in gate.keys() and key not in reports,
                  "wrong/duplicate case")
        a.require(row["iterations"] ==
                  inventory["iterations"]["iterations"]["%s-%d" % key],
                  "count differs from predeclaration")
        archive = a.safe_child(root, row["archive"])
        a.require(a.seal(archive) == row["seal"], "changed archive")
        with tempfile.TemporaryDirectory(prefix="task29a-replay-") as scratch:
            folder = Path(scratch) / "unpacked"
            a.require(bundle.unpack(archive, folder) == row["files"],
                      "changed archive file count")
            report = a.load(folder / "acceptance.json")
            a.require(row["exit"] == a.report_exit_status(report) and
                      row["protocol"] == report["success"],
                      "changed experiment outcome")
            check_report(folder, report, inventory["baseline"],
                         inventory["candidate"], inventory["seconds"], *key,
                         row["iterations"], inventory["pairs"],
                         inventory["samples"], seed)
            reports[key] = report
        print("REPLAY %s %d" % key, flush=True)
    if args.partial:
        # An interrupted run has no grid decision; each finished cell
        # still replays exactly.
        a.require(not (root / "decisions.json").exists(),
                  "complete run replayed as partial")
        print("TASK29A partial run: %d of %d cells replayed; no grid "
              "decision" % (len(reports), len(gate.keys())))
        return 2
    decisions = summary(reports)
    a.require(decisions == a.load(root / "decisions.json"),
              "changed TASK29A decisions")
    print("TASK29A archives and decisions replayed: " + decisions["status"])
    return status_code(decisions)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    counts = sub.add_parser("predeclare")
    counts.add_argument("--grid", type=Path, required=True)
    counts.add_argument("--output", type=Path, required=True)
    execute = sub.add_parser("run")
    execute.add_argument("--output", type=Path, required=True)
    execute.add_argument("--iterations", type=Path, required=True)
    execute.add_argument("--repo", type=Path, default=a.HERE.parents[3])
    execute.add_argument("--baseline", default=a.BASE)
    execute.add_argument("--candidate", required=True)
    execute.add_argument("--batch-seconds", type=float, default=0.3)
    execute.add_argument("--pairs", type=int, default=PAIRS)
    execute.add_argument("--samples", type=int, default=SAMPLES)
    execute.add_argument("--timeout", type=int, default=1800)
    execute.add_argument("--layout-seed",
                         help="randomize code layout per fresh process")
    execute.add_argument("--only", action="append",
                         help="diagnostic subset; never a grid decision")
    execute.add_argument("--authorize-measurements", action="store_true")
    check = sub.add_parser("replay")
    check.add_argument("--output", type=Path, required=True)
    check.add_argument("--partial", action="store_true",
                       help="interrupted run: replay cells, no decision")
    args = parser.parse_args(argv)
    if args.action == "predeclare":
        a.require(not args.output.exists(), "refusing to overwrite counts")
        a.save(args.output, predeclare(args.grid.resolve()))
        return 0
    if args.action == "run":
        a.require(args.authorize_measurements, "exclusive window required")
        a.exact_pin(args.baseline)
        a.exact_pin(args.candidate)
        return run(args)
    return replay(args)


if __name__ == "__main__":
    sys.exit(main())
