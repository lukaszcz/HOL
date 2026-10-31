#!/usr/bin/env python3
"""Task-independent paired timing grid under the equivalence policy.

The machinery TASK29A confirmed, parameterized by a `Table` that names a
task's cases, batch seconds, predeclared counts and code seals:

- develop-only pilot and predeclared batch counts (`pilot`, `predeclare`),
  so neither side can select its own count;
- layout-randomized paired cells, a first stage and a second stage whose
  pair counts come from the develop/develop control alone (`run`, `extend`);
- lossless archives, offline replay of every decision (`replay`), and
  resume after an infrastructure failure (`--resume`).

Policy: acceptance.EQUIVALENCE_POLICY (3% margin on inclusive CPU and wall,
B/B validity window, GC reported and not gated). Nothing here decides that a
non-passing cell is acceptable: `classify` reports pass, fail, inconclusive,
control-limited and protocol-failed cells separately, and the exit status is
zero only when every cell passes. A task that needs a disposition supplies its
own explicit, separately reviewed table (see task29a_grid.py).

Every step of `Grid` is looked up on its `hooks` object (the grid itself by
default), so a task module can wrap or replace a step by defining it.
"""
import argparse
import json
import math
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import evidence_bundle as bundle
import matrix_schema as ms
import task29_gate as gate
from performance_schema import batch_iterations, layout_seed

# The B/B control for a metric is outside the equivalence window.
CONTROL = "baseline-control outside equivalence window"
# Second stage, predeclared with the first-stage grid.
TARGET = 0.015
MAX_PAIRS = 120
CLASSES = ("pass", "fail", "inconclusive", "control_limited", "protocol")


class Table:
    """What a task supplies. Only data, no behaviour.

    cases: matrix case names; their sizes come from the matrix ledger.
    driver: the task's own module file, sealed into every inventory.
    counts: the committed predeclared counts file.
    seconds, seconds_by_case: calibration target of a batch; a longer target
        for the cases that name it (tiny operations).
    pairs, samples: defaults of a grid; pilot_pairs, pilot_samples: of a
        pilot (the protocol minimum is ten pairs and three samples).
    fixed_seconds: the counts file names each cell's seconds and a run must
        use the table's (a task whose runs predate this keeps --batch-seconds
        free).
    drivers, acceptance, layout_acceptance: seals of earlier code whose
        recorded runs must still replay.
    engine: seal this module too (a task whose runs predate it does not).
    require_seed: refuse a first stage without layout randomization."""

    def __init__(self, name, label, cases, driver, counts, *, seconds=0.3,
                 seconds_by_case=None, fixed_seconds=False, pairs=10,
                 samples=3, pilot_pairs=10, pilot_samples=3, headroom=2,
                 target=TARGET, max_pairs=MAX_PAIRS, drivers=(),
                 acceptance=(), layout_acceptance=(), engine=True,
                 require_seed=True,
                 allocation="exact allocation is the separate gate of "
                 "allocation_matrix.py; not part of this timing gate"):
        extra = seconds_by_case or {}
        a.require(len(set(cases)) == len(cases) and
                  all(c in ms.EXPECTED_CASES for c in cases),
                  "unknown or duplicate matrix case")
        a.require(set(extra) <= set(cases) and all(
            0.1 <= v <= 60 for v in [seconds, *extra.values()]),
            "invalid batch seconds")
        self.name, self.label, self.cases = name, label, tuple(cases)
        self.driver, self.counts = Path(driver), Path(counts)
        self.seconds, self.seconds_by_case = seconds, dict(extra)
        self.fixed_seconds = fixed_seconds
        self.pairs, self.samples, self.headroom = pairs, samples, headroom
        self.pilot_pairs, self.pilot_samples = pilot_pairs, pilot_samples
        self.target, self.max_pairs = target, max_pairs
        self.drivers, self.acceptance = tuple(drivers), tuple(acceptance)
        self.layout_acceptance = tuple(layout_acceptance)
        self.engine, self.require_seed = engine, require_seed
        self.allocation = allocation

    def keys(self):
        return [(case, size) for case in self.cases for size in
                ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]]]

    def names(self):
        return ["%s-%d" % k for k in self.keys()]

    def seconds_for(self, case):
        return self.seconds_by_case.get(case, self.seconds)

    def seconds_map(self):
        """The per-cell seconds a counts file records, if it records any."""
        return ({"%s-%d" % k: self.seconds_for(k[0]) for k in self.keys()}
                if self.fixed_seconds else {})

    def code(self):
        return ("driver", "engine", "acceptance") if self.engine else (
            "driver", "acceptance")

    def schema(self, kind):
        return "%s-%s-v1" % (self.name, kind)


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


def status_code(decisions):
    return {"pass": 0, "fail": 1}.get(decisions["status"], 2)


def open_metrics(row):
    """Metrics of a cell that are neither passed nor merely reported."""
    return [v for v in row["metrics"].values()
            if v["decision"] not in ("pass", "reported")]


def classify_row(row):
    """One cell: pass; fail; control_limited (every open metric is
    inconclusive only because its B/B control is outside the window);
    inconclusive; or protocol (no admitted measurement)."""
    if not row["protocol"]:
        return "protocol"
    open_ = open_metrics(row)
    if any(v["decision"] == "fail" for v in open_):
        return "fail"
    if not open_:
        return "pass"
    if all(v["reason"] == CONTROL for v in open_):
        return "control_limited"
    return "inconclusive"


def classify(decisions):
    """Every cell of a grid decision in exactly one class. The retained
    slope, when measured, is one more entry. Nothing is excused here."""
    cells = {k: [] for k in CLASSES}
    for row in decisions["workloads"]:
        cells[classify_row(row)].append("%s-%d" % (row["case"], row["size"]))
    scaling = decisions["retained_scaling"]
    if scaling is not None:
        if scaling["status"] != "measured":
            cells["inconclusive"].append("retained_scaling")
        else:
            found = {r["words_per_rule"]["decision"]
                     for r in scaling["adjacent_intervals"]
                     if r["selection"] == "candidate"}
            if "fail" in found:
                cells["fail"].append("retained_scaling")
            elif found != {"pass"}:
                cells["inconclusive"].append("retained_scaling")
    return cells


def class_report(label, decisions):
    """Printed outcome: the counts, then every cell that is not a pass."""
    cells = classify(decisions)
    lines = ["%s grid: %s (%s)" % (label, decisions["status"], ", ".join(
        "%s %d" % (k.replace("_", "-"), len(cells[k])) for k in CLASSES))]
    for kind in CLASSES[1:]:
        lines += ["%s %s" % (kind.replace("_", "-").upper(), name)
                  for name in cells[kind]]
    return lines


class Hooks:
    """Steps a module overrides by name, the engine's own for the rest.

    A module that defines `STEPS` (names) with matching module-level
    functions is called for those steps at call time, so a patched or
    wrapped step is honored. The module itself carries the steps' defaults
    by delegating to its engine."""

    def __init__(self, module, engine):
        self.module, self.engine = module, engine

    def __getattr__(self, name):
        if name in self.module.STEPS:
            return getattr(self.module, name)
        return getattr(self.engine, name)


class Grid:
    """The engine for one table. Methods call each other through `h`."""

    def __init__(self, table, hooks=None):
        self.t = table
        self.h = self if hooks is None else hooks

    # Cells and counts ------------------------------------------------

    def cell_seconds(self, inventory, name):
        """Calibration target of one cell: the predeclared one when the
        counts name it, else the inventory's."""
        return inventory["iterations"].get("seconds", {}).get(
            name, inventory["seconds"])

    def calibration_counts(self, folder, case, size):
        """Final calibration counts of the develop-only processes of one
        archived cell: the receipts of its `-control` experiment."""
        control = folder / ("%s-%d-control" % (case, size))
        counts = set()
        for path in sorted(control.glob("pair-*.json.gz")):
            receipt = a.load(path)
            if receipt["fixture"] != "performance":
                continue
            stages = receipt["measurements"]["workloads"][case]
            counts.add(stages["calibration"][-1]["iterations"])
        a.require(len(counts) >= 1, "no develop calibration counts")
        return counts

    def check_pilot_settings(self, inventory):
        """Counts follow the pilot's batch seconds; a pilot made with other
        seconds than this table predeclares says nothing about its cells."""
        if "seconds_by_case" not in inventory:
            return  # a historical grid, not a pilot
        t = self.t
        a.require(inventory["seconds"] == t.seconds and
                  inventory["seconds_by_case"] == t.seconds_by_case,
                  "pilot batch seconds differ from the table")
        a.require(inventory["schema"] == t.schema("pilot"),
                  "pilot of another task")

    def predeclare(self, grid):
        """Per-cell counts from the develop-only (B/B) processes of a pilot
        or of a historical grid, before any candidate observation."""
        t = self.t
        inventory = a.load(grid / "inventory.json")
        self.h.check_pilot_settings(inventory)
        table = {}
        with tempfile.TemporaryDirectory(
                prefix="%s-counts-" % t.name) as scratch:
            for row in inventory["runs"]:
                case, size = row["case"], row["size"]
                name = "%s-%d" % (case, size)
                a.require(name not in table, "repeated pilot cell: " + name)
                archive = a.safe_child(grid, row["archive"])
                a.require(a.seal(archive) == row["seal"], "changed archive")
                folder = Path(scratch) / row["archive"]
                a.require(bundle.unpack(archive, folder) == row["files"],
                          "changed archive file count")
                table[name] = batch_iterations(
                    t.headroom * max(self.h.calibration_counts(
                        folder, case, size)))
        a.require(set(table) == set(t.names()),
                  "incomplete predeclared counts")
        result = dict(schema=t.schema("iterations"),
                      source=inventory["driver"],
                      baseline=inventory["baseline"], headroom=t.headroom,
                      rule="HEADROOM * max develop calibration count in B/B",
                      iterations=table)
        if t.fixed_seconds:
            result["seconds"] = t.seconds_map()
        return result

    def locked(self, repo):
        """The host/repository lock for a batch, children inheriting it."""
        class Held:
            def __enter__(self):
                self.lock = a.serial_lock(repo)
                self.fds = self.lock.__enter__()
                self.old = os.environ.get("HOL4_PERF_LOCK_FDS")
                os.environ["HOL4_PERF_LOCK_FDS"] = ",".join(
                    map(str, self.fds))
                return self.fds

            def __exit__(self, *exc):
                if self.old is None:
                    del os.environ["HOL4_PERF_LOCK_FDS"]
                else:
                    os.environ["HOL4_PERF_LOCK_FDS"] = self.old
                return self.lock.__exit__(*exc)
        return Held()

    def pilot_inventory(self, args):
        t = self.t
        return dict(
            schema=t.schema("pilot"), baseline=args.baseline,
            seconds=t.seconds, seconds_by_case=t.seconds_by_case,
            pairs=args.pairs, samples=args.samples, outliers="none removed",
            runs=[], driver=a.seal(t.driver), acceptance=a.seal(a.__file__),
            engine=a.seal(__file__))

    def pilot(self, args):
        """Develop-only experiments (baseline in both slots) with free
        calibration, one per cell, archived losslessly. Their calibration
        counts, and nothing a candidate does, set the predeclared counts."""
        t = self.t
        a.require(args.pairs >= 10 and args.samples >= 3,
                  "pilot needs at least ten pairs and three samples")
        root = args.output.resolve()
        inventory = self.h.pilot_inventory(args)
        done = {}
        if args.resume:
            old = a.load(root / "inventory.json")
            a.require({k: v for k, v in old.items() if k != "runs"} ==
                      {k: v for k, v in inventory.items() if k != "runs"},
                      "resume with different settings")
            for row in old["runs"]:
                a.require(a.seal(a.safe_child(root, row["archive"])) ==
                          row["seal"], "changed archive")
                done[row["case"], row["size"]] = row
            inventory["runs"] = old["runs"]
        else:
            root.mkdir(parents=True, exist_ok=False)
        try:
            with self.h.locked(args.repo) as fds:
                for case, size in t.keys():
                    if (case, size) in done:
                        continue
                    ms.get_case(case, size)
                    self.h.pilot_cell(root, inventory, case, size, args, fds)
        finally:
            checkpoint(root / "inventory.json", inventory)
        return 0

    def pilot_cell(self, root, inventory, case, size, args, fds):
        name = "%s-%d" % (case, size)
        seconds = self.t.seconds_for(case)
        print("PILOT %s seconds=%s" % (name, seconds), flush=True)
        options = argparse.Namespace(
            repo=args.repo, baseline=args.baseline, pairs=args.pairs,
            samples=args.samples, batch_seconds=seconds,
            timeout=args.timeout)
        with tempfile.TemporaryDirectory(
                prefix="%s-pilot-" % self.t.name) as scratch:
            folder = Path(scratch) / name
            folder.mkdir()
            control = folder / (name + "-control")
            command = a.run_logged(
                a.matrix_command(options, case, size, args.baseline,
                                 control), folder / (name + "-control.log"),
                fds, None)
            archive = root / (name + ".json.xz")
            files = self.h.archive(folder, archive, scratch)
            a.require(command["exit"] == 0 and not command["timed_out"],
                      "pilot runner failed: " + name)
            self.h.check_pilot(control, options, case, size)
            counts = self.h.calibration_counts(folder, case, size)
            inventory["runs"].append(dict(
                case=case, size=size, archive=archive.name,
                seal=a.seal(archive), files=files,
                counts=sorted(counts)))
            checkpoint(root / "inventory.json", inventory)
            print("END %s max_count=%d" % (name, max(counts)), flush=True)

    def check_pilot(self, control, options, case, size):
        a.analyze(control, case=case, size=size, baseline=options.baseline,
                  candidate=options.baseline, pairs=options.pairs,
                  samples=options.samples, seconds=options.batch_seconds,
                  policy=a.EQUIVALENCE_POLICY)

    def archive(self, folder, archive, scratch):
        """Pack a cell and verify every original byte before the scratch
        tree goes: a replay defect must not lose unique observations."""
        files = bundle.pack(folder, archive)
        restored = Path(scratch) / "roundtrip"
        a.require(bundle.unpack(archive, restored) == files,
                  "transport count mismatch")
        for path in folder.rglob("*"):
            if path.is_file():
                a.require(a.seal(path) == a.seal(
                    restored / path.relative_to(folder)),
                    "transport changed original bytes")
        return files

    # Decisions -------------------------------------------------------

    def check_report(self, folder, report, baseline, candidate, seconds,
                     case, size, iterations, pairs=None, samples=None,
                     layout_seed=None):
        """Recompute a report under the policy it recorded."""
        t = self.t
        pairs = t.pairs if pairs is None else pairs
        samples = t.samples if samples is None else samples
        if not report["success"]:
            a.require(report.get("failure") or report.get("blocked"),
                      "unexplained incomplete experiment")
            return
        policy = report["policy"]
        a.require(policy == a.EQUIVALENCE_POLICY,
                  "unexpected %s policy" % t.label)
        results = {}
        for selection in ("control", "candidate"):
            results[selection] = a.analyze(
                folder / ("%s-%d-%s" % (case, size, selection)),
                case=case, size=size, baseline=baseline,
                candidate=baseline if selection == "control" else candidate,
                pairs=pairs, samples=samples, seconds=seconds,
                iterations=iterations, policy=policy,
                layout_seed=layout_seed)
        for name, value in results["candidate"]["metrics"].items():
            a.apply_control(value, results["control"]["metrics"][name])
        a.require(canonical([results]) == canonical(report["workloads"]),
                  "changed point analysis")
        scaling = (a.retained_scaling([results])
                   if case == "storage_graph" else None)
        a.require(canonical(scaling) == canonical(report["retained_scaling"]),
                  "changed slope analysis")

    def summary(self, reports):
        t = self.t
        result = gate.summary(reports, t.keys(), t.label)
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
            schema=t.schema("grid"), policy=a.EQUIVALENCE_POLICY,
            status=("pass" if set(exits) == {0} else
                    "fail" if 1 in exits else "inconclusive"),
            allocation=t.allocation)
        return result

    def status_code(self, decisions):
        return status_code(decisions)

    def unpack_report(self, root, row, scratch):
        archive = a.safe_child(root, row["archive"])
        a.require(a.seal(archive) == row["seal"], "changed archive")
        folder = Path(scratch) / "unpacked"
        a.require(bundle.unpack(archive, folder) == row["files"],
                  "changed archive file count")
        report = a.load(folder / "acceptance.json")
        a.require(row["exit"] == a.report_exit_status(report) and
                  row["protocol"] == report["success"],
                  "changed experiment outcome")
        return folder, report

    def replay_rows(self, root, inventory):
        """Recompute every archived cell of one inventory."""
        t = self.t
        reports = {}
        for row in inventory["runs"]:
            key = row["case"], row["size"]
            name = "%s-%d" % key
            a.require(key in t.keys() and key not in reports,
                      "wrong/duplicate case")
            a.require(row["iterations"] ==
                      inventory["iterations"]["iterations"][name],
                      "count differs from predeclaration")
            with tempfile.TemporaryDirectory(
                    prefix="%s-replay-" % t.name) as scratch:
                folder, report = self.h.unpack_report(root, row, scratch)
                self.h.check_report(
                    folder, report, inventory["baseline"],
                    inventory["candidate"],
                    self.cell_seconds(inventory, name), *key,
                    row["iterations"],
                    row.get("pairs", inventory["pairs"]),
                    inventory["samples"], inventory.get("layout_seed"))
                reports[key] = report
            print("REPLAY %s %d" % key, flush=True)
        return reports

    def begin(self, root, inventory, resume):
        """A fresh output, or the same experiment after an infrastructure
        failure: identical settings, finished cells replayed and kept, an
        unrecorded cell measured again from scratch. The code may differ
        only when check_header accepts both, as for the moved lock; each
        such change is recorded with the number of rows before it."""
        code = self.t.code()
        if not resume:
            root.mkdir(parents=True, exist_ok=False)
            return {}
        old = a.load(root / "inventory.json")
        a.require(not (root / "decisions.json").exists(),
                  "run already complete")
        self.h.check_header(old)
        ignored = ("runs", "resumed") + code
        a.require({k: v for k, v in old.items() if k not in ignored} ==
                  {k: v for k, v in inventory.items() if k not in ignored},
                  "resume with different settings")
        resumed = old.get("resumed", [])
        now = {k: inventory[k] for k in code}
        if now != {k: (resumed[-1] if resumed else old)[k] for k in code}:
            resumed = resumed + [dict(now, after=len(old["runs"]))]
        inventory.update({k: old[k] for k in code})
        if resumed:
            inventory["resumed"] = resumed
        inventory["runs"] = old["runs"]
        return self.h.replay_rows(root, old)

    def measure(self, root, inventory, cells, args, reports):
        """Measure (case, size, pairs) cells in order; checkpoint every
        row."""
        seed = inventory.get("layout_seed")
        counts = inventory["iterations"]["iterations"]
        try:
            with self.h.locked(args.repo) as fds:
                for case, size, pairs in cells:
                    if (case, size) in reports:
                        continue
                    ms.get_case(case, size)
                    name = "%s-%d" % (case, size)
                    count = counts[name]
                    seconds = self.cell_seconds(inventory, name)
                    print("START %s N=%d pairs=%d seconds=%s" % (
                        name, count, pairs, seconds), flush=True)
                    self.h.measure_cell(root, inventory, case, size, pairs,
                                        count, seconds, seed, args, reports,
                                        fds)
        finally:
            checkpoint(root / "inventory.json", inventory)
        return reports

    def measure_cell(self, root, inventory, case, size, pairs, count,
                     seconds, seed, args, reports, fds):
        name = "%s-%d" % (case, size)
        with tempfile.TemporaryDirectory(
                prefix="%s-" % self.t.name) as scratch:
            folder = Path(scratch) / name
            options = argparse.Namespace(
                pairs=pairs, samples=inventory["samples"],
                batch_seconds=seconds, batch_iterations=count,
                timeout=args.timeout, baseline=inventory["baseline"],
                candidate=inventory["candidate"],
                authorize_measurements=True, case=[case], size=[size],
                output=folder, mode="isolated", repo=args.repo,
                build_manifest=None, layout_seed=seed)
            report = a.run(options)
            archive = root / (name + ".json.xz")
            files = self.h.archive(folder, archive, scratch)
            reports[case, size] = report
            row = dict(case=case, size=size, iterations=count,
                       archive=archive.name, seal=a.seal(archive),
                       files=files, exit=a.report_exit_status(report),
                       protocol=report["success"])
            if pairs != inventory["pairs"]:
                row["pairs"] = pairs
            inventory["runs"].append(row)
            checkpoint(root / "inventory.json", inventory)
            self.h.check_report(folder, report, inventory["baseline"],
                                inventory["candidate"], seconds, case, size,
                                count, pairs, inventory["samples"], seed)
            print("END %s exit=%d protocol=%s" % (
                name, a.report_exit_status(report), report["success"]),
                flush=True)

    def run(self, args):
        t = self.t
        root = args.output.resolve()
        counts = a.load(args.iterations)
        a.require(counts["schema"] == t.schema("iterations"),
                  "wrong predeclared counts")
        a.require(set(counts["iterations"]) == set(t.names()) and
                  counts.get("seconds", {}) == t.seconds_map(),
                  "predeclared counts do not match the table")
        a.require(not t.fixed_seconds or args.batch_seconds == t.seconds,
                  "batch seconds differ from the table")
        a.require(args.layout_seed is not None or not t.require_seed,
                  "%s needs layout randomization (--layout-seed)" % t.label)
        inventory = dict(
            schema=t.schema("experiment"), baseline=args.baseline,
            candidate=args.candidate, seconds=args.batch_seconds,
            pairs=args.pairs, samples=args.samples,
            outliers="none removed", policy=a.EQUIVALENCE_POLICY,
            iterations=counts, iterations_seal=a.seal(args.iterations),
            runs=[], driver=a.seal(t.driver), acceptance=a.seal(a.__file__))
        if t.engine:
            inventory["engine"] = a.seal(__file__)
        if args.layout_seed is not None:
            inventory["layout_seed"] = layout_seed(args.layout_seed)
        keys = t.keys()
        if args.only:
            keys = [k for k in keys if "%s-%d" % k in args.only]
            a.require(len(keys) == len(args.only), "unknown --only cell")
        reports = self.h.begin(root, inventory, args.resume)
        self.h.measure(root, inventory, [k + (args.pairs,) for k in keys],
                       args, reports)
        if args.only:
            return 2
        decisions = self.h.summary(reports)
        a.save(root / "decisions.json", decisions)
        return self.h.status_code(decisions)

    # Second stage ----------------------------------------------------

    def extension_pairs(self, report, pairs):
        """Pairs for a cell's remeasurement, or None when it is final.

        Under randomized layout a cell's develop/develop control may be too
        wide to resolve the margin. Such a cell is measured again, with a
        pair count computed from its control interval alone (never the
        candidate's), aiming at a half width of half the margin. A
        first-stage fail stays final whatever its control, so the candidate
        can only add fails."""
        if not report["success"]:
            return None
        result, = report["workloads"]
        metrics = result["candidate"]["metrics"]
        gated = a.EQUIVALENCE_POLICY["gated_timing"]
        if any(metrics[m]["decision"] == "fail" for m in gated):
            return None
        if all(metrics[m].get("control_valid") for m in gated):
            return None
        width = 0.0
        for m in gated:
            ci = result["control"]["metrics"][m][
                "paired_ratio_bootstrap_95_percent"]
            width = max(width, math.log(ci[1] / ci[0]) / 2
                        if ci and ci[0] > 0 else math.inf)
        wanted = pairs * (width / self.t.target) ** 2
        if not math.isfinite(wanted):
            return self.t.max_pairs
        return min(self.t.max_pairs,
                   max(2 * pairs, 10 * math.ceil(wanted / 10)))

    def extension_plan(self, reports, pairs):
        plan = []
        for key in self.t.keys():
            extra = self.h.extension_pairs(reports[key], pairs)
            if extra is not None:
                plan.append([*key, extra])
        return plan

    def check_header(self, inventory):
        t = self.t
        layout = [a.seal(a.__file__)] + list(t.layout_acceptance)
        drivers = [a.seal(t.driver)] + list(t.drivers)
        for code in [inventory] + inventory.get("resumed", []):
            a.require(code["driver"] in drivers, "changed driver")
            a.require(not t.engine or code["engine"] == a.seal(__file__),
                      "changed engine")
            a.require(code["acceptance"] in layout + list(t.acceptance),
                      "changed acceptance")
            a.require(inventory.get("layout_seed") is None or
                      code["acceptance"] in layout,
                      "layout seed needs a layout-seeded acceptance")
        a.require(inventory["policy"] == a.EQUIVALENCE_POLICY,
                  "changed policy")
        a.require(inventory["iterations"] == a.load(t.counts),
                  "changed predeclared counts")

    def replay_grid(self, root):
        """A complete first-stage grid and its recorded decisions."""
        t = self.t
        inventory = a.load(root / "inventory.json")
        a.require(inventory["schema"] == t.schema("experiment"),
                  "not a first-stage grid")
        self.h.check_header(inventory)
        reports = self.h.replay_rows(root, inventory)
        decisions = self.h.summary(reports)
        a.require(decisions == a.load(root / "decisions.json"),
                  "changed %s decisions" % t.label)
        return inventory, reports, decisions

    def extension_inventory(self, grid, root, inventory):
        t = self.t
        seed = inventory.get("layout_seed")
        a.require(seed is not None,
                  "extension needs a layout-randomized grid")
        header = {k: inventory[k] for k in (
            "baseline", "candidate", "seconds", "pairs", "samples",
            "outliers", "policy", "iterations", "iterations_seal")}
        result = dict(header, schema=t.schema("extension"),
                      grid=os.path.relpath(grid, root),
                      grid_inventory=a.seal(grid / "inventory.json"),
                      grid_decisions=a.seal(grid / "decisions.json"),
                      layout_seed=layout_seed(seed + "-ext"),
                      target=t.target, max_pairs=t.max_pairs, runs=[],
                      driver=a.seal(t.driver),
                      acceptance=a.seal(a.__file__))
        if t.engine:
            result["engine"] = a.seal(__file__)
        return result

    def combined(self, stage1, stage2, plan, inventory):
        a.require(set(stage2) == {(c, s) for c, s, _ in plan},
                  "incomplete remeasurement")
        decisions = self.h.summary({**stage1, **stage2})
        decisions["remeasured"] = dict(
            plan=plan, target=inventory["target"],
            max_pairs=inventory["max_pairs"], seed=inventory["layout_seed"],
            rule="B/B control outside the window and no first-stage fail")
        return decisions

    def extend(self, args):
        t = self.t
        grid, root = args.grid.resolve(), args.output.resolve()
        first, stage1, _ = self.h.replay_grid(grid)
        inventory = self.h.extension_inventory(grid, root, first)
        plan = self.h.extension_plan(stage1, first["pairs"])
        inventory["plan"] = plan
        print("PLAN %d cells: %s" % (len(plan), json.dumps(plan)),
              flush=True)
        reports = self.h.begin(root, inventory, args.resume)
        self.h.measure(root, inventory, [tuple(p) for p in plan], args,
                       reports)
        decisions = self.h.combined(stage1, reports, plan, inventory)
        a.save(root / "decisions.json", decisions)
        return self.h.status_code(decisions)

    def replay(self, args):
        t = self.t
        root = args.output.resolve()
        inventory = a.load(root / "inventory.json")
        self.h.check_header(inventory)
        if inventory["schema"] == t.schema("extension"):
            grid = (root / inventory["grid"]).resolve()
            a.require(a.seal(grid / "inventory.json") ==
                      inventory["grid_inventory"] and
                      a.seal(grid / "decisions.json") ==
                      inventory["grid_decisions"],
                      "changed first-stage grid")
            first, stage1, _ = self.h.replay_grid(grid)
            a.require(inventory == dict(
                self.h.extension_inventory(grid, root, first),
                plan=self.h.extension_plan(stage1, first["pairs"]),
                runs=inventory["runs"],
                **{k: inventory[k] for k in t.code() + ("resumed",)
                   if k in inventory}), "changed extension plan")
            reports = self.h.replay_rows(root, inventory)
            a.require([[r["case"], r["size"],
                        r.get("pairs", inventory["pairs"])]
                       for r in inventory["runs"]] ==
                      inventory["plan"][:len(inventory["runs"])],
                      "remeasurement differs from plan")
            if args.partial:
                a.require(not (root / "decisions.json").exists(),
                          "complete run replayed as partial")
                print("%s partial remeasurement: %d of %d cells replayed"
                      % (t.label, len(reports), len(inventory["plan"])))
                return 2
            decisions = self.h.combined(stage1, reports, inventory["plan"],
                                        inventory)
            a.require(decisions == a.load(root / "decisions.json"),
                      "changed %s decisions" % t.label)
            print("%s two-stage archives and decisions replayed: %s" % (
                t.label, decisions["status"]))
            return self.h.status_code(decisions)
        reports = self.h.replay_rows(root, inventory)
        if args.partial:
            # An interrupted run has no grid decision; each finished cell
            # still replays exactly.
            a.require(not (root / "decisions.json").exists(),
                      "complete run replayed as partial")
            print("%s partial run: %d of %d cells replayed; no grid "
                  "decision" % (t.label, len(reports), len(t.keys())))
            return 2
        decisions = self.h.summary(reports)
        a.require(decisions == a.load(root / "decisions.json"),
                  "changed %s decisions" % t.label)
        print("%s archives and decisions replayed: %s" % (
            t.label, decisions["status"]))
        return self.h.status_code(decisions)

    # Command line ----------------------------------------------------

    def parser(self):
        t = self.t
        parser = argparse.ArgumentParser(description=__doc__)
        sub = parser.add_subparsers(dest="action", required=True)
        repo = a.HERE.parents[3]

        def settings(p):
            p.add_argument("--repo", type=Path, default=repo)
            p.add_argument("--timeout", type=int, default=1800)

        pilot = sub.add_parser(
            "pilot", help="develop-only experiments for the counts")
        pilot.add_argument("--output", type=Path, required=True)
        pilot.add_argument("--baseline", default=a.BASE)
        pilot.add_argument("--pairs", type=int, default=t.pilot_pairs)
        pilot.add_argument("--samples", type=int, default=t.pilot_samples)
        pilot.add_argument("--resume", action="store_true")
        pilot.add_argument("--authorize-measurements", action="store_true")
        settings(pilot)
        counts = sub.add_parser(
            "predeclare", help="counts file from a pilot or earlier grid")
        counts.add_argument("--grid", type=Path, required=True)
        counts.add_argument("--output", type=Path, required=True)
        execute = sub.add_parser("run")
        execute.add_argument("--output", type=Path, required=True)
        execute.add_argument("--iterations", type=Path, default=t.counts)
        execute.add_argument("--baseline", default=a.BASE)
        execute.add_argument("--candidate", required=True)
        execute.add_argument("--batch-seconds", type=float,
                             default=t.seconds)
        execute.add_argument("--pairs", type=int, default=t.pairs)
        execute.add_argument("--samples", type=int, default=t.samples)
        execute.add_argument("--layout-seed",
                             help="randomize code layout per fresh process")
        execute.add_argument("--only", action="append",
                             help="diagnostic subset; never a grid decision")
        execute.add_argument("--resume", action="store_true",
                             help="continue after an infrastructure failure")
        execute.add_argument("--authorize-measurements",
                             action="store_true")
        settings(execute)
        more = sub.add_parser("extend")
        more.add_argument("--grid", type=Path, required=True)
        more.add_argument("--output", type=Path, required=True)
        more.add_argument("--resume", action="store_true",
                          help="continue after an infrastructure failure")
        more.add_argument("--authorize-measurements", action="store_true")
        settings(more)
        check = sub.add_parser("replay")
        check.add_argument("--output", type=Path, required=True)
        check.add_argument("--partial", action="store_true",
                           help="interrupted run: replay cells, no decision")
        return parser, sub

    def main(self, argv=None, extra=None):
        """Dispatch. `extra` maps a task's own action to (configure the
        subparser, handler); the engine decides nothing of the kind."""
        parser, sub = self.parser()
        handlers = {}
        for name, (configure, handler) in (extra or {}).items():
            configure(sub.add_parser(name))
            handlers[name] = handler
        args = parser.parse_args(argv)
        if args.action in handlers:
            return handlers[args.action](args)
        status = self.dispatch(args)
        if args.action in ("run", "extend", "replay"):
            decided = args.output.resolve() / "decisions.json"
            if decided.exists():
                for line in class_report(self.t.label, a.load(decided)):
                    print(line)
        return status

    def dispatch(self, args):
        if args.action == "predeclare":
            a.require(not args.output.exists(),
                      "refusing to overwrite counts")
            a.save(args.output, self.h.predeclare(args.grid.resolve()))
            return 0
        if args.action in ("pilot", "run", "extend"):
            a.require(args.authorize_measurements,
                      "exclusive window required")
        if args.action in ("pilot", "run"):
            a.exact_pin(args.baseline)
        if args.action == "pilot":
            return self.h.pilot(args)
        if args.action == "run":
            a.exact_pin(args.candidate)
            return self.h.run(args)
        if args.action == "extend":
            return self.h.extend(args)
        return self.h.replay(args)
