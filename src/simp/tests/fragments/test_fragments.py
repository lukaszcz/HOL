#!/usr/bin/env python3
"""Fail-closed synthetic controls. No performance claims from these tests."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import run_fragments as probe


def fake_dependencies(root):
    for module in probe.MATCHED_MODULES:
        base = root / "src/simp/src"
        generated = module == "simpMarkerTheory"
        if generated:
            base /= ".hol/objs"
        base.mkdir(parents=True, exist_ok=True)
        for suffix in ((".sig", ".sml", ".dat") if generated else
                       (".sig", ".sml")):
            (base / (module + suffix)).write_text(module + suffix + "\n")


def encode(events):
    return "".join(probe.paired.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                   for i, e in enumerate(events))


def behavior_events():
    events = []
    for n in probe.SIZES:
        for label in (*probe.LABELS, "cells"):
            key = "control.cells" if label == "cells" else "graph." + label
            events += [["observation", key, f"{n},{5 * n}"],
                       ["check", label + " " + str(n), "pass"]]
    return events + [["check", name, "pass"] for name in probe.EXTRAS] + [
        ["observation", "complete", "TASK15-fragments-v1"]]


def schedule():
    return {label + "." + str(n): i + 2
            for n in probe.SIZES for i, label in enumerate(probe.LABELS)}


def timing_events(fixed=None):
    # Metrics: wall, nongc user/system, GC user/system, inclusive user/system,
    # GC user, consumed count. Values are synthetic and deliberately distinct.
    times = ".25,.15,.02,.03,.01,.18,.03,.03,"
    events = [["observation", "timer.accounting", times + "5"],
              ["check", "timer accounting", "pass"]]
    total = 5
    for n in probe.SIZES:
        for label in probe.LABELS:
            key = label + "." + str(n)
            count = fixed[key] if fixed is not None else 1
            fields = times + str(count)
            events.append(["observation", "calibration." + key,
                           f"{count}," + fields])
            for i in range(3):
                events += [["observation", "batch." + key,
                            f"{i},{count}," + fields],
                           ["check", "results " + key, "pass"]]
            total += 4 * count
    return events + [["observation", "sink", str(total)]]


class FragmentProtocolTests(unittest.TestCase):
    def test_complete(self):
        events, graphs = probe.behavior(encode(behavior_events()))
        self.assertEqual(sum(e[0] == "check" for e in events), 105)
        self.assertEqual(len(graphs), 15)
        _, data = probe.timing(encode(timing_events()), 3, .2)
        self.assertEqual(len(data), 90)
        self.assertAlmostEqual(data["rewrites.0"][0]["cpu"], .21)
        self.assertAlmostEqual(data["rewrites.0"][0]["user_cpu"], .18)
        self.assertAlmostEqual(data["rewrites.0"][0]["system_cpu"], .03)

    def test_complete_fixed_schedule(self):
        fixed = schedule()
        # One calibration, even below the adaptive wall threshold.
        _, data = probe.timing(encode(timing_events(fixed)), 3, 100, fixed)
        self.assertEqual(set(data), set(fixed))
        for key, rows in data.items():
            for row in rows:
                self.assertEqual(row["iterations"], fixed[key])
                self.assertAlmostEqual(row["user_cpu"], .18 / fixed[key])
                self.assertAlmostEqual(row["system_cpu"], .03 / fixed[key])
                self.assertEqual(row["raw"],
                                 [.25, .15, .02, .03, .01, .18, .03, .03])
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "schedule.json"
            path.write_text(json.dumps(fixed))
            parsed, seal = probe.load_fixed_iterations(path)
            self.assertEqual(parsed, fixed)
            self.assertEqual(seal, probe.paired.fingerprint(path))
            env = ",".join(k + "=" + str(v) for k, v in parsed.items())
            self.assertEqual(dict(entry.split("=") for entry in env.split(",")),
                             {k: str(v) for k, v in fixed.items()})

    def test_adaptive_doubling_unchanged(self):
        events = timing_events()
        first = copy.deepcopy(events[2])
        fields = first[2].split(",")
        fields[1] = ".1"
        first[2] = ",".join(fields)
        # First workload calibrates at 1 then 2, samples at 2; others at 1.
        for i in (2, 3, 5, 7):
            fields = events[i][2].split(",")
            fields[0 if i == 2 else 1] = "2"
            fields[-1] = "2"
            events[i][2] = ",".join(fields)
        events[-1][2] = str(int(events[-1][2]) + 5)
        events.insert(2, first)
        _, data = probe.timing(encode(events), 3, .2)
        self.assertEqual(data["rewrites.0"][0]["iterations"], 2)
        self.assertEqual(data["merge.0"][0]["iterations"], 1)

    def test_fixed_missing_extra_and_malformed_counts(self):
        fixed = schedule()
        invalid = [None, [], {}, dict(fixed, unknown=1)]
        partial = dict(fixed)
        del partial["rewrites.0"]
        invalid.append(partial)
        for value in (0, -1, True, False, 1.5, 2.0, "2", None, [], {}):
            invalid.append(dict(fixed, **{"rewrites.0": value}))
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "schedule.json"
            for values in invalid:
                with self.subTest(values=values):
                    path.write_text(json.dumps(values))
                    with self.assertRaises(ValueError):
                        probe.load_fixed_iterations(path)
                    if values is not None:
                        with self.assertRaises(ValueError):
                            probe.timing(encode(timing_events()), 3, .2, values)
            for text in ('{"rewrites.0":1,"rewrites.0":2}', '{',
                         json.dumps(fixed).replace(': 2,', ': NaN,', 1)):
                path.write_text(text)
                with self.assertRaises(ValueError):
                    probe.load_fixed_iterations(path)

    def test_fixed_protocol_is_fail_closed(self):
        fixed = schedule()
        events = timing_events(fixed)
        # Wrong calibration count, sample index/count, consumption, accounting.
        for i, field, value in ((2, 0, "1"), (3, 0, "1"), (3, 1, "1"),
                                (2, 9, "1"), (3, 10, "1"), (3, 7, "100"),
                                (-1, 0, "0")):
            es = copy.deepcopy(events)
            fields = es[i][2].split(",")
            fields[field] = value
            es[i][2] = ",".join(fields)
            with self.subTest(i=i, field=field), self.assertRaises(ValueError):
                probe.timing(encode(es), 3, 100, fixed)
        es = copy.deepcopy(events)
        es[2], es[3] = es[3], es[2]
        with self.assertRaises(ValueError):
            probe.timing(encode(es), 3, 100, fixed)
        # No additional adaptive calibration is permitted in fixed mode.
        with self.assertRaises(ValueError):
            probe.timing(encode(events[:3] + [events[2]] + events[3:]),
                         3, 100, fixed)
        for i in range(len(events)):
            with self.subTest(missing=i), self.assertRaises(ValueError):
                probe.timing(encode(events[:i] + events[i + 1:]), 3, 100, fixed)

    def test_every_behavior_event_required(self):
        events = behavior_events()
        for i in range(len(events)):
            with self.subTest(i=i), self.assertRaises(ValueError):
                probe.behavior(encode(events[:i] + events[i + 1:]))

    def test_every_timing_event_required(self):
        events = timing_events()
        for i in range(len(events)):
            with self.subTest(i=i), self.assertRaises(ValueError):
                probe.timing(encode(events[:i] + events[i + 1:]), 3, .2)

    def test_missing_count_control_exception_and_extras(self):
        for row in (["observation", "graph.rewrites", "1,0"],
                    ["observation", "graph.rewrites", "0,-1"],
                    ["observation", "graph.rewrites", "0,nan"]):
            events = behavior_events()
            events[0] = row
            with self.assertRaises(ValueError):
                probe.behavior(encode(events))
        for replacement in ("0,0", "1,6"):
            events = behavior_events()
            events[30][2] = replacement
            if replacement == "0,0":
                events[62][2] = "1,6"
            with self.assertRaises(ValueError):
                probe.behavior(encode(events))
        for extra in (["exception", "Fail", "bad proof"], behavior_events()[0]):
            with self.assertRaises(ValueError):
                probe.behavior(encode(behavior_events() + [extra]))

    def test_bad_timer_counts_sink_and_nonfinite(self):
        for index, value in ((0, "nan"), (1, "inf"), (2, "~1"),
                             (3, "-1"), (5, "100"), (8, "0")):
            es = timing_events()
            fields = es[2][2].split(",")
            fields[index + 1] = value
            es[2][2] = ",".join(fields)
            with self.subTest(index=index), self.assertRaises(ValueError):
                probe.timing(encode(es), 3, .2)
        for i, field, value in ((2, 0, "2"), (3, 0, "1"), (3, 1, "2"),
                                (-1, 0, "0")):
            es = timing_events()
            fs = es[i][2].split(",")
            fs[field] = value
            es[i][2] = ",".join(fs)
            with self.subTest(i=i), self.assertRaises(ValueError):
                probe.timing(encode(es), 3, .2)

    def test_extra_timing_fields_and_events_reject(self):
        for i in (0, 1, 2, 3, 4, -1):
            es = timing_events()
            es[i].append("extra")
            with self.subTest(i=i), self.assertRaises(ValueError):
                probe.timing(encode(es), 3, .2)
        with self.assertRaises(ValueError):
            probe.timing(encode(timing_events() + [["check", "extra", "pass"]]),
                         3, .2)

    def test_pair_ratios_and_graph_deltas_are_per_workload(self):
        _, data = probe.timing(encode(timing_events()), 3, .2)
        runs = [dict(selection=s, pair=0, measurements=copy.deepcopy(data))
                for s in ("baseline", "candidate")]
        for row in runs[1]["measurements"]["rewrites.1000"]:
            row["cpu"] *= 2
        result = probe.timing_comparison(runs)
        self.assertEqual(
            result["rewrites.1000"]["cpu"]["median_paired_ratio"], 2)
        self.assertEqual(result["merge.1000"]["cpu"]["median_paired_ratio"], 1)
        self.assertEqual(
            result["merge.1000"]["user_cpu"]["median_paired_ratio"], 1)
        self.assertEqual(
            result["merge.1000"]["system_cpu"]["median_paired_ratio"], 1)
        _, graphs = probe.behavior(encode(behavior_events()))
        sides = {s: dict(graphs=copy.deepcopy(graphs))
                 for s in ("baseline", "candidate")}
        sides["candidate"]["graphs"]["rewrites"][3][1] += 100
        delta = probe.graph_comparison(sides)
        self.assertEqual(
            delta["rewrites"]["candidate_minus_baseline_words"][3], 100)
        with self.assertRaisesRegex(ValueError,
                                    "increased retained fragment words"):
            probe.require_baseline_graphs(delta)
        sides["candidate"] = copy.deepcopy(sides["baseline"])
        probe.require_baseline_graphs(probe.graph_comparison(sides))

    def test_failed_process_stale_path_and_footer_use_existing_validator(self):
        # The common validator must reject these before accepting dynamic data.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            args = dict(selection="baseline", fixture="behavior",
                control="none", private=root, repo=root,
                private_names={"simpLib"},
                flavor="baseline", signature="pass", source_hashes={})
            header = [["begin", "baseline", "behavior", "none"], ["cwd", tmp],
                ["holdir", tmp, tmp], ["preloaded", "HolKernel,Paired"],
                ["heapfile", str(root / "Paired.sml")], ["search", tmp],
                ["search", str(root / "sigobj")]]
            receipt = dict(timed_out=False, exit=1,
                stdout=encode(header + [["end", "pass", "1"]]))
            with self.assertRaisesRegex(ValueError, "failed process"):
                probe.paired.validate(receipt, **args)
            receipt["exit"] = 0
            receipt["stdout"] = encode(header)
            with self.assertRaisesRegex(ValueError, "completion/test count"):
                probe.paired.validate(receipt, **args)
            outside = root / "outside"
            outside.mkdir()
            (outside / "simpLib.sml").write_text("(* synthetic *)\n")
            private = root / "private"
            private.mkdir()
            header[1] = ["cwd", str(private)]
            header[5] = ["search", str(private)]
            receipt["stdout"] = encode(header + [
                ["use", str(outside / "simpLib.sml")],
                ["check", "legacy signature", "pass"],
                ["used", str(outside / "simpLib.sml")],
                ["loaded", str(root / "Paired.sml")],
                ["loaded", str(outside / "simpLib.sml")], ["end", "pass", "1"]])
            with self.assertRaisesRegex(ValueError,
                                        "wrong loaded simplifier path"):
                probe.paired.validate(receipt, **dict(args, private=private))

    def test_supplements_preserve_selected_sources_and_audit_separately(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake_dependencies(root)
            snapshot = probe.supplement_snapshot(root, root / "snapshot")
            self.assertEqual(len(snapshot), 11)
            self.assertNotIn("Cond_rewrExt", probe.MATCHED_MODULES)
            self.assertFalse(any("simpExtLib" in s["source_path"]
                                 for s in snapshot))
            baseline, candidate = root / "baseline", root / "candidate"
            baseline.mkdir()
            candidate.mkdir()
            # Even a chosen dependency must not replace an existing selection.
            existing = baseline / "TraverseExt.sml"
            existing.write_text("selected historical API, do not replace\n")
            seal = probe.paired.fingerprint(existing)
            ordinary = baseline / "Cond_rewr.sig"
            ordinary.write_text("historical API; no is_var_perm export\n")
            ordinary_seal = probe.paired.fingerprint(ordinary)
            a = probe.install_supplements(baseline, snapshot)
            b = probe.install_supplements(candidate, snapshot)
            self.assertEqual(probe.paired.fingerprint(existing), seal)
            self.assertEqual(probe.paired.fingerprint(ordinary), ordinary_seal)
            self.assertTrue(all("Cond_rewr." not in s["private_path"]
                                for s in a))
            self.assertEqual(len(a), 10)
            self.assertEqual(len(b), 11)
            self.assertNotIn(str(existing), [s["private_path"] for s in a])
            self.assertTrue(all(s["source_path"] != s["private_path"]
                                for s in a + b))
            probe.verify_supplements(snapshot, a + b)
            for source in snapshot:
                for key in ("source_path", "snapshot_path"):
                    path = Path(source[key])
                    data = path.read_bytes()
                    path.write_bytes(data + b"drift")
                    with self.assertRaisesRegex(ValueError,
                                                "supplement.*drift"):
                        probe.verify_supplements(snapshot, a + b)
                    path.write_bytes(data)
            for source in a + b:
                path = Path(source["private_path"])
                data = path.read_bytes()
                path.write_bytes(data + b"drift")
                with self.assertRaisesRegex(ValueError,
                                            "installed supplement drift"):
                    probe.verify_supplements(snapshot, a + b)
                path.write_bytes(data)

    def test_missing_or_changed_snapshot_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake_dependencies(root)
            snapshot = probe.supplement_snapshot(root, root / "snapshot")
            dst = root / "baseline"
            dst.mkdir()
            source = Path(snapshot[0]["snapshot_path"])
            source.write_text("drift\n")
            with self.assertRaisesRegex(ValueError,
                                        "supplement snapshot drift"):
                probe.install_supplements(dst, snapshot)
            self.assertFalse(list(dst.iterdir()))
            missing = root / "src/simp/src/TraverseExt.sml"
            missing.unlink()
            with self.assertRaises(FileNotFoundError):
                probe.supplement_snapshot(root, root / "missing-snapshot")

    def test_private_build_has_preload_metadata_and_no_theory_regeneration(self):
        default = probe.private_holmakefile(False)
        self.assertEqual(default,
            "HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
            "paired.exe: runner.uo CheckSupport.uo selftest.uo "
            "FragmentPerformance.uo\n\t$(HOLMOSMLC) -o $@ $<\n")
        matched = probe.private_holmakefile(True)
        for module in probe.MATCHED_MODULES:
            self.assertNotIn(module + ".uo", default)
            self.assertIn(module + ".uo", matched.splitlines()[1])
        self.assertNotIn("simpExtLib", matched)
        self.assertIn("simpMarkerTheory.sml simpMarkerTheory.sig "
                      "simpMarkerTheory.dat:\n\t@test -f $@\n", matched)
        self.assertNotIn("Script", matched)

    def test_private_runner_preloads_without_changing_common_runner(self):
        original = (probe.HERE.parent /
                    "compatibility/paired/runner.sml").read_text()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "runner.sml"
            path.write_text(original)
            probe.install_matched_runner(Path(tmp))
            text = path.read_text()
            support = text.index('Meta.loadPlan tracedUse "CheckSupport";')
            target = text.index('Meta.loadPlan tracedUse (Paired.env')
            for module in probe.MATCHED_MODULES:
                preload = 'Meta.loadPlan tracedUse "' + module + '";'
                self.assertEqual(text.count(preload), 1)
                self.assertTrue(support < text.index(preload) < target)
            self.assertEqual((probe.HERE.parent /
                "compatibility/paired/runner.sml").read_text(), original)
            path.write_text("unexpected runner\n")
            with self.assertRaisesRegex(ValueError, "preload anchor"):
                probe.install_matched_runner(Path(tmp))

    def test_matched_trace_requires_once_before_target_and_no_simp_ext(self):
        dst = Path("/private")
        modules = ("CheckSupport", *probe.MATCHED_MODULES, "selftest")
        events = [["use", str(dst / (name + ".sml"))] for name in modules]
        probe.validate_matched_trace(events, dst, "selftest")
        for i in range(len(events)):
            with self.assertRaises(ValueError):
                probe.validate_matched_trace(events[:i] + events[i + 1:],
                                             dst, "selftest")
        for i in range(1, len(events) - 1):
            with self.assertRaises(ValueError):
                probe.validate_matched_trace(events + [events[i]],
                                             dst, "selftest")
            late = events[:i] + events[i + 1:] + [events[i]]
            with self.assertRaises(ValueError):
                probe.validate_matched_trace(late, dst, "selftest")
        with self.assertRaisesRegex(ValueError, "simpExtLib is forbidden"):
            probe.validate_matched_trace(events + [
                ["preloaded", "HolKernel,simpExtLib"]], dst, "selftest")
        for kind in ("use", "used", "loaded", "heapfile"):
            with self.assertRaisesRegex(ValueError, "simpExtLib is forbidden"):
                probe.validate_matched_trace(events + [
                    [kind, str(dst / "simpExtLib.sml")]], dst, "selftest")

    def test_heap_options_exact_and_default_launcher_unchanged(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            launcher = root / "paired.exe"
            original = ("#!/bin/sh\n" + str(root / "bin/hol") +
                " --gcthreads=1 run --holstate=" +
                str(root / "bin/hol.state0") + "  runner\n")
            for mb in (None, 256, 512):
                launcher.write_text(original)
                text, options = probe.configure_launcher(root, root, mb)
                expected = ["--gcthreads=1"]
                if mb is not None:
                    expected += [f"--minheap={mb}", f"--maxheap={mb}"]
                else:
                    self.assertEqual(text, original)
                self.assertEqual(options, expected)
                self.assertIn(" ".join(expected) + " run ", text)
                self.assertEqual(launcher.read_text(), text)
            launcher.write_text("wrong launcher\n")
            with self.assertRaisesRegex(ValueError, "wrong launcher"):
                probe.configure_launcher(root, root, 256)

    def test_bad_flags_fail_before_output_creation(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "must-not-exist"
            for flags in (("--seconds", "nan"), ("--samples", "2"),
                          ("--performance-pairs", "-1"), ("--timeout", "0"),
                          ("--heap-mb", "0"), ("--heap-mb", "-1"),
                          ("--heap-mb", "1.5"), ("--heap-mb", "nan")):
                result = subprocess.run([sys.executable, "-B", probe.__file__,
                    "--output", str(output), *flags],
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 2)
                self.assertFalse(output.exists())

    def test_bad_schedule_fails_before_output_creation(self):
        with tempfile.TemporaryDirectory() as tmp:
            path, output = Path(tmp) / "schedule.json", Path(tmp) / "output"
            # Includes unreadable/missing input, partial and malformed JSON.
            for text in (None, "{}", "[]", "{", "null",
                         json.dumps(dict(schedule(), **{"rewrites.0": True})),
                         json.dumps(dict(schedule(), **{"rewrites.0": 0}))):
                if text is not None:
                    path.write_text(text)
                result = subprocess.run([sys.executable, "-B", probe.__file__,
                    "--output", str(output), "--fixed-iterations", str(path)],
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn("invalid fixed iterations", result.stderr)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
