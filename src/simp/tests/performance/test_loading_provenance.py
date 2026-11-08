#!/usr/bin/env python3
"""Loading provenance controls; synthetic builds/processes are NOT timings."""
from contextlib import nullcontext
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import loading as l
import timing_grid as tg

RAW = "1,0.4,0.1,0.1,0.1,0.5,0.2,0.1"
EMPTY = "0.000001,0,0,0,0,0,0,0"


def receipt(text="", code=0, timeout=False):
    return dict(exit=code, timed_out=timeout, stdout=text,
                stdout_sha256=l.rp.digest(text.encode()),
                stdout_bytes=len(text.encode()), process_wall=0.001)


class ChildStdin(unittest.TestCase):
    # `cat` waits for EOF on the inherited descriptor; an open pipe that is
    # never closed hung the Poly/ML version query the same way. The pipe is
    # the stdin of a separate Python process, so that this process's own
    # descriptors (fd 0 may be closed) are not touched.
    CODE = (
        "import json, os, sys\n"
        "sys.path.insert(0, sys.argv[1])\n"
        "from pathlib import Path\n"
        "import loading as l\n"
        "got = l.execute(['cat'], Path.cwd(), dict(os.environ), 20, ())\n"
        "logged = l.a.run_logged(['cat'], Path(sys.argv[2]) / 'log', (), 20)\n"
        "print(json.dumps([[got['exit'], got['timed_out']],\n"
        "                  [logged['exit'], logged['timed_out']]]))\n")

    def test_children_never_inherit_an_open_stdin(self):
        temp = tempfile.TemporaryDirectory(prefix="stdin-")
        self.addCleanup(temp.cleanup)
        child = subprocess.Popen(
            [sys.executable, "-B", "-c", self.CODE,
             str(Path(__file__).parent), temp.name],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.addCleanup(child.stdin.close)
        self.addCleanup(child.kill)
        self.addCleanup(child.stdout.close)
        out = child.stdout.read()
        child.wait(timeout=90)
        self.assertEqual(child.returncode, 0)
        self.assertEqual(json.loads(out), [[0, False], [0, False]])


class LibraryDiscovery(unittest.TestCase):
    def test_actual_linker_mapping_and_loader_not_vdso(self):
        text = ("\tlinux-vdso.so.1 (0x123)\n"
                "\tlibpolyml.so.16 => /lib/libpolyml.so.16 (0x456)\n"
                "\t/lib/ld-linux-aarch64.so.1 (0x789)\n")
        self.assertEqual(l.library_paths(receipt(text)),
                         ["/lib/libpolyml.so.16",
                          "/lib/ld-linux-aarch64.so.1"])

    def test_failed_partial_unresolved_empty_or_unsupported_discovery(self):
        good = "libc.so => /lib/libc.so (0x123)\n"
        for row in (receipt(good, code=1), receipt(good, timeout=True),
                    receipt(good[:-1]), receipt(""),
                    receipt("linux-vdso.so.1 (0x123)\n"),
                    receipt(good + "libpolyml.so => not found\n"),
                    receipt(good + "unexpected diagnostic\n"),
                    receipt(good * 2), receipt("statically linked\n")):
            with self.subTest(row=row), self.assertRaises(ValueError):
                l.library_paths(row)

    def test_missing_library_is_not_silently_omitted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            text = "libmissing => " + str(root / "missing.so") + " (0x1)\n"
            with self.assertRaises(FileNotFoundError):
                l.library_inputs(receipt(text))


class BuildBinding(unittest.TestCase):
    """Real Git extraction/install/path validators, mocked build and execution.

    The positive control must admit six complete smoke observations. Mutations
    happen inside installation/build, BEFORE post-build product fingerprinting,
    rather than after sealing as in the earlier validator unit test.
    """
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="loading-provenance-")
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        native = self.repo / "src/simp/src"
        native.mkdir(parents=True)
        for module in ("Traverse", "simpLib", "congLib", "Unloaded"):
            for suffix in (".sig", ".sml"):
                (native / (module + suffix)).write_text("(* git source *)\n")
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        l.rp.git(self.repo, "add", "src")
        l.rp.git(self.repo, "-c", "user.name=Protocol Test", "-c",
                 "user.email=test@invalid", "commit", "-qm", "fixture")
        self.pin = l.rp.git(self.repo, "rev-parse", "HEAD").decode().strip()
        # The attempts ledger lives below the checkout, ignored by git.
        exclude = self.repo / ".git/info/exclude"
        exclude.write_text(exclude.read_text() + ".agent-files\n")
        self.ledger = l.ledger_path(self.repo)
        (self.repo / "bin").mkdir()
        for name in ("hol", "Holmake", "hol.state0", "poly"):
            (self.repo / "bin" / name).write_text("synthetic tool\n")
        self.library = self.repo / "libpolyml.so.16.0"
        self.library.write_text("synthetic HOL-linked library\n")
        self.link = self.repo / "libpolyml.so.16"
        self.link.symlink_to(self.library)
        self.other = self.repo / "other.so"
        self.other.write_bytes(self.library.read_bytes())
        self.processes = 0
        self.discovery = 0
        self.mutation = None
        self.kill_at = None  # the process number that is killed
        self.extension_from = 1  # first process of "baseline-extension"
        self.builds = []
        # Scale of the loading.raw of process number n (1-based) on `side`.
        self.scale = lambda n, side: 1.0
        self.layouts = []

    def execute(self, command, cwd, env, timeout, fds):
        command = list(map(str, command))
        self.assertEqual(env["LC_ALL"], "C")
        self.assertEqual(timeout, 30)
        text = ""
        if command == [str(self.repo / "bin/poly"), "-v"]:
            text = "Poly/ML synthetic\n"
        elif command == ["ldd", str(self.repo / "bin/hol")]:
            self.discovery += 1
            if self.mutation == "discovery-failure" or \
                    (self.mutation == "recheck-failure" and self.discovery > 1):
                return receipt("not found\n", code=1)
            path = self.other if self.mutation == "resolution" and \
                self.discovery > 1 else self.link
            text = "libpolyml.so.16 => " + str(path) + " (0x1)\n"
        elif command[0] == str(self.repo / "bin/Holmake"):
            dst = Path(command[command.index("-C") + 1])
            self.builds.append(dst)
            target = dst / "simpLib.sml"
            if self.mutation == "baseline-build" and dst.name == "baseline":
                target.write_text(target.read_text() + "val changed = ();\n")
            if dst.name == "candidate":
                if self.mutation in ("candidate-build", "signature", "delete"):
                    target = dst / ("Unloaded.sig" if
                                    self.mutation == "signature" else
                                    "simpLib.sml")
                    if self.mutation == "delete":
                        target.unlink()
                    else:
                        target.write_text(target.read_text() +
                                          "val changed = ();\n")
                elif self.mutation == "earlier-selection":
                    target = self.builds[0] / "simpLib.sml"
                    target.write_text(target.read_text() + "val x = ();\n")
                elif self.mutation == "fixture-build":
                    target = dst / "runner.sml"
                    target.write_text(target.read_text() + "val x = ();\n")
            (dst / "paired.exe").write_text(
                "#!/bin/sh\n" + str(self.repo / "bin/hol") +
                " --gcthreads=1 run --holstate=" +
                str(self.repo / "bin/hol.state0") + "\n")
        else:
            dst = Path(cwd)
            self.assertEqual(command, [str(dst / "paired.exe")])
            self.processes += 1
            self.layouts.append(env.get("PERF_LAYOUT"))
            raw = ",".join(repr(float(x) * self.scale(
                self.processes, dst.name)) for x in RAW.split(","))
            if self.processes == 1:
                if self.mutation == "library-bytes":
                    self.library.write_text("changed library\n")
                elif self.mutation == "symlink":
                    self.link.unlink()
                    self.link.symlink_to(self.other)
                elif self.mutation == "post-build":
                    target = dst / "simpLib.sml"
                    target.write_text(target.read_text() + "val x = ();\n")
            events = [
                ["begin", env["PAIR_SELECTION"], "loading", "none"],
                ["cwd", str(dst)],
                ["holdir", str(self.repo), str(self.repo)],
                ["preloaded", "HolKernel,Paired"],
                ["heapfile", str(dst / "Paired.sml")],
                ["search", str(dst)],
                ["search", str(self.repo / "sigobj")],
                ["observation", "timer.accounting", RAW],
                ["observation", "timer.empty", EMPTY],
                ["observation", "loading.begin", "congLib"],
            ]
            for module in ("Traverse", "simpLib", "congLib"):
                events += [[kind, str(dst / (module + ".sml"))]
                           for kind in ("use", "used")]
            events += [
                ["observation", "loading.end", "congLib"],
                ["observation", "loading.raw", raw],
                ["observation", "loading.extensions",
                 "SplitData" if (self.mutation, dst.name) in (
                     ("extension", "candidate"),
                     ("baseline-extension", "baseline")) and (
                     self.mutation != "baseline-extension" or
                     self.processes >= self.extension_from)
                 else l.NO_EXTENSIONS],
                ["use", str(dst / "selftest.sml")],
                ["check", "ordinary exact kernel equality", "pass"],
                ["check", "congruence exact kernel equality", "pass"],
                ["used", str(dst / "selftest.sml")],
            ]
            events += [["loaded", str(dst / (module + ".sml"))]
                       for module in ("Paired", "Traverse", "simpLib",
                                      "congLib", "selftest")]
            events += [["end", "pass", "2"]]
            text = "".join(l.rp.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                           for i, e in enumerate(events))
            if self.processes == self.kill_at:
                return dict(command=command, cwd=str(cwd),
                            **receipt(text, code=-9))
        return dict(command=command, cwd=str(cwd), **receipt(text))

    def run_protocol(self, **changes):
        options = SimpleNamespace(
            repo=self.repo, baseline=self.pin, candidate=self.pin,
            module="congLib", pairs=1, reps=1, smoke=True, calibrate=False,
            timeout=30, layout_seed=l.LAYOUT_SEED,
            authorize_measurements=True, api_audit=None,
            output=self.repo / "output")
        if changes.get("smoke", True):
            options.layout_seed = l.SMOKE_SEED
        options.__dict__.update(changes)
        install = l.install

        def install_mutation(dst, module):
            install(dst, module)
            if self.mutation == "install":
                target = dst / "simpLib.sml"
                target.write_text(target.read_text() + "val x = ();\n")

        with patch.object(l, "execute", self.execute), \
                patch.object(l, "install", install_mutation), \
                patch.object(l.shutil, "which", return_value=str(
                    self.repo / "bin/poly")), \
                patch.object(l.a, "serial_lock", lambda _: nullcontext(())):
            return l.run(options)

    def test_unmodified_control_uses_git_bytes_and_actual_hol_libraries(self):
        report = self.run_protocol()
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(self.processes, 6)
        self.assertEqual(self.discovery, 2)
        self.assertEqual(report["dynamic_libraries"]["inputs"], {
            str(self.link): dict(resolved=str(self.library),
                                 **l.a.seal(self.library))})
        self.assertIn(str(self.link), report["inputs"])
        self.assertIn(str(self.library), report["inputs"])
        for selection in report["selections"].values():
            for source in selection["sources"]:
                expected = {k: source[k] for k in ("bytes", "sha256")}
                self.assertEqual(selection["products"][
                    Path(source["private_path"]).name], expected)

    def test_calibration_run_records_reps_and_replays(self):
        self.decision_settings()
        report = self.run_protocol(pairs=10, reps=2, smoke=False,
                                   calibrate=True)
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(report["mode"], "calibration")
        self.assertEqual((report["schema"], report["reps"], report["stage"],
                          report["layout_seed"]),
                         (l.SCHEMA, 2, "first", l.LAYOUT_SEED))
        self.assertEqual(self.processes, 2 + 2 * 10 * 2)
        self.assertEqual(report["policy"], l.a.EQUIVALENCE_POLICY)
        self.assertEqual(sorted({r["rep"] for r in report["runs"]}), [0, 1])
        self.assertEqual(report["jitter"]["second_stage_pairs"], 20)
        self.assertEqual(report["jitter"]["configured_units"],
                         l.PAIRS * l.REPS)
        self.assertEqual(report["semantic_gate"],
                         "not admitted: calibration only")
        out = self.repo / "output"
        info = l.replay(out)
        self.assertEqual((info["replayed"], info["exit"]), (42, None))
        self.assertIs(info["covered"], l.covered(report["jitter"]))
        self.assertEqual(info["seal"], l.a.seal(out / "loading.json"))
        # Tampering with a process receipt is caught by its seal.
        victim = out / report["runs"][5]["receipt"]
        victim.write_bytes(victim.read_bytes() + b"x")
        with self.assertRaisesRegex(ValueError, "changed process receipt"):
            l.replay(out)

    def test_a_long_seed_is_refused_before_anything_is_created(self):
        # layout_units appends "-pilot", so 59-64 characters do not fit.
        for seed, ok in (("s" * 58, True), ("s" * 59, False),
                         ("s" * 64, False)):
            with self.subTest(length=len(seed)):
                out = self.repo / ("seed%d" % len(seed))
                if ok:
                    self.assertTrue(self.run_protocol(
                        layout_seed=seed, output=out)["success"])
                else:
                    with self.assertRaisesRegex(ValueError, "at most 58"):
                        self.run_protocol(layout_seed=seed, output=out)
                    self.assertFalse(out.exists())

    def test_every_process_gets_a_recorded_replayed_layout(self):
        self.decision_settings()
        report = self.run_protocol(pairs=10, reps=2, smoke=False,
                                   calibrate=True)
        self.assertTrue(report["success"], report.get("failure"))
        expected = [str(l.layout_units(l.LAYOUT_SEED, ph, i, side, r))
                    for ph, i, side, r in l.expected_runs(10, 2, True)]
        self.assertEqual(self.layouts, expected)
        self.assertGreater(len(set(expected)), 10)
        for entry in report["runs"]:
            env = l.a.load(self.repo / "output" / entry["receipt"])[
                "environment"]
            self.assertEqual(env["PERF_LAYOUT"], str(l.layout_units(
                l.LAYOUT_SEED, entry["phase"], entry["pair"],
                entry["selection"], entry["rep"])))
        self.run_protocol(pairs=1, reps=1, output=self.repo / "second",
                          layout_seed="other")
        self.assertNotEqual(self.layouts[len(expected):][:6],
                            expected[:6])

    # Decision runs: the develop pin is the fixture's, the counts are small.
    def decision_settings(self, pairs=10, reps=2):
        for target, name, value in ((l, "PAIRS", pairs), (l, "REPS", reps),
                                    (l.a, "BASE", self.pin)):
            patcher = patch.object(target, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        gate = dict(receipt="/nonexistent/receipt.json", seal={},
                    actual_files={}, cases=8, candidate_sources_bound=True)
        patcher = patch.object(l, "semantic_gate", return_value=gate)
        patcher.start()
        self.addCleanup(patcher.stop)

    def decide(self, name="output", **changes):
        options = dict(smoke=False, calibrate=False, pairs=l.PAIRS,
                       reps=l.REPS, baseline=self.pin, candidate=self.pin,
                       api_audit=self.repo / "audit.json",
                       output=self.repo / name)
        options.update(changes)
        return self.run_protocol(**options)

    def wide(self, n, side):
        return 1 + 0.3 * ((n * 7) % 5 - 2) / 2

    def test_decision_run_is_exactly_the_predeclared_counts(self):
        self.decision_settings()
        for changes in (dict(pairs=11), dict(pairs=9), dict(reps=3),
                        dict(reps=1), dict(layout_seed="free"),
                        dict(baseline="b" * 40),
                        dict(module="simpLib", pairs=40, reps=5)):
            with self.subTest(changes=changes), \
                    self.assertRaisesRegex(
                        ValueError, "exactly|develop pin|layout seed"):
                self.decide(**changes)
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "output").exists())
        with self.assertRaisesRegex(ValueError, "exclusive"):
            self.decide(smoke=True, calibrate=True)
        report = self.decide()
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual((report["stage"], report["pairs"], report["reps"]),
                         ("first", 10, 2))
        self.assertEqual(self.processes, 2 + 2 * 2 * 10 * 2)

    def test_cli_refuses_other_counts_and_stray_flags(self):
        base = ["--baseline", l.a.BASE, "--candidate", "c" * 40,
                "--module", "simpLib", "--authorize-measurements",
                "--api-audit", "/unused"]
        out = self.repo / "cli"
        for extra in (["--pairs", "30"], ["--reps", "4"],
                      ["--pairs", "39", "--reps", "5"],
                      ["--layout-seed", "mine"]):
            with self.subTest(extra=extra):
                self.assertEqual(l.main(base + extra + [
                    "--output", str(out)]), 1)
                self.assertFalse(out.exists())
        for argv in (["--replay", str(out), "--pairs", "40"],
                     ["--replay", str(out), "--output", str(out)],
                     ["--extend", str(out), "--pairs", "80"],
                     ["--extend", str(out), "--baseline", l.a.BASE],
                     ["--replay", str(out), "--extend", str(out)],
                     ["--expect-seal", "0" * 64, "--module", "simpLib"]):
            with self.subTest(argv=argv):
                self.assertEqual(l.main(argv), 1)

    def test_decision_run_replays_with_seal_and_exit_status(self):
        self.decision_settings()
        report = self.decide()
        self.assertTrue(report["success"], report.get("failure"))
        out = self.repo / "output"
        info = l.replay(out)
        self.assertEqual((info["exit"], info["replayed"], info["stage"]),
                         (0, 82, "first"))
        self.assertEqual(l.replay(out, expect_seal=info["seal"]["sha256"]),
                         info)
        with self.assertRaisesRegex(ValueError, "expected seal"):
            l.replay(out, expect_seal="0" * 64)
        self.assertEqual(l.main(["--replay", str(out), "--expect-seal",
                                 info["seal"]["sha256"]]), 0)
        self.assertEqual(l.main(["--replay", str(out), "--expect-seal",
                                 "0" * 64]), 1)
        # A decision run found at other counts is not a decision run.
        with patch.object(l, "PAIRS", 12), \
                self.assertRaisesRegex(ValueError, "exactly"):
            l.replay(out)

    def rewrite(self, out, edit_report=None, edit_run=None, index=3):
        """Edit loading.json and/or one process receipt, keeping every seal
        consistent: only the replay's own checks can then refuse it."""
        report = l.a.load(out / "loading.json")
        if edit_run:
            entry = report["runs"][index]
            path = out / entry["receipt"]
            receipt = l.a.load(path)
            edit_run(receipt)
            path.write_bytes(gzip.compress(
                (json.dumps(receipt, indent=2) + "\n").encode(), mtime=0))
            entry["seal"] = l.a.seal(path)
        if edit_report:
            edit_report(report)
        (out / "loading.json").write_text(json.dumps(report, indent=2))

    def test_replay_refuses_every_inconsistent_report(self):
        self.decision_settings()
        self.assertTrue(self.decide()["success"])
        out = self.repo / "output"
        pristine = (out / "loading.json").read_text()
        runs = l.a.load(out / "loading.json")["runs"]
        control = next(i for i, r in enumerate(runs)
                       if r["phase"] == "control" and r["rep"] == 1)
        cand = next(i for i, r in enumerate(runs)
                    if r["phase"] == "candidate" and
                    r["selection"] == "candidate")

        def relabel(r):
            r["runs"][control]["pair"] += 1

        def swap_phase(r):
            r["runs"][control], r["runs"][cand] = (r["runs"][cand],
                                                   r["runs"][control])

        def swap_pilots(r):
            r["runs"][0], r["runs"][1] = r["runs"][1], r["runs"][0]

        def drop(r):
            r["runs"].pop()

        def selection(r):
            r["runs"][cand]["selection"] = "baseline"

        cases = {
            "relabelled pair": (relabel, None, control, "reordered"),
            "relabelled selection": (selection, None, cand, "reordered"),
            "receipt pair": (
                None, lambda x: x.update(pair=x["pair"] + 1), control,
                "disagrees"),
            "receipt phase": (
                None, lambda x: x.update(phase="candidate"), control,
                "disagrees"),
            "cross-phase order": (swap_phase, None, control, "reordered"),
            "pilot order": (swap_pilots, None, control, "reordered"),
            "missing process": (drop, None, control, "reordered"),
            "actual selection": (
                None, lambda x: x.update(actual_selection="candidate"),
                control, "actual selection"),
            "candidate actual": (
                None, lambda x: x.update(actual_selection="baseline"),
                cand, "actual selection"),
            "enforcement flag": (
                None, lambda x: x["measurement"].update(
                    extension_absence_enforced=False), cand, "enforcement"),
            "layout": (
                None, lambda x: x["environment"].update(PERF_LAYOUT="127"),
                cand, "layout"),
            "selection env": (
                None, lambda x: x["environment"].update(
                    PAIR_SELECTION="baseline"), cand, "environment"),
            "control from the candidate launcher": (
                None, lambda x: x.update(command=[x["command"][0].replace(
                    "baseline", "candidate")]), control, "launcher command"),
            "candidate from the baseline launcher": (
                None, lambda x: x.update(command=[x["command"][0].replace(
                    "candidate", "baseline")]), cand, "launcher command"),
            "launcher cwd": (
                None, lambda x: x.update(cwd=x["cwd"].replace(
                    "candidate", "baseline")), cand, "launcher directory"),
            "private directory": (
                None, lambda x: x["environment"].update(
                    PAIR_PRIVATE=x["environment"]["PAIR_PRIVATE"].replace(
                        "baseline", "candidate")), control,
                "launcher directory"),
            "module": (
                None, lambda x: x["environment"].update(
                    LOADING_MODULE="simpLib"), cand, "module"),
            "stems": (
                None, lambda x: x["measurement"].update(
                    loaded_stems=x["measurement"]["loaded_stems"] + ["q"]),
                cand, "changed measurement"),
            "calibration": (
                lambda r: r["calibration"][0].update(calibrated=False),
                None, control, "calibration"),
            "statistics": (
                lambda r: r["results"]["candidate"]["metrics"]["wall"]
                .update(decision="pass" if r["results"]["candidate"][
                    "metrics"]["wall"]["decision"] != "pass" else "fail"),
                None, control, "statistics"),
            "width": (
                lambda r: r.update(control_half_log_width=0.5),
                None, control, "width"),
            "pairs for target": (
                lambda r: r.update(second_stage_pairs=99), None, control,
                "width or count"),
            "semantic gate": (
                lambda r: r.update(semantic_gate="not admitted: smoke only"),
                None, control, "semantic"),
            "semantic cases": (
                lambda r: r["semantic_gate"].update(cases=7), None, control,
                "semantic"),
            "first stage": (
                lambda r: r.update(stage="second"), None, control,
                "malformed|first stage"),
            "floor": (
                lambda r: r.update(layout_seed="free"), None, control,
                "exactly"),
        }
        for name, (edit_report, edit_run, index, error) in cases.items():
            (out / "loading.json").write_text(pristine)
            # Receipt edits are made on a copy of the pristine files.
            backup = {p.name: p.read_bytes() for p in out.glob("*.json.gz")}
            self.rewrite(out, edit_report, edit_run, index)
            with self.subTest(case=name):
                try:
                    with self.assertRaisesRegex(ValueError, error):
                        l.replay(out)
                finally:
                    for file, data in backup.items():
                        (out / file).write_bytes(data)
        (out / "loading.json").write_text(pristine)
        self.assertEqual(l.replay(out)["exit"], 0)

    def test_replay_checks_the_calibration_jitter(self):
        self.decision_settings()
        self.assertTrue(self.run_protocol(
            pairs=10, reps=2, smoke=False, calibrate=True)["success"])
        out = self.repo / "output"
        self.rewrite(out, lambda r: r["jitter"].update(required_units=1))
        with self.assertRaisesRegex(ValueError, "jitter"):
            l.replay(out)

    def second_stage(self, scale=None, **changes):
        """A first stage with a wide B/B control and its second stage."""
        self.decision_settings()
        self.scale = scale or self.wide
        self.assertTrue(self.decide()["success"])
        first = self.repo / "output"
        plan = l.first_stage(first)
        args = dict(smoke=False, calibrate=False, pairs=plan["pairs"],
                    reps=2, baseline=self.pin, candidate=self.pin,
                    api_audit=self.repo / "audit.json",
                    output=self.repo / "second",
                    layout_seed=l.EXTENSION_SEED)
        args.update(changes)
        return first, plan, args

    def test_second_stage_is_bound_to_the_first_and_its_control(self):
        first, plan, args = self.second_stage()
        report = plan["report"]
        control = l.a.load(first / "loading.json")["results"]["control"]
        width = tg.control_half_width({"control": control})
        self.assertGreater(width, tg.TARGET)
        self.assertEqual(plan["pairs"], tg.second_stage_pairs(
            width, l.PAIRS, tg.TARGET, tg.MAX_PAIRS))
        self.assertGreaterEqual(plan["pairs"], 2 * l.PAIRS)
        patch_args = SimpleNamespace(**dict(
            repo=self.repo, module="congLib", timeout=30,
            authorize_measurements=True, **args))
        self.processes = 0
        with patch.object(l, "execute", self.execute), \
                patch.object(l.shutil, "which", return_value=str(
                    self.repo / "bin/poly")), \
                patch.object(l.a, "serial_lock", lambda _: nullcontext(())):
            second = l.run(patch_args, plan)
        self.assertTrue(second["success"], second.get("failure"))
        self.assertEqual(second["stage"], "second")
        self.assertEqual(second["layout_seed"], l.EXTENSION_SEED)
        self.assertEqual(second["first_stage"], dict(
            run=str(first), seal=l.a.seal(first / "loading.json"),
            attempt=report["attempt"], pairs=l.PAIRS,
            second_stage_pairs=plan["pairs"]))
        units = 2 + 4 * plan["pairs"] * 2
        self.assertEqual(self.processes, units)
        out = self.repo / "second"
        info = l.replay(out)
        self.assertEqual((info["stage"], info["replayed"]),
                         ("second", units))
        # The first stage may have moved; its seal and plan still bind.
        moved = self.repo / "moved"
        first.rename(moved)
        with self.assertRaises(OSError):
            l.replay(out)
        self.assertEqual(l.replay(out, first_dir=moved), info)
        (moved / "loading.json").write_text(
            (moved / "loading.json").read_text() + " ")
        with self.assertRaisesRegex(ValueError, "expected seal"):
            l.replay(out, first_dir=moved)

    def test_second_stage_count_and_settings_are_not_free(self):
        first, plan, args = self.second_stage()
        for changes in (dict(pairs=plan["pairs"] + 10),
                        dict(pairs=plan["pairs"] - 10), dict(reps=3),
                        dict(layout_seed=l.LAYOUT_SEED),
                        dict(baseline="d" * 40), dict(candidate="d" * 40)):
            with self.subTest(changes=changes), \
                    self.assertRaisesRegex(ValueError,
                                           "second stage|develop pin"):
                l.run(SimpleNamespace(**dict(
                    repo=self.repo, module="congLib", timeout=30,
                    authorize_measurements=True, **dict(args, **changes))),
                    plan)
        self.assertFalse((self.repo / "second").exists())

    def test_a_valid_control_or_a_fail_is_final(self):
        # Resolving control: even an inconclusive candidate is final.
        self.decision_settings()
        self.scale = lambda n, side: 1.0
        self.assertTrue(self.decide()["success"])
        with self.assertRaisesRegex(ValueError, "first stage is final"):
            l.first_stage(self.repo / "output")
        # A fail is final whatever the control.
        self.processes = 0
        self.scale = lambda n, side: self.wide(n, side) * (
            3.0 if side == "candidate" and n > 2 + 2 * 10 * 2 else 1.0)
        self.ledger.unlink()  # another gate: the draw is not a rerun
        self.assertTrue(self.decide("failing")["success"])
        info = l.replay(self.repo / "failing")
        self.assertEqual(info["exit"], 1)
        with self.assertRaisesRegex(ValueError, "fail is final"):
            l.first_stage(self.repo / "failing")
        # Smoke and calibration runs have no second stage and no ledger.
        self.assertTrue(self.run_protocol(
            pairs=10, reps=2, smoke=False, calibrate=True,
            output=self.repo / "cal")["success"])
        with self.assertRaises(ValueError):
            l.first_stage(self.repo / "cal")

    def records(self):
        return [json.loads(x) for x in self.ledger.read_text().splitlines()]

    def test_each_decision_run_and_extend_is_one_recorded_attempt(self):
        first, plan, args = self.second_stage()
        opened, closed = self.records()
        self.assertEqual((opened["event"], closed["event"]),
                         ("open", "close"))
        self.assertEqual((opened["table"], opened["stage"],
                          opened["module"], opened["candidate"]),
                         (l.TABLE, "first", "congLib", self.pin))
        self.assertEqual(closed["attempt"], opened["attempt"])
        self.assertEqual(closed["seal"],
                         l.a.seal(first / "loading.json")["sha256"])
        self.assertEqual(closed["status"], "inconclusive")
        self.assertEqual(l.a.load(first / "loading.json")["attempt"],
                         opened["attempt"])

    def test_a_second_decision_run_is_refused(self):
        self.decision_settings()
        self.assertTrue(self.decide()["success"])
        before = self.processes
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("again")
        self.assertEqual(self.processes, before)
        self.assertFalse((self.repo / "again").exists())
        self.assertEqual(len(self.records()), 2)
        # The refusal is the gate's, whatever the first run decided.
        self.assertEqual(l.main([
            "--baseline", l.a.BASE, "--candidate", self.pin, "--module",
            "congLib", "--authorize-measurements", "--api-audit", "/x",
            "--repo", str(self.repo), "--output", str(self.repo / "cli")]),
            1)
        self.assertFalse((self.repo / "cli").exists())

    def test_a_run_that_decided_nothing_may_be_rerun(self):
        self.decision_settings()
        self.mutation = "candidate-build"
        failed = self.decide("failed")
        self.assertFalse(failed["success"])
        self.assertEqual(self.records()[-1]["status"], l.FAILED)
        self.mutation = None
        self.assertTrue(self.decide("retry")["success"])
        info = l.replay(self.repo / "retry")
        # Both attempts stay in the ledger and in the replay's counts.
        self.assertEqual(info["attempts"]["first"],
                         dict(attempts=2, judged=1))
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("third")

    def test_a_void_attempt_is_shown_by_its_own_output(self):
        self.decision_settings()
        self.mutation = "candidate-build"
        self.assertFalse(self.decide("void")["success"])
        found = tg.Ledger(self.ledger)
        row = next(iter(l.table_attempts(found).values()))
        self.assertIsNone(
            l.judged_because(row["opens"][0]["attempt"], "first", row))
        # Killed before any control or candidate process: still void.
        self.mutation, self.kill_at = None, 3
        self.processes = 0
        report = self.decide("early")
        self.assertFalse(report["success"])
        self.assertEqual(self.records()[-1]["status"], l.FAILED)
        self.kill_at = None
        self.assertTrue(self.decide("retry")["success"])
        info = l.replay(self.repo / "retry")
        self.assertEqual(info["attempts"]["first"],
                         dict(attempts=3, judged=1))
        self.assertEqual([r["void"] for r in info["attempts"]["table"]],
                         [True, True, False])

    def test_a_process_killed_late_is_a_judged_attempt(self):
        self.decision_settings()
        self.kill_at = 2 + 2 * 2 * 10 * 2  # the last candidate process
        report = self.decide("killed")
        self.assertFalse(report["success"])
        self.assertIn("loading process rejected", report["failure"])
        self.assertEqual(self.records()[-1]["status"], l.FAILED)
        self.kill_at, self.processes = None, 0
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("redraw")
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "redraw").exists())

    def test_a_second_close_does_not_unjudge_an_attempt(self):
        self.decision_settings()
        self.assertTrue(self.decide()["success"])
        opened, closed = self.records()
        tg.ledger_append(self.ledger, **dict(
            closed, status=l.FAILED, time="2026-01-01T00:00:00Z"))
        for call in (lambda: self.decide("again"),
                     lambda: l.replay(self.repo / "output")):
            with self.assertRaisesRegex(ValueError,
                                        "corrupt attempts ledger"):
                call()
        self.assertFalse((self.repo / "again").exists())

    def test_a_failed_close_must_match_its_output(self):
        self.decision_settings()
        self.mutation = "candidate-build"
        self.assertFalse(self.decide("void")["success"])
        self.mutation = None
        pristine = self.ledger.read_bytes()
        shutil.copytree(self.repo / "void", self.repo / "void-copy")

        def zero_seal(r):
            r[1]["seal"] = "0" * 64

        for name, edit in (("zero seal", zero_seal), ("missing output", None)):
            with self.subTest(case=name):
                if edit:
                    self.edit_ledger(edit)
                else:
                    shutil.rmtree(self.repo / "void")
                with self.assertRaisesRegex(ValueError,
                                            "judged attempt already"):
                    self.decide("retry")
                self.assertFalse((self.repo / "retry").exists())
                self.ledger.write_bytes(pristine)
                if not edit:
                    shutil.copytree(self.repo / "void-copy",
                                    self.repo / "void")
        # A report that admitted a measured process is not void either.
        path = self.repo / "void" / "loading.json"
        report = l.a.load(path)
        report["runs"].append(dict(phase="candidate", accepted=True))
        path.unlink()
        l.a.save(path, report)
        self.edit_ledger(lambda r: r[1].update(
            seal=l.a.seal(path)["sha256"]))
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("retry")

    def test_a_blocked_close_edited_to_failed_is_still_judged(self):
        self.decision_settings()
        self.mutation = "extension"
        report = self.decide("blocked")
        self.assertEqual([(r["phase"], r["accepted"])
                          for r in report["runs"]],
                         [("pilot", True), ("pilot", False)])
        self.edit_ledger(lambda r: r[-1].update(status=l.FAILED))
        self.mutation = None
        self.processes = 0
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("retry")
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "retry").exists())

    def test_void_is_read_from_the_archived_receipts(self):
        self.decision_settings()
        self.kill_at = 3  # control-000, rejected: void
        self.assertFalse(self.decide("early")["success"])
        out = self.repo / "early"
        found = l.table_attempts(tg.Ledger(self.ledger))
        (key, row), = found.items()
        self.assertIsNone(l.judged_because(key[0], key[1], row))
        # The receipt says admitted although the report says it was not.
        name = "control-000-baseline-00.json.gz"
        path = out / name
        original = path.read_bytes()
        receipt = l.a.load(path)
        receipt["accepted"] = True
        path.write_bytes(gzip.compress(
            (json.dumps(receipt, indent=2) + "\n").encode(), mtime=0))

        def reseal(report):
            for entry in report["runs"]:
                if entry["receipt"] == name:
                    entry["seal"] = l.a.seal(path)

        def reseal_all():
            self.rewrite(out, reseal)
            self.edit_ledger(lambda r: r[-1].update(
                seal=l.a.seal(out / "loading.json")["sha256"]))

        reseal_all()
        found = l.table_attempts(tg.Ledger(self.ledger))
        self.assertIsNotNone(l.judged_because(
            key[0], key[1], next(iter(found.values()))))
        self.kill_at = None
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("retry")
        # A receipt the report does not list is not void either.
        path.write_bytes(original)
        reseal_all()
        found = l.table_attempts(tg.Ledger(self.ledger))
        self.assertIsNone(l.judged_because(
            key[0], key[1], next(iter(found.values()))))
        (out / "candidate-000-candidate-00.json.gz").write_bytes(original)
        found = l.table_attempts(tg.Ledger(self.ledger))
        self.assertIsNotNone(l.judged_because(
            key[0], key[1], next(iter(found.values()))))

    def test_a_baseline_rejection_with_nothing_admitted_is_void(self):
        self.decision_settings()
        self.mutation = "baseline-extension"
        self.extension_from = 1  # the baseline pilot, which is exempt
        report = self.decide("rejected")
        self.assertFalse(report["success"])
        self.assertNotIn("blocked", report)
        self.assertEqual(self.processes, 1)
        self.assertEqual(self.records()[-1]["status"], l.FAILED)
        (key, row), = l.table_attempts(tg.Ledger(self.ledger)).items()
        self.assertIsNone(l.judged_because(key[0], key[1], row))
        self.mutation = None
        self.assertTrue(self.decide("retry")["success"])
        info = l.replay(self.repo / "retry")
        self.assertEqual(info["attempts"]["first"],
                         dict(attempts=2, judged=1))

    def test_a_baseline_rejection_after_admission_is_judged(self):
        self.decision_settings()
        self.mutation = "baseline-extension"
        self.extension_from = 4  # control-001, after control-000 was admitted
        report = self.decide("rejected")
        self.assertFalse(report["success"])
        self.assertNotIn("blocked", report)
        self.assertEqual(self.records()[-1]["status"], l.FAILED)
        (key, row), = l.table_attempts(tg.Ledger(self.ledger)).items()
        self.assertIn("admitted", l.judged_because(key[0], key[1], row))
        self.mutation = None
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("retry")

    def test_the_ledger_has_no_release_route(self):
        self.decision_settings()
        self.mutation = "extension"
        self.assertFalse(self.decide("blocked")["success"])
        self.mutation = None
        attempt = self.records()[0]["attempt"]
        status = ["--repo", str(self.repo)]
        self.assertEqual(l.main(["--ledger-status"] + status), 0)
        listing = l.ledger_status(SimpleNamespace(
            repo=self.repo, ledger=None, module=None))["table"]
        self.assertEqual([(r["attempt"], r["statuses"], r["void"])
                          for r in listing],
                         [(attempt, ["blocked"], False)])
        self.assertIn("blocked", listing[0]["judged_because"])
        with self.assertRaises(SystemExit):
            with patch("sys.stderr"):
                l.main(["--release", attempt, "--decider", "o",
                        "--reason", "r"] + status)
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("retry")
        # A line of an unknown event is a corrupt ledger.
        tg.ledger_append(self.ledger, event="decision", table=l.TABLE,
                         stage="first", attempt=attempt, decider="o",
                         reason="r")
        with self.assertRaisesRegex(ValueError, "unknown event"):
            self.decide("retry")
        with self.assertRaisesRegex(ValueError, "unknown event"):
            l.ledger_status(SimpleNamespace(
                repo=self.repo, ledger=None, module=None))

    def test_a_line_of_unknown_event_or_missing_key_fails_replay_too(self):
        self.decision_settings()
        self.assertTrue(self.decide("good")["success"])
        good = self.ledger.read_bytes()
        self.assertEqual(l.main(["--replay", str(self.repo / "good")]), 0)
        attempt = self.records()[0]["attempt"]
        tg.ledger_append(self.ledger, event="decision", table=l.TABLE,
                         stage="first", attempt=attempt)
        with self.assertRaisesRegex(ValueError, "unknown event"):
            l.replay(self.repo / "good")
        with patch("sys.stderr"):
            self.assertEqual(l.main(["--replay", str(self.repo / "good")]),
                             1)
        # A missing key is a corrupt ledger for a new run, --ledger-status
        # and replay, never a traceback.
        status = SimpleNamespace(repo=self.repo, ledger=None, module=None)
        for line, missing in (
                (dict(event="open", stage="first"), "attempt"),
                (dict(event="open", attempt="x", stage="first"),
                 "candidate"),
                (dict(event="close", attempt="x", stage="first",
                      status="fail"), "seal"),
                (dict(event="smoke", attempt="x", candidate=self.pin),
                 "source_key")):
            with self.subTest(line=line):
                self.ledger.write_bytes(good)
                tg.ledger_append(self.ledger, table=l.TABLE, **line)
                with self.assertRaisesRegex(ValueError,
                                            "corrupt.*lacks.*" + missing):
                    self.decide("retry")
                with self.assertRaisesRegex(ValueError,
                                            "corrupt.*lacks.*" + missing):
                    l.ledger_status(status)
                with self.assertRaisesRegex(ValueError,
                                            "corrupt.*lacks.*" + missing):
                    l.replay(self.repo / "good")
                with patch("sys.stderr"):
                    self.assertEqual(
                        l.main(["--replay", str(self.repo / "good")]), 1)

    def smoke_lines(self):
        return [r for r in self.records() if r["event"] == "smoke"]

    def smoke_ends(self):
        return [r for r in self.records() if r["event"] == "smoke-end"]

    def test_a_smoke_run_is_capped_and_never_uses_a_decision_seed(self):
        for changes in (dict(pairs=3), dict(reps=2), dict(pairs=40, reps=5),
                        dict(layout_seed=l.LAYOUT_SEED),
                        dict(layout_seed=l.EXTENSION_SEED)):
            with self.subTest(changes=changes), \
                    self.assertRaisesRegex(ValueError,
                                           "at most 2 pairs|may not use"):
                self.run_protocol(**changes)
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "output").exists())
        self.assertFalse(self.ledger.exists())
        self.assertTrue(self.run_protocol(pairs=2, reps=1)["success"])
        cli = ["--smoke", "--baseline", self.pin, "--module", "congLib",
               "--repo", str(self.repo), "--output", str(self.repo / "cli"),
               "--authorize-measurements"]
        for extra in (["--pairs", "3"], ["--reps", "2"],
                      ["--layout-seed", l.LAYOUT_SEED]):
            with patch("sys.stderr"):
                self.assertEqual(l.main(cli + extra), 1)
        self.assertFalse((self.repo / "cli").exists())

    def test_a_smoke_run_is_recorded_listed_and_never_judged(self):
        self.decision_settings()
        report = self.run_protocol(output=self.repo / "smoke1")
        self.assertTrue(report["success"])
        self.assertTrue(self.run_protocol(
            output=self.repo / "smoke2", pairs=2)["success"])
        # A failed smoke run is recorded too.
        self.mutation = "install"
        self.assertFalse(self.run_protocol(
            output=self.repo / "smoke3")["success"])
        self.mutation = None
        lines = self.smoke_lines()
        self.assertEqual(len(lines), 3)
        line = lines[0]
        self.assertEqual(
            (line["table"], line["candidate"], line["baseline"],
             line["module"], line["seed"], line["output"]),
            (l.TABLE, self.pin, self.pin, "congLib", l.SMOKE_SEED,
             str(self.repo / "smoke1")))
        self.assertEqual((line["source_key"], line["baseline_key"]),
                         (l.source_key(self.repo, self.pin),) * 2)
        ends = self.smoke_ends()
        self.assertEqual([e["attempt"] for e in ends],
                         [x["attempt"] for x in lines])
        self.assertEqual(ends[0]["seal"], l.a.seal(
            self.repo / "smoke1/loading.json")["sha256"])
        self.assertEqual([e["success"] for e in ends], [True, True, False])
        # Neither judged nor void: no attempt at all, and no draw blocked.
        self.assertEqual(l.table_attempts(tg.Ledger(self.ledger)), {})
        status = SimpleNamespace(repo=self.repo, ledger=None, module=None)
        listing = l.ledger_status(status)
        self.assertEqual(listing["table"], [])
        self.assertEqual([r["output"] for r in listing["smokes"]],
                         [r["output"] for r in lines])
        self.assertEqual(l.ledger_status(SimpleNamespace(
            repo=self.repo, ledger=None, module="simpLib"))["smokes"], [])
        self.assertEqual(l.main(["--ledger-status", "--repo",
                                 str(self.repo)]), 0)
        self.assertTrue(self.decide("good")["success"])
        info = l.replay(self.repo / "good")
        self.assertEqual(info["attempts"]["first"],
                         dict(attempts=1, judged=1))
        self.assertEqual([r["output"] for r in info["attempts"]["smokes"]],
                         [r["output"] for r in lines])
        # The smoke runs themselves replay as plain smoke replays.
        self.ledger.unlink()
        smoke = l.replay(self.repo / "smoke1")
        self.assertEqual((smoke["replayed"], smoke["exit"]), (6, None))
        self.assertNotIn("attempts", smoke)

    def test_a_smoke_run_needs_an_ignored_ledger(self):
        exclude = self.repo / ".git/info/exclude"
        exclude.write_text(exclude.read_text().replace(".agent-files\n", ""))
        with self.assertRaisesRegex(ValueError, "tracked by git"):
            self.run_protocol()
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "output").exists())

    def forged(self, event, drop=None, **changes):
        """A line of the event with a value of the right type for each
        field of the table, less `drop`, with `changes`."""
        values = {str: "x", int: 1, bool: True, l.STR_OR_NONE: None}
        line = {k: values[t] for k, t in l.EVENT_FIELDS[event].items()
                if k != drop}
        line.update(changes)
        return dict(event=event, table=l.TABLE, **line)

    def test_every_field_of_every_event_is_required_and_typed(self):
        self.decision_settings()
        self.assertTrue(self.decide("good")["success"])
        good = self.ledger.read_bytes()
        status = SimpleNamespace(repo=self.repo, ledger=None, module=None)
        cases = []
        for event, fields in l.EVENT_FIELDS.items():
            for key in fields:
                cases.append((event, key, "lacks " + key,
                              self.forged(event, drop=key)))
                cases.append((event, key, "wrong type for.*" + key,
                              self.forged(event, **{key: [1]})))
        # The table is what the readers use: it names every field of an
        # open line that check_ledger compares.
        for key in ("baseline", "seed", "first_attempt", "source_key"):
            self.assertIn(key, l.EVENT_FIELDS["open"])
        for event in ([1], {"a": 1}):
            cases.append(("open", "event", "unknown event",
                          dict(self.forged("open"), event=event)))
        for event, key, error, line in cases:
            with self.subTest(event=event, key=key, error=error):
                self.ledger.write_bytes(good)
                tg.ledger_append(self.ledger, **line)
                regex = "corrupt attempts ledger.*" + error
                with self.assertRaisesRegex(ValueError, regex):
                    self.decide("retry")
                with self.assertRaisesRegex(ValueError, regex):
                    l.ledger_status(status)
                with self.assertRaisesRegex(ValueError, regex):
                    l.replay(self.repo / "good")
                with self.assertRaisesRegex(ValueError, regex):
                    self.run_protocol(output=self.repo / "smoke")
                with patch("sys.stderr"):
                    self.assertEqual(
                        l.main(["--replay", str(self.repo / "good")]), 1)
                    self.assertEqual(l.main(
                        ["--ledger-status", "--repo", str(self.repo)]), 1)
        self.assertEqual(self.processes, 2 + 2 * 2 * 10 * 2)
        self.assertFalse((self.repo / "smoke").exists())
        # A bool is no int.
        self.ledger.write_bytes(good)
        tg.ledger_append(self.ledger, **self.forged("smoke", pairs=True))
        with self.assertRaisesRegex(ValueError, "wrong type for pairs"):
            l.ledger_status(status)

    def test_a_smoke_or_end_line_without_its_partner_is_corrupt(self):
        status = SimpleNamespace(repo=self.repo, ledger=None, module=None)
        self.ledger.parent.mkdir(parents=True)
        tg.ledger_append(self.ledger, **self.forged("smoke-end"))
        with self.assertRaisesRegex(ValueError, "no start"):
            l.ledger_status(status)
        self.ledger.unlink()
        for _ in range(2):
            tg.ledger_append(self.ledger, **self.forged("smoke"))
        with self.assertRaisesRegex(ValueError, "recorded twice"):
            l.ledger_status(status)

    def test_a_smoke_is_recorded_before_its_first_process(self):
        seen = []
        execute = self.execute

        def watch(*args, **kwargs):
            seen.append((len(self.smoke_lines()), len(self.smoke_ends()),
                         (self.repo / "smoke").is_dir()))
            return execute(*args, **kwargs)

        self.execute = watch
        self.assertTrue(self.run_protocol(output=self.repo / "smoke")[
            "success"])
        self.assertEqual(set(seen), {(1, 0, True)})
        self.assertEqual(len(self.smoke_ends()), 1)

    def test_a_smoke_without_an_end_line_is_unfinished(self):
        self.decision_settings()
        # A kill after the start line leaves no end line.
        with patch.object(l, "end_smoke"):
            self.assertTrue(self.run_protocol(
                output=self.repo / "killed")["success"])
        self.assertTrue(self.run_protocol(
            output=self.repo / "whole")["success"])
        self.assertEqual((len(self.smoke_lines()), len(self.smoke_ends())),
                         (2, 1))
        status = SimpleNamespace(repo=self.repo, ledger=None, module=None)
        listing = l.ledger_status(status)
        self.assertEqual(listing["table"], [])
        self.assertEqual([(r["unfinished"], r["seal"] is None)
                          for r in listing["smokes"]],
                         [(True, True), (False, False)])
        self.assertEqual(l.table_attempts(tg.Ledger(self.ledger)), {})
        self.assertTrue(self.decide("good")["success"])
        info = l.replay(self.repo / "good")
        self.assertEqual(info["attempts"]["first"],
                         dict(attempts=1, judged=1))
        self.assertEqual([r["unfinished"]
                          for r in info["attempts"]["smokes"]],
                         [True, False])

    def test_a_smoke_whose_start_cannot_be_written_starts_nothing(self):
        with patch.object(tg, "ledger_append", side_effect=OSError("full")):
            with self.assertRaisesRegex(OSError, "full"):
                self.run_protocol(output=self.repo / "smoke")
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "smoke").exists())
        self.assertFalse(self.ledger.exists())
        # A chain-broken ledger refuses the smoke as well.
        self.assertTrue(self.run_protocol(output=self.repo / "s1")["success"])
        text = self.ledger.read_text()
        self.ledger.write_text(text.replace("smoke-", "smoke+", 1))
        before = self.processes
        with self.assertRaises(ValueError):
            self.run_protocol(output=self.repo / "s2")
        self.assertEqual(self.processes, before)
        self.assertFalse((self.repo / "s2").exists())

    def test_a_smoke_refuses_what_ledger_status_refuses(self):
        self.decision_settings()
        self.assertTrue(self.decide("good")["success"])
        opening = [r for r in map(json.loads,
                                  self.ledger.read_text().splitlines())
                   if r.get("event") == "open"][0]
        for key in ("hash", "prev", "seq", "index"):
            opening.pop(key, None)
        tg.ledger_append(self.ledger, **opening)
        status = SimpleNamespace(repo=self.repo, ledger=None, module=None)
        with self.assertRaisesRegex(ValueError, "opening"):
            l.ledger_status(status)
        before, text = self.processes, self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, "opening"):
            self.run_protocol(output=self.repo / "smoke")
        self.assertEqual(self.processes, before)
        self.assertFalse((self.repo / "smoke").exists())
        self.assertEqual(self.ledger.read_bytes(), text)

    def test_a_smoke_whose_output_cannot_be_created_ends_unsuccessful(self):
        blocker = self.repo / "blocker"
        blocker.write_text("a file\n")
        before = self.processes
        with self.assertRaises(OSError):
            self.run_protocol(output=blocker / "smoke")
        self.assertEqual(self.processes, before)
        self.assertEqual(len(self.smoke_lines()), 1)
        ends = self.smoke_ends()
        self.assertEqual(len(ends), 1)
        self.assertIs(ends[0]["success"], False)
        self.assertIsNone(ends[0]["seal"])
        status = SimpleNamespace(repo=self.repo, ledger=None, module=None)
        smokes = l.ledger_status(status)["smokes"]
        self.assertEqual([r["unfinished"] for r in smokes], [False])

    def test_a_smoke_is_listed_with_the_roles_swapped(self):
        self.decision_settings()
        native = self.repo / "src/simp/src/simpLib.sml"
        native.write_text("(* another git source *)\n")
        l.rp.git(self.repo, "-c", "user.name=Protocol Test", "-c",
                 "user.email=test@invalid", "commit", "-qam", "second")
        other = l.rp.git(self.repo, "rev-parse", "HEAD").decode().strip()
        self.assertNotEqual(other, self.pin)
        # The candidate of the decision runs as the baseline of the smoke.
        swapped = self.run_protocol(
            candidate=self.pin, baseline=other,
            output=self.repo / "swapped")
        self.assertTrue(swapped["success"], swapped.get("failure"))
        # Another module's smoke is recorded whatever its outcome.
        self.run_protocol(candidate=self.pin, baseline=other,
                          module="simpLib", output=self.repo / "elsewhere")
        self.assertTrue(self.run_protocol(
            candidate=self.pin, baseline=self.pin,
            output=self.repo / "unrelated")["success"])
        self.assertTrue(self.decide("good", candidate=other)["success"])
        smokes = l.replay(self.repo / "good")["attempts"]["smokes"]
        self.assertEqual([r["output"] for r in smokes],
                         [str(self.repo / "swapped")])

    def test_a_calibration_measures_only_the_pin_against_itself(self):
        self.decision_settings()
        other = "b" * 40
        base = dict(smoke=False, calibrate=True, pairs=10, reps=1)
        for changes in (dict(baseline=other, candidate=other),
                        dict(baseline=self.pin, candidate=other),
                        dict(baseline=other, candidate=self.pin)):
            with self.subTest(changes=changes), \
                    self.assertRaisesRegex(ValueError, "develop pin"):
                self.run_protocol(**base, **changes)
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "output").exists())
        cli = ["--calibrate", "--module", "congLib", "--repo",
               str(self.repo), "--output", str(self.repo / "cli"),
               "--authorize-measurements"]
        for extra in (["--baseline", other],
                      ["--baseline", self.pin, "--candidate", other]):
            with patch("sys.stderr"):
                self.assertEqual(l.main(cli + extra), 1)
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "cli").exists())
        self.assertFalse(self.ledger.exists())
        self.assertTrue(self.run_protocol(
            **base, baseline=self.pin, candidate=self.pin)["success"])

    def test_replay_reads_each_attempt_once(self):
        self.decision_settings()
        self.mutation = "candidate-build"
        self.assertFalse(self.decide("void")["success"])
        self.mutation = None
        self.assertTrue(self.decide("retry")["success"])
        calls = []
        judged_because = l.judged_because

        def counting(attempt, stage, row):
            calls.append(attempt)
            return judged_because(attempt, stage, row)

        with patch.object(l, "judged_because", counting):
            info = l.replay(self.repo / "retry")
        self.assertEqual(len(info["attempts"]["table"]), 2)
        self.assertEqual(sorted(calls),
                         sorted(r["attempt"]
                                for r in info["attempts"]["table"]))

    def test_the_receipt_names_have_one_definition(self):
        label = l.receipt_label("control", 7, "baseline", 3)
        self.assertEqual(label, "control-007-baseline-03")
        self.assertTrue(l.RECEIPT_NAME.fullmatch(label + ".json.gz"))
        self.assertFalse(l.RECEIPT_NAME.fullmatch("pilot-000-baseline-00"
                                                  ".json.gz"))

    def test_a_moved_void_output_is_named_by_the_replay(self):
        self.decision_settings()
        self.mutation = "candidate-build"
        self.assertFalse(self.decide("void")["success"])
        self.mutation = None
        self.assertTrue(self.decide("retry")["success"])
        void = self.repo / "void"
        void.rename(self.repo / "moved")
        with self.assertRaisesRegex(
                ValueError, "output must stay at its recorded path.*"
                "its output is missing: .*void/loading.json"):
            l.replay(self.repo / "retry")

    def test_a_candidate_rejection_is_blocked_and_judged(self):
        self.decision_settings()
        self.mutation = "extension"
        report = self.decide("blocked")
        self.assertFalse(report["success"])
        self.assertEqual(self.records()[-1]["status"], l.BLOCKED)
        self.mutation = None
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("retry")

    def test_a_new_commit_of_a_judged_tree_is_the_same_draw(self):
        self.decision_settings()
        self.assertTrue(self.decide()["success"])
        opened = self.records()[0]
        key = l.key_of([(i["git_path"], i["git_blob"]) for i in
                        l.a.load(self.repo / "output/loading.json")
                        ["selections"]["candidate"]["sources"]])
        self.assertEqual(opened["source_key"], key)
        self.assertEqual(opened["baseline_key"], opened["source_key"])
        l.rp.git(self.repo, "-c", "user.name=Protocol Test", "-c",
                 "user.email=test@invalid", "commit", "-q", "--allow-empty",
                 "-m", "amended message")
        amended = l.rp.git(self.repo, "rev-parse", "HEAD").decode().strip()
        self.assertNotEqual(amended, self.pin)
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("again", candidate=amended)
        self.assertFalse((self.repo / "again").exists())
        # Another tree is another candidate.
        (self.repo / "src/simp/src/simpLib.sml").write_text("(* new *)\n")
        l.rp.git(self.repo, "add", "src")
        l.rp.git(self.repo, "-c", "user.name=Protocol Test", "-c",
                 "user.email=test@invalid", "commit", "-qm", "other tree")
        other = l.rp.git(self.repo, "rev-parse", "HEAD").decode().strip()
        self.assertTrue(self.decide("other", candidate=other)["success"])

    def commit(self, message, **files):
        for name, text in files.items():
            path = self.repo / "src/simp/src" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        l.rp.git(self.repo, "add", "src")
        l.rp.git(self.repo, "-c", "user.name=Protocol Test", "-c",
                 "user.email=test@invalid", "commit", "-q",
                 "--allow-empty", "-m", message)
        return l.rp.git(self.repo, "rev-parse", "HEAD").decode().strip()

    def test_the_gate_is_keyed_by_the_extracted_inventory(self):
        self.commit("skipped files", **{
            "notes.md": "docs\n", "Holmakefile": "all:\n",
            "selftest.sml": "(* t *)\n", "mosml/Bloom.sml": "(* m *)\n",
            "poly/Poly.sml": "(* p *)\n"})
        head = self.commit("more")
        # The key is exactly what rp.extract takes.
        dst = self.repo / "extracted"
        dst.mkdir()
        inventory = l.rp.extract(self.repo, head, dst)
        self.assertEqual(
            l.extracted_files(self.repo, head),
            sorted((i["git_path"], i["git_blob"]) for i in inventory))
        self.assertEqual(l.source_key(self.repo, head),
                         l.inventory_key(inventory))
        self.decision_settings()
        self.assertTrue(self.decide(candidate=head)["success"])
        # Edits to files that are never extracted do not make a new draw.
        for name, text in (("notes.md", "other docs\n"),
                           ("Holmakefile", "all: x\n"),
                           ("selftest.sml", "(* u *)\n"),
                           ("mosml/Bloom.sml", "(* n *)\n")):
            other = self.commit("edit " + name, **{name: text})
            with self.subTest(name=name), \
                    self.assertRaisesRegex(ValueError, "judged attempt"):
                self.decide("again", candidate=other)
            self.assertFalse((self.repo / "again").exists())
        # An extracted file makes a new inventory, and so a new draw.
        other = self.commit("poly", **{"poly/Poly.sml": "(* q *)\n"})
        self.assertTrue(self.decide("other", candidate=other)["success"])

    def test_replay_recomputes_the_key_from_the_sources(self):
        self.decision_settings()
        self.assertTrue(self.decide()["success"])
        out = self.repo / "output"
        self.rewrite(out, lambda r: r["selections"]["candidate"]["sources"][0]
                     .update(git_blob="0" * 40))
        with self.assertRaisesRegex(ValueError, "source key"):
            l.replay(out)

    def test_a_missing_source_tree_is_refused_before_any_output(self):
        self.decision_settings()
        l.rp.git(self.repo, "rm", "-rq", "src")
        l.rp.git(self.repo, "-c", "user.name=Protocol Test", "-c",
                 "user.email=test@invalid", "commit", "-qm", "nothing")
        bare = l.rp.git(self.repo, "rev-parse", "HEAD").decode().strip()
        with self.assertRaisesRegex(ValueError, "no src/simp/src"):
            self.decide(candidate=bare)
        self.assertFalse((self.repo / "output").exists())
        self.assertFalse(self.ledger.exists())

    def test_an_interrupted_attempt_counts_as_judged(self):
        self.decision_settings()
        self.assertTrue(self.decide()["success"])
        lines = self.ledger.read_text().splitlines(True)
        self.ledger.write_text(lines[0])  # the close never written
        with self.assertRaisesRegex(ValueError, "judged attempt already"):
            self.decide("again")

    def test_a_second_extend_is_refused(self):
        first, plan, args = self.second_stage()
        self.assertEqual(self.extend(plan, args)["stage"], "second")
        with self.assertRaisesRegex(ValueError, "at most one --extend"):
            self.extend(plan, dict(args, output=self.repo / "second2"))
        self.assertEqual(self.processes, 0)
        self.assertFalse((self.repo / "second2").exists())
        self.assertEqual([r["event"] for r in self.records()],
                         ["open", "close", "open", "close"])
        self.assertEqual(l.main(["--extend", str(first), "--output",
                                 str(self.repo / "second3"),
                                 "--repo", str(self.repo),
                                 "--authorize-measurements"]), 1)

    def extend(self, plan, args):
        options = SimpleNamespace(**dict(
            repo=self.repo, module="congLib", timeout=30,
            authorize_measurements=True, **args))
        self.processes = 0
        with patch.object(l, "execute", self.execute), \
                patch.object(l.shutil, "which", return_value=str(
                    self.repo / "bin/poly")), \
                patch.object(l.a, "serial_lock", lambda _: nullcontext(())):
            return l.run(options, plan)

    def edit_ledger(self, edit):
        """Rewrite the ledger with its hash chain kept intact."""
        records = self.records()
        edit(records)
        prev, lines = "0" * 64, []
        for record in records:
            record["prev"] = prev
            line = json.dumps(record, sort_keys=True)
            prev = tg.ledger_hash(line)
            lines.append(line)
        self.ledger.write_text("\n".join(lines) + "\n")

    def test_replay_checks_the_ledger(self):
        first, plan, args = self.second_stage()
        self.assertEqual(self.extend(plan, args)["stage"], "second")
        second = self.repo / "second"
        info = l.replay(second)
        table = info["attempts"].pop("table")
        self.assertEqual(info["attempts"].pop("smokes"), [])
        self.assertEqual(info["attempts"], dict(
            first=dict(attempts=1, judged=1),
            second=dict(attempts=1, judged=1)))
        # Every attempt of the table is listed.
        self.assertEqual([(r["stage"], r["statuses"], r["void"])
                          for r in table],
                         [("first", ["inconclusive"], False),
                          ("second", ["inconclusive"], False)])
        self.assertEqual(table[0]["candidate"], self.pin)
        self.assertEqual(len(table[0]["source_key"]), 64)
        # A copy of the ledger may be named from another checkout.
        copy = self.repo / "copy.jsonl"
        copy.write_bytes(self.ledger.read_bytes())
        self.ledger.unlink()
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            l.replay(second)
        again = l.replay(second, ledger=copy)
        again["attempts"].pop("table")
        again["attempts"].pop("smokes")
        self.assertEqual(again, info)
        self.assertEqual(l.main(["--replay", str(second), "--ledger",
                                 str(copy)]), 0)
        self.ledger.write_bytes(copy.read_bytes())
        pristine = copy.read_bytes()
        stray = dict(event="open", stage="first", table=l.TABLE,
                     attempt="first-stray", candidate=self.pin,
                     module="congLib", baseline=self.pin, seed=l.LAYOUT_SEED,
                     first_attempt=None, output="/x", checkout="/x",
                     source_key="k" * 64, baseline_key="k" * 64,
                     time="2026-01-01T00:00:00Z")

        def forget_open(r):
            del r[0]

        def forget_close(r):
            del r[1]

        def wrong_seal(r):
            r[1]["seal"] = "0" * 64

        def wrong_status(r):
            r[1]["status"] = "fail"

        def other_candidate(r):
            r[0]["candidate"] = "d" * 40

        def other_parent(r):
            r[2]["first_attempt"] = "first-other"

        def extra_first(r):
            r.append(stray)

        def extra_second(r):
            r.append(dict(stray, stage="second", attempt="second-stray",
                          first_attempt=r[0]["attempt"]))

        def extra_failed(r):
            r.append(stray)
            r.append(dict(stray, event="close", status=l.FAILED,
                          seal="0" * 64))

        cases = {"no opening": (forget_open,
                                "no opening|corrupt|chain|disagrees"),
                 "no close": (forget_close, "close does not name"),
                 "seal": (wrong_seal, "close does not name"),
                 "decision": (wrong_status, "close does not name"),
                 "candidate": (other_candidate, "disagrees"),
                 "parent": (other_parent, "disagrees"),
                 "second first attempt": (extra_first, "another judged"),
                 "second second attempt": (extra_second, "another judged")}
        for name, (edit, error) in cases.items():
            with self.subTest(case=name):
                self.edit_ledger(edit)
                try:
                    with self.assertRaisesRegex(ValueError, error):
                        l.replay(second)
                    if name == "second first attempt":
                        with self.assertRaisesRegex(ValueError, error):
                            l.replay(first)
                finally:
                    self.ledger.write_bytes(pristine)
        # A second close of the attempt is a corrupt ledger.
        self.edit_ledger(lambda r: r.append(dict(r[1], status=l.FAILED)))
        with self.assertRaisesRegex(ValueError, "corrupt attempts ledger"):
            l.replay(second)
        self.ledger.write_bytes(pristine)
        # A broken hash chain is refused.
        self.ledger.write_text(pristine.decode().replace(
            '"stage": "first"', '"stage": "first" ', 1))
        with self.assertRaisesRegex(ValueError, "chain|malformed"):
            l.replay(second)

    def test_candidate_extension_load_blocks_the_run(self):
        self.mutation = "extension"
        report = self.run_protocol()
        self.assertFalse(report["success"])
        self.assertIn("extension module loaded", report["failure"])
        # The baseline pilot ran first and was admitted; the candidate's
        # pilot stopped the run.
        self.assertEqual(self.processes, 2)

    def reject(self, mutation, error, processes=0):
        self.mutation = mutation
        report = self.run_protocol()
        self.assertFalse(report["success"])
        self.assertIn(error, report["failure"])
        self.assertEqual(self.processes, processes)
        return report

    def test_candidate_build_mutation(self):
        self.reject("candidate-build", "sealed input changed")

    def test_baseline_build_mutation(self):
        self.reject("baseline-build", "sealed input changed")

    def test_installation_mutation(self):
        self.reject("install", "sealed input changed")

    def test_unloaded_git_signature_mutation(self):
        self.reject("signature", "sealed input changed")

    def test_build_source_deletion(self):
        self.reject("delete", "No such file")

    def test_later_build_mutates_earlier_selection(self):
        self.reject("earlier-selection", "sealed input changed")

    def test_generated_fixture_mutation_in_build(self):
        self.reject("fixture-build", "sealed input changed")

    def test_post_build_mutation_still_rejected(self):
        self.reject("post-build", "source changed", processes=1)

    def test_library_mutation_before_final_seal_check(self):
        self.reject("library-bytes", "sealed input changed", processes=6)

    def test_same_bytes_symlink_retargeting_is_not_hidden(self):
        self.reject("symlink", "runtime library resolution changed", processes=6)

    def test_changed_dependency_resolution(self):
        self.reject("resolution", "runtime library resolution changed",
                    processes=6)

    def test_failed_discovery_blocks_before_builds_or_processes(self):
        report = self.reject("discovery-failure",
                             "runtime library discovery failed")
        self.assertEqual(self.builds, [])
        self.check_failed_discovery_receipt(report, "discovery")

    def test_failed_final_discovery_keeps_diagnostic_receipt(self):
        report = self.reject("recheck-failure",
                             "runtime library discovery failed", processes=6)
        self.check_failed_discovery_receipt(report, "recheck")

    def check_failed_discovery_receipt(self, report, key):
        info = report["dynamic_libraries"][key]
        path = self.repo / "output" / info["receipt"]
        self.assertEqual(l.a.seal(path), info["seal"])
        result = l.a.load(path)
        self.assertEqual(result["exit"], 1)
        self.assertEqual(result["stdout"], "not found\n")


if __name__ == "__main__":
    unittest.main()
