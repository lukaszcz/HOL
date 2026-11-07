#!/usr/bin/env python3
"""Loading provenance controls; synthetic builds/processes are NOT timings."""
from contextlib import nullcontext
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
        self.builds = []

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
                ["observation", "loading.raw", RAW],
                ["observation", "loading.extensions",
                 "SimpTracking" if self.mutation == "extension" and
                 dst.name == "candidate" else l.NO_EXTENSIONS],
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
        return dict(command=command, cwd=str(cwd), **receipt(text))

    def run_protocol(self, **changes):
        options = SimpleNamespace(
            repo=self.repo, baseline=self.pin, candidate=self.pin,
            module="congLib", pairs=1, reps=1, smoke=True, calibrate=False,
            timeout=30,
            authorize_measurements=True, api_audit=None,
            output=self.repo / "output")
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
        report = self.run_protocol(pairs=10, reps=2, smoke=False,
                                   calibrate=True)
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(report["mode"], "calibration")
        self.assertEqual((report["schema"], report["reps"]),
                         (l.SCHEMA, 2))
        self.assertEqual(self.processes, 2 + 2 * 10 * 2)
        self.assertEqual(report["policy"], l.a.EQUIVALENCE_POLICY)
        self.assertEqual(sorted({r["rep"] for r in report["runs"]}), [0, 1])
        self.assertEqual(report["jitter"]["pairs_for_target"], 10)
        out = self.repo / "output"
        self.assertEqual(l.replay(out), {"replayed": 42, "exit": None})
        # Tampering with a process receipt is caught by its seal.
        victim = out / report["runs"][5]["receipt"]
        victim.write_bytes(victim.read_bytes() + b"x")
        with self.assertRaisesRegex(ValueError, "changed process receipt"):
            l.replay(out)

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
