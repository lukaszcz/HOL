"""Controls are synthetic except the separately authorized runtime driver."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
COUNTER = HERE / "allocator-counter"
sys.path.insert(0, str(COUNTER))
import control_schema as s
import private_runtime as pr
import run_controls as driver


def synthetic():
    lines = ["@@TASK29_ALLOC_SCOPE_V1\tcontrols-only; not full runtime "
             "validation",
             "@@TASK29_ALLOC_RUNTIME_V1\t/synthetic/libpolyml.so.16",
             "@@TASK29_ALLOC_ABI_V1\t15"]
    count = [100, 100, 0, 0, 0]
    layouts = []
    for label in s.LABELS:
        d = [4, 4, 0, 0, 0]
        if label.startswith(("word-array-", "byte-array-", "ref-list-")):
            n = int(label.rsplit("-", 1)[1])
            words = (n+1 if label.startswith("word-array-") else
                     4+(n+7)//8 if label.startswith("byte-array-") else 5*n)
            d = [4+words, 4+words, 0, 0, 0]
            layouts.append(f"@@TASK29_ALLOC_LAYOUT_V1\t{label}\t{n}\t"
                           f"{words}\t{d[0]}\t4\t{8*d[0]}")
        if label == "rts-bignum-multiply":
            d = [14, 4, 10, 0, 0]
        if label == "compile-retained-entry-closure":
            d = [14, 4, 0, 0, 10]
        for side, c in (("start", count),
                        ("end", [a+b for a, b in zip(count, d)])):
            lines.append("\t".join(["@@TASK29_ALLOC_ENDPOINT_V1", label,
                                   side, *map(str, [1, 8, 0, *c])]))
        count = [a+b for a, b in zip(count, d)]
        lines.append("\t".join(["@@TASK29_ALLOC_DELTA_V1", label,
                                *map(str, d)]))
    lines += layouts
    lines += ["@@TASK29_ALLOC_NOOP_V1\t4\t4\t0\t0\t0",
              "@@TASK29_ALLOC_UNCLAIMED_V1\tfull runtime; TASK29B matrix",
              "@@TASK29_ALLOC_CONTROLS_COMPLETE_V1\t34"]
    return "\n".join(lines) + "\n"


class ControlSchemaTests(unittest.TestCase):
    def test_complete_synthetic_protocol(self):
        result = s.observations(synthetic())
        self.assertEqual(result["brackets"], 34)
        self.assertEqual(result["no_op_words"], [4, 4, 0, 0, 0])

    def test_missing_duplicate_and_reordered_records(self):
        lines = synthetic().splitlines()
        for prefix in ("ENDPOINT", "DELTA", "LAYOUT", "ABI", "NOOP",
                       "CONTROLS_COMPLETE"):
            i = next(i for i, line in enumerate(lines)
                     if line.startswith("@@TASK29_ALLOC_" + prefix))
            for changed in (lines[:i]+lines[i+1:],
                            lines[:i]+[lines[i]]+lines[i:]):
                with self.subTest(prefix=prefix), \
                        self.assertRaises(ValueError):
                    s.observations("\n".join(changed))
        i = next(i for i, line in enumerate(lines)
                 if line.startswith("@@TASK29_ALLOC_ENDPOINT"))
        lines[i], lines[i+1] = lines[i+1], lines[i]
        with self.assertRaises(ValueError):
            s.observations("\n".join(lines))

    def test_uint64_and_metadata(self):
        text = synthetic()
        for bad in ("1\t4\t0", "1\t8\t1", "2\t8\t0",
                    "1\t8\t-1", "1\t8\t01", f"1\t8\t{2**64}"):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                s.observations(text.replace("1\t8\t0", bad, 1))

    def test_changed_delta_endpoint_and_layout(self):
        text = synthetic()
        for old, new in (
            ("noop-warmup-1\t4\t4\t0\t0\t0", "noop-warmup-1\t5\t5\t0\t0\t0"),
            ("start\t1\t8\t0\t100\t100", "start\t1\t8\t0\t101\t100"),
            ("word-array-0\t0\t1\t5\t4\t40", "word-array-0\t0\t1\t5\t4\t41"),
            ("CONTROLS_COMPLETE_V1\t34", "CONTROLS_COMPLETE_V1\t33"),
            ("ABI_V1\t15", "ABI_V1\t7")):
            self.assertIn(old, text)
            with self.subTest(old=old), self.assertRaises(ValueError):
                s.observations(text.replace(old, new, 1))

    def test_no_unknown_or_unscoped_record(self):
        for text in (synthetic()+"@@TASK29_ALLOC_FUTURE_V1\t1\n",
                     synthetic().replace("controls-only", "acceptance"),
                     synthetic().replace("TASK29B matrix", "all passed")):
            with self.assertRaises(ValueError):
                s.observations(text)

    def test_completion_cannot_precede_observations(self):
        lines = synthetic().splitlines()
        lines.insert(0, lines.pop())
        with self.assertRaisesRegex(ValueError, "after completion"):
            s.observations("\n".join(lines))

    def test_physical_slope_not_just_positive_counts(self):
        # Consistently multiply every endpoint/delta by 2. Sums, positivity and
        # monotonicity survive; exact physical allocation semantics must not.
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            if p[0].endswith("ENDPOINT_V1"):
                p[6:] = [str(2*int(n)) for n in p[6:]]
            elif p[0].endswith("DELTA_V1"):
                p[2:] = [str(2*int(n)) for n in p[2:]]
            elif p[0].endswith("NOOP_V1"):
                p[1:] = [str(2*int(n)) for n in p[1:]]
            lines[i] = "\t".join(p)
        with self.assertRaises(ValueError):
            s.observations("\n".join(lines))

    def test_gc_and_noop_repeat_are_strict(self):
        text = synthetic()
        for label in ("noop-repeat-1", "gc-with-retained-arrays-1"):
            # Changing just a delta is already rejected at the endpoint guard.
            with self.subTest(label=label), self.assertRaises(ValueError):
                s.observations(text.replace(label+"\t4\t4\t0\t0\t0",
                                            label+"\t5\t5\t0\t0\t0"))


class IdentityTests(unittest.TestCase):
    def test_actual_symbol_and_single_process_mapping(self):
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp) / "libpolyml.so.16.0.0"
            lib.write_bytes(b"synthetic, not executable")
            text = (f"@@TASK29_ALLOC_RUNTIME_V1\t{lib}\n"
                    f"@@TASK29_ALLOC_MAP_V1\t100-200 r-xp 0 00:00 1 {lib}\n")
            self.assertEqual(driver.runtime_identity(text, lib)["symbol"],
                             str(lib))
            for changed in ("", text+text,
                text + "@@TASK29_ALLOC_MAP_V1\t200-300 r-xp 0 00:00 2 "
                "/other/libpolyml.so\n",
                text.replace("@@TASK29_ALLOC_MAP_V1", "unrecorded")):
                with self.subTest(changed=changed), \
                        self.assertRaises(Exception):
                    driver.runtime_identity(changed, lib)

    def test_authorization_required_before_build(self):
        with self.assertRaises(SystemExit):
            driver.main(["--output", "/nonexistent/forbidden.json"])

    def test_bootstrap_lineage_and_positive_timeout_are_required(self):
        base = ["--output", "/nonexistent/forbidden.json",
                "--authorize-experimental-runtime"]
        for extra in ([], ["--timeout", "0", "--bootstrap-hol"],
                      ["--timeout", "-5", "--bootstrap-hol"]):
            with self.subTest(extra=extra), self.assertRaises(SystemExit), \
                    contextlib.redirect_stderr(io.StringIO()):
                driver.main(base + extra)
        self.assertEqual(driver.arguments(base + ["--bootstrap-hol"]).
                         reference, "simplifier")

    def test_every_loaded_sml_source_is_copied_to_the_fixture(self):
        # A launcher referencing a structure that is not copied fails only
        # in the (long) authorized run; check the list here.
        for name in driver.FIXTURE_SOURCES:
            self.assertTrue((COUNTER / name).is_file(), name)
        sources = {p.name for p in COUNTER.glob("*.sml")}
        self.assertLessEqual(sources, set(driver.FIXTURE_SOURCES))
        makefile = (COUNTER / "Holmakefile").read_text()
        for launcher in driver.LAUNCHERS:
            self.assertIn(launcher, makefile)

    def test_pinned_source_and_patch(self):
        # Optional source availability; the authorized driver always runs it.
        if not driver.DEFAULT_SOURCE.is_dir():
            self.skipTest("local pristine Poly/ML distribution unavailable")
        patched = driver.verify_source(driver.DEFAULT_SOURCE)
        self.assertEqual(len(patched), 8)
        # The lower-level allocator records path diagnostics only. Counting
        # there would charge segments and retries, not reservations.
        processes = patched["libpolyml/processes.cpp"].decode()
        self.assertIn("RecordManagedFindSuccess", processes)
        for hook in ("RecordManagedAllocation(",
                     "RecordManagedInterpreterAllocation("):
            self.assertNotIn(hook, processes)


NM_BRACKET = """\
                 U PolyManagedAllocPathSnapshotV1
                 U PolyManagedAllocSnapshotV1
                 U PolyManagedInterpreterAllocSnapshotV1
                 w _ITM_deregisterTMCloneTable
                 w _ITM_registerTMCloneTable
                 w __cxa_finalize@GLIBC_2.17
                 w __gmon_start__
                 U __stack_chk_fail@GLIBC_2.17
                 U __stack_chk_guard@GLIBC_2.17
                 U abort@GLIBC_2.17
                 U dladdr@GLIBC_2.34
                 U fputc@GLIBC_2.17
                 U fputs@GLIBC_2.17
                 U memcmp@GLIBC_2.17
                 U memcpy@GLIBC_2.17
                 U memset@GLIBC_2.17
                 U stderr@GLIBC_2.17
"""
NM_LIMIT = "".join("                 U %s@GLIBC_2.17\n" % n for n in (
    "close", "fwrite", "getrlimit", "open", "read", "setrlimit", "sysconf"))


class ShimGuardTests(unittest.TestCase):
    """Negative controls of the guards run_controls and the matrix share."""

    def rejected(self, call, *args, why):
        with self.assertRaisesRegex(Exception, why):
            call(*args)

    def test_shim_import_allowlist_is_exact(self):
        self.assertEqual(len(pr.shim_imports(NM_BRACKET, False)), 17)
        self.assertEqual(len(pr.shim_imports(NM_BRACKET + NM_LIMIT, True)),
                         24)
        # Only the shim with failure_limit.c may import the limit functions.
        self.rejected(pr.shim_imports, NM_BRACKET + NM_LIMIT, False,
                      why="outside the allowlist: close fwrite")
        for name in ("pthread_create", "thrd_create", "clone", "clone3",
                     "fork", "vfork", "popen", "system", "execve", "socket",
                     "mmap", "dlopen", "signal", "malloc"):
            with self.subTest(name=name):
                for extended in (False, True):
                    self.rejected(
                        pr.shim_imports,
                        NM_BRACKET + "                 U %s@GLIBC_2.17\n"
                        % name, extended, why="outside the allowlist: "
                        + name)

    def test_shim_must_import_the_counter_snapshots_and_parse_cleanly(self):
        for name in pr.COUNTER_SYMBOLS:
            lines = [l for l in NM_BRACKET.splitlines(True)
                     if name + "\n" not in l]
            self.rejected(pr.shim_imports, "".join(lines), False,
                          why="does not import the counter snapshots")
        self.rejected(pr.shim_imports, NM_BRACKET + "garbage\n", False,
                      why="malformed shim import")
        self.rejected(pr.shim_imports, NM_BRACKET + "   T defined\n", False,
                      why="malformed shim import")
        self.rejected(pr.shim_imports, NM_BRACKET + "  X  weird\n", False,
                      why="malformed shim import")
        self.rejected(pr.shim_imports, b"bytes", False,
                      why="malformed nm output")
        # An allowlisted name with a symbol version is the same import.
        self.assertIn("abort", pr.shim_imports(
            NM_BRACKET.replace("abort@GLIBC_2.17", "abort"), False))

    def test_counter_exports_are_all_required(self):
        symbols = "".join("0000 T %s\n" % n for n in pr.COUNTER_SYMBOLS)
        pr.counter_exports(symbols)
        for name in pr.COUNTER_SYMBOLS:
            self.rejected(pr.counter_exports,
                          symbols.replace(" T " + name, " t " + name),
                          why="counter symbols not exported")
            self.rejected(pr.counter_exports,
                          symbols.replace(name + "\n", name + "x\n"),
                          why="counter symbols not exported")
        self.rejected(pr.counter_exports, "", why="not exported")
        self.rejected(pr.counter_exports, None, why="malformed nm output")

    def test_compact32_and_backend_are_rejected_from_the_real_config(self):
        good = "#define HOSTARCHITECTURE_AARCH64 1\n"
        pr.reject_compact32(good)
        self.rejected(pr.reject_compact32, "", why="wrong backend")
        self.rejected(pr.reject_compact32,
                      "#define HOSTARCHITECTURE_X86_64 1\n",
                      why="wrong backend")
        self.rejected(pr.reject_compact32, good + "#define POLYML32IN64 1\n",
                      why="compact32 runtime configuration")
        self.assertEqual(pr.CONFIGURE_ARGUMENTS, (
            "--without-x", "--disable-compact32bit", "--enable-shared"))

    def test_seals_are_checked_while_and_after_the_tree_exists(self):
        with tempfile.TemporaryDirectory() as tmp, \
                tempfile.TemporaryDirectory() as keep:
            scratch, outside = Path(tmp), Path(keep) / "input"
            inside = scratch / "product"
            inside.write_text("a")
            outside.write_text("b")
            seals = {str(inside): pr.a.seal(inside),
                     str(outside): pr.a.seal(outside)}
            self.assertEqual(pr.check_transient(seals, scratch),
                             {str(inside): seals[str(inside)]})
            inside.write_text("changed")
            self.rejected(pr.check_transient, seals, scratch,
                          why="sealed input changed")
            # While the temporary tree exists, persistence is premature.
            self.rejected(pr.check_persistent, seals, scratch,
                          why="not deleted")
            inside.unlink()
            scratch.rmdir()
            self.rejected(pr.check_transient, seals, scratch,
                          why="already deleted")
            pr.check_persistent(seals, scratch)
            outside.write_text("tampered")
            self.rejected(pr.check_persistent, seals, scratch,
                          why="sealed input changed")
            scratch.mkdir()  # let the temporary directory clean up


class ToolSealTests(unittest.TestCase):
    """The build tools a PATH resolves to are sealed, nothing else is
    consulted."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        for tool in pr.BUILD_TOOLS:
            (self.bin / tool).write_text("tool " + tool + "\n")
            (self.bin / tool).chmod(0o755)
        for _, program in pr.COMPILER_PROGRAMS:
            (self.root / program).write_text("program " + program + "\n")
        self.ran = []

    def runner(self, command):
        self.ran.append(list(command))
        out = ""
        if command[-1].startswith("-print-prog-name="):
            out = str(self.root / command[-1].split("=", 1)[1]) + "\n"
        return dict(stdout=out)

    def test_tools_and_compiler_programs_are_sealed_and_run(self):
        env = dict(PATH=str(self.bin))
        seals = pr.seal_tools(env, self.runner)
        wanted = {str(self.bin / t) for t in pr.BUILD_TOOLS} | {
            str(self.root / p) for _, p in pr.COMPILER_PROGRAMS}
        self.assertEqual(set(seals), wanted)
        for path, seal in seals.items():
            self.assertEqual(seal, pr.a.seal(path))
        for tool in pr.BUILD_TOOLS:
            self.assertIn([str(self.bin / tool), "--version"], self.ran)
        for compiler, program in pr.COMPILER_PROGRAMS:
            self.assertIn([compiler, "-print-prog-name=" + program],
                          self.ran)

    def test_a_tool_off_the_given_path_is_missing(self):
        env = dict(PATH=str(self.bin))
        (self.bin / "make").unlink()
        with self.assertRaisesRegex(Exception, "missing tool: make"):
            pr.seal_tools(env, self.runner)
        # the caller's own PATH is never consulted
        with mock.patch.dict(os.environ, PATH=str(self.bin)):
            with self.assertRaisesRegex(Exception, "missing tool: gcc"):
                pr.seal_tools(dict(PATH=str(self.root / "empty")),
                              self.runner)

    def test_a_missing_compiler_program_is_refused(self):
        (self.root / "cc1").unlink()
        with self.assertRaisesRegex(Exception, "compiler internal"):
            pr.seal_tools(dict(PATH=str(self.bin)), self.runner)

    def test_a_changed_tool_has_another_seal(self):
        env = dict(PATH=str(self.bin))
        before = pr.seal_tools(env, self.runner)
        (self.bin / "gcc").write_text("another compiler\n")
        after = pr.seal_tools(env, self.runner)
        self.assertNotEqual(before[str(self.bin / "gcc")],
                            after[str(self.bin / "gcc")])

    def test_the_controls_driver_seals_through_the_same_function(self):
        report = dict(inputs={})
        driver.seal_tools(dict(PATH=str(self.bin)), self.runner, report)
        self.assertEqual(report["inputs"], pr.seal_tools(
            dict(PATH=str(self.bin)), self.runner))


GIT = ["git", "-c", "user.name=t", "-c", "user.email=t@example.com",
       "-c", "commit.gpgsign=false"]


class HarnessIdentityTests(unittest.TestCase):
    """The harness checkout against the reference, in a throwaway repo."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        self.git("init", "-q", "-b", "reference")
        self.write("src/other/a.sml", "a")
        self.write(pr.PERFORMANCE_DIR + "x.py", "x")
        self.write(pr.PERFORMANCE_DIR + "allocator-counter/y.sml", "y")
        self.commit("base")
        self.git("branch", "harness")
        self.git("checkout", "-q", "harness")

    def git(self, *args):
        env = dict(os.environ, GIT_CONFIG_GLOBAL="/dev/null",
                   GIT_CONFIG_SYSTEM="/dev/null")
        subprocess.run([*GIT, "-C", str(self.repo), *args], check=True,
                       env=env, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)

    def write(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def commit(self, message):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def test_identical_and_performance_only_differences_are_accepted(self):
        record = pr.harness_identity(self.repo, "reference")
        self.assertEqual(record["dirty"], False)
        self.assertEqual(record["reference"], "reference")
        self.assertEqual(record["head"], record["reference_commit"])
        self.write(pr.PERFORMANCE_DIR + "x.py", "changed")
        self.write(pr.PERFORMANCE_DIR + "new/z.sml", "new")
        self.git("rm", "-q", "-f", pr.PERFORMANCE_DIR +
                 "allocator-counter/y.sml")
        self.commit("performance only")
        moved = pr.harness_identity(self.repo, "reference")
        self.assertNotEqual(moved["head"], moved["reference_commit"])
        self.assertEqual(moved["tree_outside_performance"],
                         record["tree_outside_performance"])

    def test_any_difference_outside_the_performance_area_is_refused(self):
        for name, text in (("src/other/a.sml", "changed"),
                           ("src/other/new.sml", "new"),
                           ("src/simp/tests/other.sml", "sibling"),
                           ("src/simp/tests/performance-x/q.sml", "near")):
            with self.subTest(name=name):
                self.write(name, text)
                self.commit("outside " + name)
                with self.assertRaisesRegex(Exception,
                                            "outside the performance"):
                    pr.harness_identity(self.repo, "reference")
                self.git("reset", "-q", "--hard", "reference")

    def test_dirty_untracked_and_unknown_references_are_refused(self):
        self.write("src/other/a.sml", "dirty")
        with self.assertRaisesRegex(Exception, "not clean"):
            pr.harness_identity(self.repo, "reference")
        self.git("checkout", "-q", "--", "src/other/a.sml")
        self.write(pr.PERFORMANCE_DIR + "untracked.py", "u")
        with self.assertRaisesRegex(Exception, "not clean"):
            pr.harness_identity(self.repo, "reference")
        (self.repo / (pr.PERFORMANCE_DIR + "untracked.py")).unlink()
        pr.harness_identity(self.repo, "reference")
        with self.assertRaises(subprocess.CalledProcessError):
            pr.harness_identity(self.repo, "no-such-reference")

    def test_a_fresh_clone_holding_the_serial_lock_is_clean(self):
        # serial_lock puts its lock under .agent-files, which a fresh clone
        # does not ignore; the cleanliness check runs inside that lock.
        clone = Path(self.tmp.name) / "clone"
        subprocess.run([*GIT, "clone", "-q", "-b", "harness",
                        str(self.repo), str(clone)], check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        with pr.a.serial_lock(clone):
            self.assertTrue((clone / pr.AGENT_STATE).is_dir())
            (clone / pr.AGENT_STATE / "evidence").mkdir()
            (clone / pr.AGENT_STATE / "evidence/log.txt").write_text("l")
            self.assertEqual(
                pr.harness_identity(clone, "origin/reference")["dirty"], False)

    def test_only_the_top_level_agent_state_directory_is_ignored(self):
        for name in ("src/other/" + pr.AGENT_STATE + "/x",
                     pr.AGENT_STATE + "-more/x", pr.AGENT_STATE + "x",
                     "x" + pr.AGENT_STATE):
            with self.subTest(name):
                self.write(name, "u")
                with self.assertRaisesRegex(Exception, "not clean"):
                    pr.harness_identity(self.repo, "reference")
                (self.repo / name).unlink()
        # tracked files elsewhere that change are still refused while the
        # agent state is present
        self.write(pr.AGENT_STATE + "/lock", "l")
        pr.harness_identity(self.repo, "reference")
        self.write("src/other/a.sml", "dirty")
        with self.assertRaisesRegex(Exception, "not clean"):
            pr.harness_identity(self.repo, "reference")

    def test_tree_identity_needs_a_performance_area(self):
        self.git("rm", "-q", "-r", "src/simp")
        self.commit("no performance area")
        with self.assertRaisesRegex(Exception, "no performance area"):
            pr.tree_outside_performance(self.repo, "HEAD")


if __name__ == "__main__":
    unittest.main()
