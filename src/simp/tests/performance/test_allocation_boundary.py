#!/usr/bin/env python3
"""SYNTHETIC tests of the TASK29B isolated-source boundary and of the
binding of the harness to its commit; NOT execution evidence.

Throwaway git repositories stand in for baseline, candidate and the
harness checkout. Nothing is read from or written to the real repository
except the reviewed manifest, which is only parsed.
"""
import ast
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import allocation_boundary as bd
import allocation_matrix as m
import allocation_schema as sc

SEQUENCE = "tools/sequences/seq"
KERNEL = "tools/sequences/kernel"
HEAP = "src/proofman"
GIT_ENV = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t",
               GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_SYSTEM="/dev/null")
FILES = {
    SEQUENCE: "#include sequences/kernel\nsrc/proofman\n"
              "!src/selftest_only\nsrc/compute/src\nsrc/marker\n"
              "src/combin\nsrc/simp/src\nsrc/late\n[sys]src/later\n",
    KERNEL: "# a comment\n!src/early_selftest\n[poly]src/early\n"
            "**KERNEL**\n(kernel)src/thm\n",
    "src/proofman/Holmakefile": "ZEROSTATE = $(HOLDIR)/bin/hol.state0\n",
    "src/early/E.sml": "e\n", "src/early/Holmakefile": "X = 1\n",
    "src/early_selftest/S.sml": "s\n", "src/thm/T.sml": "t\n",
    "src/late/L.sml": "l\n", "src/later/L.sml": "l\n",
    "src/selftest_only/S.sml": "s\n", "src/proofman/P.sml": "p\n",
    "src/compute/src/C.sml": "c\n", "src/marker/M.sml": "m\n",
    "src/combin/C.sml": "c\n", "src/0/K.sml": "k\n", "tools/x.sml": "x\n",
    "bin/b": "b\n",
    "src/simp/src/S.sml": "s\n", "doc/a.md": "a\n", "top.txt": "t\n",
}


def git(repo, *args):
    return subprocess.run(["git", "-C", str(repo), *args], env=GIT_ENV,
                          check=True, stdout=subprocess.PIPE,
                          text=True).stdout.strip()


def manifest(prefixes=("doc/", "src/late/"), files=()):
    return dict(schema=bd.SCHEMA,
                prefixes=[dict(path=p, reason="r") for p in prefixes],
                files=[dict(path=p, blob=b, reason="r") for p, b in files])


class Repo(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        self.write(FILES)
        self.baseline = self.commit("baseline")

    def write(self, files):
        for name, text in files.items():
            path = self.repo / name
            if text is None:
                path.unlink()
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def commit(self, message):
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--allow-empty", "-m", message)
        return git(self.repo, "rev-parse", "HEAD")

    def candidate(self, files):
        self.write(files)
        return self.commit("candidate")

    def blob(self, name):
        return git(self.repo, "rev-parse", "HEAD:" + name)

    def resolve(self, candidate, data=None):
        path = self.root / "manifest.json"
        path.write_text(json.dumps(manifest() if data is None else data))
        return bd.resolve(self.repo, self.baseline, candidate, SEQUENCE,
                          path)


class Resolve(Repo):
    def test_covered_differences_are_resolved_and_counted(self):
        cand = self.candidate({
            "src/simp/src/S.sml": "s2\n", "doc/a.md": "b\n",
            "doc/new.md": "n\n", "src/late/L.sml": "l2\n",
            "top.txt": "t2\n"})
        data = manifest(files=[("top.txt", self.blob("top.txt"))])
        found = self.resolve(cand, data)
        self.assertEqual((found["changed"], found["subject_changed"]),
                         (5, 1))
        self.assertEqual(found["prefixes"], {"doc/": 2, "src/late/": 1})
        self.assertEqual(found["files"], [dict(
            path="top.txt", blob=self.blob("top.txt"))])
        self.assertEqual(found["schema"], bd.SCHEMA)
        self.assertEqual((found["baseline"], found["candidate"]),
                         (self.baseline, cand))
        self.assertEqual((found["subject_directory"],
                          found["heap_directory"]),
                         ("src/simp/src", HEAP))
        self.assertEqual(found["manifest_prefixes"], ["doc/", "src/late/"])
        paths = ["doc/a.md", "doc/new.md", "src/late/L.sml",
                 "src/simp/src/S.sml", "top.txt"]
        self.assertEqual(found["changed_sha256"], hashlib.sha256(
            "\0".join(paths).encode()).hexdigest())
        self.assertEqual(found["manifest"], hashlib.sha256(
            (self.root / "manifest.json").read_bytes()).hexdigest())

    def test_the_record_depends_on_the_set_of_changed_paths(self):
        one = self.resolve(self.candidate({"doc/a.md": "b\n"}))
        two = self.resolve(self.candidate({"doc/c.md": "c\n"}))
        self.assertNotEqual(one["changed_sha256"], two["changed_sha256"])

    def test_no_difference_at_all_is_an_empty_boundary(self):
        found = self.resolve(self.baseline)
        self.assertEqual((found["changed"], found["subject_changed"],
                          found["prefixes"], found["files"]),
                         (0, 0, {}, []))

    def test_every_manifest_prefix_is_listed_changed_or_not(self):
        # The processes check "no file loaded under a prefix" against this
        # list: a prefix nothing changed under still guards the boundary.
        self.assertEqual(self.resolve(self.baseline)["manifest_prefixes"],
                         ["doc/", "src/late/"])
        found = self.resolve(self.candidate({"doc/a.md": "b\n"}))
        self.assertEqual(found["prefixes"], {"doc/": 1})
        self.assertEqual(found["manifest_prefixes"], ["doc/", "src/late/"])
        data = manifest(prefixes=("src/late/", "doc/"))
        self.assertEqual(self.resolve(self.baseline, data)[
            "manifest_prefixes"], ["doc/", "src/late/"])

    def test_an_unreviewed_difference_is_refused_before_anything_else(self):
        for name in ("top.txt", "src/proofman/P.sml", "src/early/E.sml",
                     "src/thm/T.sml", "src/0/K.sml", "tools/x.sml",
                     "bin/b", "src/selftest_only/S.sml", "src/later/L.sml",
                     "brand/new.txt", "src/simp/README", "src/simp/src.txt",
                     "src/simp/srcx/Y.sml", "src/simp/tests/x.sml"):
            with self.subTest(name):
                self.setUp()
                cand = self.candidate({name: "changed\n"})
                with self.assertRaisesRegex(
                        sc.InvalidAllocation,
                        "reviewed manifest does not cover: .*" +
                        name.replace(".", r"\.")):
                    self.resolve(cand)

    def test_a_deleted_path_is_a_difference_too(self):
        cand = self.candidate({"top.txt": None})
        with self.assertRaisesRegex(sc.InvalidAllocation, "top.txt"):
            self.resolve(cand)
        # a covered deletion is fine
        self.setUp()
        cand = self.candidate({"doc/a.md": None})
        self.assertEqual(self.resolve(cand)["prefixes"], {"doc/": 1})

    def test_an_exact_entry_is_pinned_to_its_blob(self):
        cand = self.candidate({"top.txt": "t2\n"})
        data = manifest(files=[("top.txt", self.blob("top.txt"))])
        self.assertEqual(self.resolve(cand, data)["files"][0]["path"],
                         "top.txt")
        later = self.candidate({"top.txt": "t3\n"})
        with self.assertRaisesRegex(sc.InvalidAllocation, "changed blob"):
            self.resolve(later, data)
        gone = self.candidate({"top.txt": None})
        with self.assertRaisesRegex(sc.InvalidAllocation, "deleted"):
            self.resolve(gone, data)

    def test_a_renamed_file_counts_as_two_paths(self):
        git(self.repo, "mv", "top.txt", "doc/top.txt")
        cand = self.commit("rename")
        with self.assertRaisesRegex(sc.InvalidAllocation, "top.txt"):
            self.resolve(cand)

    def test_the_most_specific_prefix_takes_the_count(self):
        cand = self.candidate({"doc/a.md": "b\n", "doc/sub/b.md": "c\n"})
        found = self.resolve(cand, manifest(prefixes=("doc/", "doc/sub/")))
        self.assertEqual(found["prefixes"], {"doc/": 1, "doc/sub/": 1})

    def test_a_list_of_unknown_paths_is_shortened(self):
        cand = self.candidate({"u%d.txt" % i: "x\n" for i in range(12)})
        with self.assertRaisesRegex(sc.InvalidAllocation, r"\.\.\.$"):
            self.resolve(cand)


class Manifest(Repo):
    def refuse(self, data, message):
        cand = self.candidate({"doc/a.md": "b\n"})
        with self.assertRaisesRegex(sc.InvalidAllocation, message):
            self.resolve(cand, data)

    def test_a_prefix_may_not_touch_what_is_built_before_the_subject(self):
        # the heap's inputs, and the libraries sigobj gives the fixture
        # after the heap: all are built before src/simp/src
        for prefix in ("src/early/", "src/", "src/proofman/", "src/thm/",
                       "src/0/", "src/0/sub/", "src/experimental-kernel/",
                       "src/marker/", "src/marker/sub/", "src/combin/",
                       "src/compute/", "src/compute/src/",
                       "src/compute/src/x/", "tools/", "tools/sequences/",
                       "tools-poly/", "bin/", "src/simp/", "src/simp/src/",
                       "src/simp/src/x/"):
            with self.subTest(prefix):
                self.refuse(manifest(prefixes=("doc/", prefix)),
                            "overlaps .*built before the subject")

    def test_prefixes_after_the_subject_or_selftest_only_are_allowed(self):
        for prefix in ("src/late/", "src/later/", "src/selftest_only/",
                       "src/early_selftest/", "src/simp/tests/", "doc/"):
            with self.subTest(prefix):
                cand = self.candidate({"doc/a.md": "b\n"})
                self.resolve(cand, manifest(
                    prefixes=tuple({"doc/", prefix})))

    def test_the_kernel_marker_stands_for_both_kernels(self):
        built = bd.barred_directories(self.repo, self.baseline, SEQUENCE)
        self.assertEqual(built, [
            "src/early/", "src/0/", "src/experimental-kernel/",
            "src/thm/", "src/proofman/", "src/compute/src/", "src/marker/",
            "src/combin/", "src/simp/src/"])
        # `!` entries are built only with -t, and the walk stops at the
        # subject directory, a constant and not a manifest value
        for name in ("src/late/", "src/later/", "src/selftest_only/",
                     "src/early_selftest/"):
            self.assertNotIn(name, built)
        self.assertEqual((bd.SUBJECT_DIRECTORY, bd.HEAP_DIRECTORY),
                         ("src/simp/src", HEAP))

    def test_the_subject_and_the_heap_must_be_built_in_that_order(self):
        def refuse(sequence, message, **files):
            self.write(dict({SEQUENCE: sequence}, **files))
            with self.assertRaisesRegex(sc.InvalidAllocation, message):
                self.resolve(self.commit("variant"))
        refuse("#include sequences/kernel\nsrc/late\n", "never builds the "
               "subject")
        refuse("!src/simp/src\nsrc/proofman\n", "never builds the subject")
        # the heap built only after the subject, or not at all
        refuse("src/simp/src\nsrc/proofman\n", "not built at or before")
        refuse("src/simp/src\n", "not built at or before")
        refuse("!src/proofman\nsrc/simp/src\n", "not built at or before")

    def test_the_heap_directory_must_deposit_the_heap(self):
        self.write({"src/proofman/Holmakefile": "X = 1\n"})
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "does not deposit"):
            self.resolve(self.commit("no heap"))
        self.write({"src/proofman/Holmakefile": None})
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "does not deposit"):
            self.resolve(self.commit("no makefile"))

    def test_the_manifest_cannot_name_the_heap_directory(self):
        self.refuse(dict(manifest(), heap_directory=HEAP),
                    "wrong manifest shape")

    def test_a_malformed_manifest_is_refused(self):
        good = manifest()
        entry = dict(path="doc/", reason="r")
        cases = (
            ("extra key", dict(good, more=1), "wrong manifest shape"),
            ("schema", dict(good, schema="other"), "wrong manifest shape"),
            ("not an object", [], "wrong manifest shape"),
            ("a number", 5, "wrong manifest shape"),
            ("slashless prefix", dict(good, prefixes=[
                entry, dict(path="doc2", reason="r")]),
             "prefix must end with /"),
            ("absolute", manifest(prefixes=("doc/", "/etc/")), "bad path"),
            ("parent", manifest(prefixes=("doc/", "doc/../src/")),
             "bad path"),
            ("empty component", manifest(prefixes=("doc/", "doc//x/")),
             "bad path"),
            ("backslash", manifest(prefixes=("doc/", "doc\\x/")),
             "bad path"),
            ("duplicate", manifest(prefixes=("doc/", "doc/")), "duplicate"),
            ("prefix as file", dict(good, files=[dict(
                path="x/", blob="0" * 40, reason="r")]), "bad file entry"),
            ("bad blob", manifest(files=[("top.txt", "xyz")]),
             "bad file entry"),
            ("empty reason", dict(good, prefixes=[entry, dict(
                path="doc2/", reason="")]), "empty field"),
            ("number as reason", dict(good, prefixes=[entry, dict(
                path="doc2/", reason=5)]), "empty field"),
            ("missing entry field", dict(good, prefixes=[entry, dict(
                path="doc2/")]), "malformed prefixes entry"),
            ("extra entry field", dict(good, prefixes=[entry, dict(
                path="doc2/", reason="r", more="x")]),
             "malformed prefixes entry"),
            ("entry not an object", dict(good, prefixes=[entry, 5]),
             "malformed prefixes entry"),
            ("not a list", dict(good, files={}), "bad files"))
        for label, data, message in cases:
            with self.subTest(label):
                self.refuse(data, "boundary: .*" + message)

    def test_a_sequence_that_includes_itself_is_refused(self):
        self.write({KERNEL: "#include sequences/seq\nsrc/early\n"})
        cand = self.commit("loop")
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "recursive include"):
            self.resolve(cand)

    def test_a_sequence_that_includes_itself_directly_is_refused(self):
        self.write({SEQUENCE: "#include sequences/seq\nsrc/proofman\n"})
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "recursive include tools/sequences/seq"):
            self.resolve(self.commit("self"))

    def test_git_failures_are_refusals(self):
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "git diff failed"):
            bd.changed_paths(self.repo, "0" * 40, self.baseline)
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "git ls-tree failed"):
            bd.candidate_blobs(self.repo, "0" * 40, ["top.txt"])
        self.assertEqual(bd.candidate_blobs(self.repo, self.baseline, []),
                         {})

    def test_a_missing_sequence_or_bad_entry_is_refused(self):
        self.write({KERNEL: "[poly src/early\n"})
        with self.assertRaisesRegex(sc.InvalidAllocation, "bad sequence"):
            self.resolve(self.commit("bad"))
        self.write({SEQUENCE: "#include sequences/none\n"})
        with self.assertRaisesRegex(sc.InvalidAllocation, "no sequence file"):
            self.resolve(self.commit("none"))

    def test_the_manifest_is_judged_at_the_candidates_sequence(self):
        # a candidate that builds a prefix's directory before the subject
        # changes what a prefix may cover
        self.write({SEQUENCE: "#include sequences/kernel\nsrc/proofman\n"
                              "src/late\nsrc/simp/src\n"})
        cand = self.commit("reorder")
        with self.assertRaisesRegex(sc.InvalidAllocation, "overlaps"):
            self.resolve(cand)


class Committed(unittest.TestCase):
    """The reviewed manifest of this checkout, as committed."""

    def test_it_is_well_formed_and_its_files_are_listed_once(self):
        data = bd.load_manifest(m.BOUNDARY)
        self.assertNotIn("heap_directory", data)
        for item in data["prefixes"] + data["files"]:
            self.assertLess(len(item["reason"]), 80)
        paths = [i["path"] for i in data["prefixes"] + data["files"]]
        self.assertEqual(len(paths), len(set(paths)))

    def test_no_prefix_touches_what_is_built_before_the_subject(self):
        root = m.HERE.parents[3]
        data = bd.load_manifest(m.BOUNDARY)
        built = bd.check_manifest(root, "HEAD", data, m.pr.HOL_SEQUENCE)
        # the libraries the fixture loads from sigobj after the heap are
        # inside the barred walk of the real sequence
        for name in ("src/proofman/", "src/compute/src/", "src/HolSat/",
                     "src/taut/", "src/marker/", "src/combin/", "src/lite/",
                     "src/refute/", "src/simp/src/"):
            self.assertIn(name, built)

    def test_every_listed_file_exists_with_its_blob(self):
        root = m.HERE.parents[3]
        data = bd.load_manifest(m.BOUNDARY)
        found = bd.candidate_blobs(root, "HEAD", [
            i["path"] for i in data["files"]])
        self.assertEqual(found, {i["path"]: i["blob"]
                                 for i in data["files"]})


class HarnessFiles(unittest.TestCase):
    """harness_files(): the files that decide a measurement, as listed."""

    def module_level(self, body):
        """Imports executed when the module loads, not those in functions."""
        for node in body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                yield node
            elif isinstance(node, (ast.Try, ast.If, ast.With)):
                parts = [node.body, getattr(node, "orelse", []),
                         getattr(node, "finalbody", [])]
                parts += [h.body for h in getattr(node, "handlers", [])]
                for part in parts:
                    yield from self.module_level(part)

    def imported(self):
        """Modules of this checkout that the driver imports at module
        level, transitively, as file names."""
        search = [m.HERE, m.HERE.parent / "compatibility",
                  m.HERE / "allocator-counter"]
        todo, seen, found = [m.HERE / "allocation_matrix.py"], set(), set()
        while todo:
            path = todo.pop()
            if path in seen:
                continue
            seen.add(path)
            for node in self.module_level(ast.parse(path.read_text()).body):
                if isinstance(node, ast.Import):
                    mods = [n.name.split(".")[0] for n in node.names]
                else:
                    mods = [node.module.split(".")[0]] if node.module else []
                for mod in mods:
                    for where in search:
                        if (where / (mod + ".py")).exists():
                            found.add(mod + ".py")
                            todo.append(where / (mod + ".py"))
        return found

    def test_every_listed_file_exists_once_and_fixtures_are_inputs(self):
        inputs, fixtures = m.harness_files()
        self.assertTrue(all(p.is_file() for p in inputs + fixtures))
        self.assertEqual(len(inputs), len(set(inputs)))
        self.assertLessEqual(set(fixtures), set(inputs))

    def test_every_module_the_driver_imports_is_listed(self):
        # Per task: what the driver imports at module level is in the
        # harness files of every task; a task's own case list, imported
        # only when the task is asked for, is in that task's.
        imported = self.imported()
        for name, task in ((n, m.TASKS[n]) for n in m.TASKS):
            listed = {p.name for p in m.harness_files(task)[0]}
            self.assertLessEqual(imported, listed | {
                "allocation_matrix.py"}, name)
        inputs, _ = m.harness_files()
        listed = {p.name for p in inputs}
        for name in ("allocation_boundary.py", "allocation_boundary.json",
                     "allocation_iterations.json", "path_schema.py",
                     "MatrixAllocation.sml", "MatrixSupport.sml",
                     "run_paired.py", "private_runtime.py", "bracket.c"):
            self.assertIn(name, listed)

    def test_the_task31_cases_are_not_imported_at_module_level(self):
        self.assertNotIn("task31_cases.py", self.imported())
        self.assertIn("task31_cases.py", {
            p.name for p in m.harness_files(m.TASKS["task31"])[0]})
        self.assertNotIn("task31_cases.py", {
            p.name for p in m.harness_files()[0]})

    def test_importing_the_matrix_does_not_load_the_task31_cases(self):
        code = (
            "import sys\n"
            "sys.dont_write_bytecode = True\n"
            "import allocation_matrix as m, task30_dispose\n"
            "assert 'task31_cases' not in sys.modules\n"
            "assert sorted(m.TASKS) == ['task29b', 'task30', 'task31']\n"
            "assert 'task31' in m.TASKS\n"
            "task = m.task_of({})\n"
            "assert task.name == 'task29b'\n"
            "m.keys(task)\n"
            "m.harness_files(m.task_named('task30'))\n"
            "m.load_iterations(task=m.task_named('task30'))\n"
            "assert 'task31_cases' not in sys.modules\n"
            "m.task_named('task31')\n"
            "assert 'task31_cases' in sys.modules\n")
        ran = subprocess.run(
            [sys.executable, "-B", "-c", code], cwd=m.HERE,
            stdin=subprocess.DEVNULL, capture_output=True, text=True)
        self.assertEqual(ran.returncode, 0, ran.stderr)

    def test_the_tasks_are_built_once_and_named_without_building(self):
        tasks = m.Tasks({"a": 1}, {"b": lambda: object()})
        self.assertEqual(sorted(tasks), ["a", "b"])
        self.assertIn("b", tasks)
        self.assertEqual(len(tasks), 2)
        self.assertIs(tasks["b"], tasks["b"])
        with self.assertRaises(KeyError):
            tasks["c"]

    def test_the_paired_fixtures_are_inputs_and_the_sml_ones_fixtures(self):
        inputs, fixtures = m.harness_files()
        paired = sorted((m.HERE.parent / "compatibility" /
                         "paired").iterdir())
        self.assertTrue(paired)
        self.assertLessEqual({p for p in paired if p.is_file()},
                             set(inputs))
        self.assertEqual(
            {p.name for p in fixtures},
            set(m.FIXTURES) | {p.name for p in paired
                               if p.suffix == ".sml"})

    def test_library_names_are_unambiguous(self):
        seal = dict(sha256="1", bytes=2)
        self.assertEqual(m.library_names({"/a/libc.so.6": seal}),
                         {"libc.so.6": seal})
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "ambiguous library name: libc.so.6"):
            m.library_names({"/a/libc.so.6": seal, "/b/libc.so.6": seal})


class Harness(Repo):
    """harness_binding over a throwaway checkout laid out like the repo."""
    PERF = "src/simp/tests/performance/"

    def setUp(self):
        super().setUp()
        self.write({self.PERF + "driver.py": "d\n",
                    self.PERF + "Fix.sml": "f\n",
                    self.PERF + "other.py": "o\n"})
        self.candidate_commit = self.commit("candidate with harness")
        self.inputs = [self.repo / self.PERF / "driver.py",
                       self.repo / self.PERF / "Fix.sml"]
        self.fixtures = [self.repo / self.PERF / "Fix.sml"]

    def bind(self, candidate=None):
        return m.harness_binding(self.repo, candidate or
                                 self.candidate_commit, self.inputs,
                                 self.fixtures)

    def test_a_clean_committed_harness_is_bound_to_its_blobs(self):
        found = self.bind()
        self.assertEqual(found["head"], self.candidate_commit)
        self.assertIs(found["dirty"], False)
        self.assertEqual(found["fixtures"], [self.PERF + "Fix.sml"])
        self.assertEqual(found["blobs"], {
            self.PERF + n: self.blob(self.PERF + n)
            for n in ("driver.py", "Fix.sml")})
        self.assertEqual(found["tree_outside_performance"],
                         m.pr.tree_outside_performance(
                             self.repo, self.candidate_commit))

    def test_a_file_that_is_not_its_blob_is_refused_by_its_hash_too(self):
        # independent of the cleanliness check: the file is hashed
        identity = m.pr.harness_identity(self.repo, self.candidate_commit)
        (self.repo / self.PERF / "driver.py").write_text("weaker\n")
        with mock.patch.object(m.pr, "harness_identity",
                               return_value=identity):
            with self.assertRaisesRegex(sc.InvalidAllocation,
                                        "differs from its commit"):
                self.bind()

    def test_a_locally_weakened_file_is_refused(self):
        for name in ("driver.py", "Fix.sml"):
            with self.subTest(name):
                (self.repo / self.PERF / name).write_text("weaker\n")
                with self.assertRaisesRegex(ValueError, "not clean"):
                    self.bind()
                git(self.repo, "checkout", "--", ".")

    def test_the_agent_state_of_a_fresh_clone_does_not_dirty_it(self):
        lock = self.repo / ".agent-files/hol4-performance-1.lock"
        lock.parent.mkdir()
        lock.write_text("")
        self.assertEqual(self.bind()["head"], self.candidate_commit)
        (self.repo / ".agent-files-x").write_text("n\n")
        with self.assertRaisesRegex(ValueError, "not clean"):
            self.bind()

    def test_an_untracked_input_is_refused(self):
        (self.repo / self.PERF / "new.py").write_text("n\n")
        with self.assertRaisesRegex(ValueError, "not clean"):
            m.harness_binding(self.repo, self.candidate_commit,
                              self.inputs + [self.repo / self.PERF /
                                             "new.py"], self.fixtures)

    def test_a_committed_input_that_is_ignored_by_git_is_refused(self):
        stray = self.repo / self.PERF / "stray.py"
        stray.write_text("s\n")
        with self.assertRaisesRegex(sc.InvalidAllocation, "not committed"):
            git(self.repo, "add", "-A")
            git(self.repo, "reset", "-q", "--", self.PERF + "stray.py")
            (self.repo / ".git/info/exclude").write_text(
                self.PERF + "stray.py\n")
            m.harness_binding(self.repo, self.candidate_commit,
                              self.inputs + [stray], self.fixtures)

    def test_a_fixture_other_than_the_candidates_is_refused(self):
        self.write({self.PERF + "Fix.sml": "f2\n"})
        head = self.commit("fixture moved on")
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "candidate's committed blob"):
            self.bind(self.candidate_commit)
        self.assertEqual(self.bind(head)["head"], head)

    def test_a_fixture_absent_from_the_candidate_is_refused(self):
        self.write({self.PERF + "Late.sml": "l\n"})
        self.commit("fixture added after the candidate")
        late = [self.repo / self.PERF / "Late.sml"]
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "candidate's committed blob"):
            m.harness_binding(self.repo, self.candidate_commit,
                              self.inputs + late, late)

    def test_the_harness_may_not_differ_outside_the_performance_area(self):
        self.write({"top.txt": "changed\n"})
        self.commit("not a harness change")
        with self.assertRaisesRegex(ValueError, "outside the performance"):
            self.bind(self.candidate_commit)

    def test_the_harness_may_differ_below_the_performance_area(self):
        self.write({self.PERF + "other.py": "o2\n"})
        self.commit("only a harness change")
        self.assertEqual(self.bind()["fixtures"], [self.PERF + "Fix.sml"])


if __name__ == "__main__":
    unittest.main()
