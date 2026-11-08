#!/usr/bin/env python3
"""The reviewed table of TASK31 differences (task31_attribution.py)."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import acceptance as a
import task31_attribution as attr
import task31_cases as c
import task31_pins as pins
import timing_grid as tg

REPO = a.HERE.parents[3]
B, C = "1" * 40, "2" * 40


def entry(path="src/simp/src/A.sig", kind="source", old=B, new=C):
    return dict(path=path, kind=kind, baseline_blob=old, candidate_blob=new,
                reason="why", gate="gate 2")


class Shipped(unittest.TestCase):
    def test_the_shipped_file_is_valid_and_holds_the_reviewed_files(self):
        document = attr.load()
        paths = [e["path"] for e in document["entries"]]
        self.assertEqual(paths, sorted(paths))
        self.assertIn("src/simp/src/Cond_rewr.sig", paths)
        self.assertNotIn("src/simp/src/SimpTracking.sml", paths)
        self.assertEqual(document["history"], {})

    def test_the_heap_file_names_the_startup_gate(self):
        found = {e["path"]: e for e in attr.load()["entries"]}
        reason = found["src/1/ThmAttribute.sml"]["reason"]
        self.assertEqual(
            reason, "in hol.state0; measured exactly by the startup gate "
            "(gate 5) hol-startup/first-use kinds, and by TASK_32/33 "
            "independent builds")
        self.assertEqual(found["src/1/ThmAttribute.sig"]["kind"], "heap")

    def test_the_candidate_blobs_are_filled_and_pin_the_sources(self):
        document = attr.load()
        self.assertEqual(attr.unfilled(document["entries"]), [])
        for e in document["entries"]:
            found = subprocess.run(
                ["git", "log", "-1", "-m", "--format=%H",
                 "--find-object=" + e["candidate_blob"], "HEAD", "--",
                 e["path"]], cwd=REPO, capture_output=True, text=True,
                stdin=subprocess.DEVNULL, check=True).stdout
            self.assertRegex(found, "^[0-9a-f]{40}\n$", e["path"])
        sources = {e["path"]: dict(blob=e["candidate_blob"],
                                   reason=e["reason"])
                   for e in document["entries"] if e["kind"] == "source"}
        self.assertEqual(pins.pins(document["entries"], c.SOURCES), sources)

    def test_the_baseline_blobs_are_those_of_git(self):
        for e in attr.load()["entries"]:
            self.assertEqual(e["baseline_blob"],
                             tg.git_blob(REPO, a.BASE, e["path"]), e["path"])

    def test_the_shipped_source_entries_are_among_the_timing_sources(self):
        import task31_grid as g
        document = attr.load()
        sources = {e["path"] for e in document["entries"]
                   if e["kind"] == "source"}
        self.assertTrue(sources)
        self.assertLessEqual(sources, set(g.TABLE.sources))


class Validate(unittest.TestCase):
    def refused(self, entries):
        with self.assertRaises(ValueError):
            pins.validate(entries)

    def test_good_entries_pass(self):
        pins.validate([entry(), entry("src/x/Holmakefile", "build")])
        pins.validate([entry(new=None)])

    def test_malformed_entries_are_refused(self):
        self.refused("no")
        self.refused([dict(entry(), extra=1)])
        self.refused([entry(kind="other")])
        self.refused([entry(old="short")])
        self.refused([entry(new="A" * 40)])
        self.refused([dict(entry(), reason=" ")])
        self.refused([dict(entry(), gate="")])
        self.refused([entry(path="src/x/Holmakefile")])  # source kind
        self.refused([entry(new=B)])
        self.refused([entry("src/b/B.sig"), entry("src/a/A.sig")])
        self.refused([entry(), entry()])


class Files(unittest.TestCase):
    def write(self, **more):
        tmp = tempfile.TemporaryDirectory(prefix="task31-attr-")
        self.addCleanup(tmp.cleanup)
        path = Path(tmp.name) / "t.json"
        document = dict(schema=pins.SCHEMA, entries=[entry()], history={})
        document.update(more)
        path.write_text(json.dumps(document))
        return path

    def test_load_returns_the_seal_of_the_file(self):
        path = self.write()
        document = attr.load(path)
        self.assertEqual(document["seal"], a.seal(path))
        self.assertEqual(
            pins.pins(document["entries"], ["src/simp/src/A.sig"]),
            {"src/simp/src/A.sig": dict(blob=C, reason="why")})
        self.assertEqual(pins.pins(document["entries"], []), {})

    def test_another_schema_or_extra_field_is_refused(self):
        for bad in (dict(schema="x"), dict(extra=1)):
            with self.assertRaises(ValueError):
                attr.load(self.write(**bad))

    def test_the_history_keeps_the_entries_an_earlier_seal_judged(self):
        old = [entry(new="3" * 40)]
        digest = "a" * 64
        document = attr.load(self.write(history={digest: old}))
        self.assertEqual(attr.entries_of(document, document["seal"]),
                         document["entries"])
        self.assertEqual(attr.entries_of(document, {"sha256": digest}), old)
        with self.assertRaises(ValueError):
            attr.entries_of(document, {"sha256": "b" * 64})
        self.assertIn("src/simp/src/A.sig", attr.paths(document))
        history = pins.pin_history(document, ["src/simp/src/A.sig"])
        self.assertEqual(history[digest]["src/simp/src/A.sig"]["blob"],
                         "3" * 40)
        self.assertEqual(pins.pin_history(document, []), {digest: {}})

    def test_the_digest_follows_the_entries(self):
        self.assertEqual(attr.digest([entry()]), attr.digest([entry()]))
        self.assertNotEqual(attr.digest([entry()]), attr.digest([]))


class Account(unittest.TestCase):
    def classes(self, blobs, entries=(), loaded=()):
        return {p: v[0] for p, v in
                attr.account(blobs, list(entries), set(loaded)).items()}

    def diff(self, *paths):
        return {p: dict(baseline=B, candidate=C) for p in paths}

    def test_the_classes(self):
        blobs = self.diff(
            "src/simp/src/A.sig", "src/1/H.sml", "src/boss/Holmakefile",
            "src/far/Holmakefile", "src/far/Z.sml",
            "src/simp/tests/performance/x.py", "src/simp/src/M.sml")
        blobs["src/same/S.sml"] = dict(baseline=B, candidate=B)
        got = self.classes(
            blobs, [entry()], loaded=["src/1/H.sml", "src/boss/b.sml",
                                      "src/simp/src/M.sml"])
        self.assertEqual(got, {
            "src/1/H.sml": "unattributed",
            "src/boss/Holmakefile": "unattributed-build",
            "src/far/Holmakefile": "unloaded",
            "src/far/Z.sml": "unloaded",
            "src/simp/src/A.sig": "attributed",
            "src/simp/src/M.sml": "unattributed",
            "src/simp/tests/performance/x.py": "excluded"})

    def test_every_differing_path_outside_src_is_accounted(self):
        blobs = self.diff(
            "tools/sequences/base-hol", "tools/Holmake/Foo.sml",
            "tools-poly/build.sml", "bin/build", "tools/README.md",
            "tools/h4pedant/x.sml", "help/Docfiles/a.smd", "CLAUDE.md",
            "Manual/Developers/x.md", "examples/e.sml",
            "src/simp/tests/compatibility/run_paired.py",
            "src/simp/tests/compatibility/paired/P.sml",
            "src/simp/tests/compatibility/inputs/x.sml",
            "src/simp/tests/native-extension/Holmakefile")
        got = self.classes(blobs)
        build = {p: "unattributed-build" for p in (
            "tools/sequences/base-hol", "tools/Holmake/Foo.sml",
            "tools-poly/build.sml", "bin/build", "tools/h4pedant/x.sml")}
        excluded = {p: "excluded" for p in (
            "help/Docfiles/a.smd", "CLAUDE.md",
            "src/simp/tests/compatibility/run_paired.py",
            "src/simp/tests/compatibility/paired/P.sml")}
        unloaded = {p: "unloaded" for p in (
            "tools/README.md", "Manual/Developers/x.md",
            "examples/e.sml", "src/simp/tests/compatibility/inputs/x.sml",
            "src/simp/tests/native-extension/Holmakefile")}
        self.assertEqual(got, {**build, **excluded, **unloaded})
        # An entry attributes a build tool; a mismatching one does not.
        row = entry("tools/sequences/base-hol", "build")
        self.assertEqual(
            self.classes(self.diff("tools/sequences/base-hol"),
                         [row])["tools/sequences/base-hol"], "attributed")
        self.assertEqual(
            self.classes(self.diff("tools/sequences/base-hol"),
                         [dict(row, candidate_blob="4" * 40)])[
                             "tools/sequences/base-hol"], "mismatch")

    def test_a_file_holmake_reads_upward_is_a_build_file(self):
        # Holmake also follows INCLUDES, PRE_INCLUDES and project
        # externals, so a file of these names is a build input wherever it
        # is: in a loaded directory, in an ancestor of one, or in a
        # directory (non-ancestor) that nothing loaded.
        loaded = ["src/boss/b.sml"]
        for name in attr.UPWARD:
            for where in ("src/boss/", "src/", "", "src/far/",
                          "src/boss/sub/", "src/boss2/", "examples/x/"):
                path = where + name
                self.assertEqual(
                    self.classes(self.diff(path), loaded=loaded),
                    {path: "unattributed-build"}, path)
        self.assertEqual(sorted(attr.UPWARD), [
            ".hol_preexec", ".holpath", "holproject.local.toml",
            "holproject.toml"])
        # Nothing loaded changes nothing.
        self.assertEqual(self.classes(self.diff("holproject.toml")),
                         {"holproject.toml": "unattributed-build"})
        # An excluded path is excluded whatever its name.
        path = "src/simp/tests/performance/.hol_preexec"
        self.assertEqual(self.classes(self.diff(path), loaded=loaded),
                         {path: "excluded"})
        path = "help/holproject.toml"
        self.assertEqual(self.classes(self.diff(path), loaded=loaded),
                         {path: "excluded"})
        # A reviewed entry attributes it; other blobs do not.
        row = entry("holproject.toml", "build")
        self.assertEqual(self.classes(self.diff("holproject.toml"), [row],
                                      loaded), {"holproject.toml":
                                                "attributed"})
        self.assertEqual(self.classes(
            self.diff("holproject.toml"), [dict(row, candidate_blob="4" * 40)],
            loaded), {"holproject.toml": "mismatch"})

    def test_a_loaded_path_is_never_excluded(self):
        path = "src/simp/tests/performance/x.sml"
        self.assertEqual(self.classes(self.diff(path), loaded=[path]),
                         {path: "unattributed"})

    def test_the_exclusions_are_reviewed_with_a_reason_each(self):
        for found, reason in attr.EXCLUDED:
            self.assertTrue(reason.strip() and len(reason) > 20, found)
            self.assertIsNotNone(attr.excluded(found.rstrip("/") + (
                "/x" if found.endswith("/") else "")))
        self.assertIsNone(attr.excluded("src/simp/src/Cond_rewr.sml"))
        self.assertIsNone(attr.excluded("tools/sequences/base-hol"))
        self.assertIsNone(attr.excluded("holproject.toml"))
        self.assertIsNone(attr.excluded("src/simp/tests/performance"))

    def test_an_entry_with_other_blobs_is_a_mismatch(self):
        got = self.classes(self.diff("src/simp/src/A.sig"),
                           [entry(new="3" * 40)])
        self.assertEqual(got, {"src/simp/src/A.sig": "mismatch"})

    def test_an_entry_for_an_unknown_or_identical_file_is_refused(self):
        with self.assertRaises(ValueError):
            attr.account({}, [entry()], set())
        with self.assertRaises(ValueError):
            attr.account({"src/simp/src/A.sig": dict(baseline=B,
                                                     candidate=B)},
                         [entry()], set())

    def test_the_decisive_classes(self):
        self.assertEqual(set(attr.DECISIVE), {
            "unattributed", "unattributed-build", "mismatch"})

    def test_build_files(self):
        for path in ("a/Holmakefile", "a/MANIFEST", "a/mktool.ML",
                     "a/data.txt"):
            self.assertTrue(attr.is_build(path), path)
        for path in ("a/B.sml", "a/B.sig", "a/README", "a/doc.md"):
            self.assertFalse(attr.is_build(path), path)


class Check(unittest.TestCase):
    def test_the_entries_name_the_blobs_git_has(self):
        path = "src/simp/src/Cond_rewr.sml"
        have = tg.git_blob(REPO, a.BASE, path)
        attr.check_blobs(REPO, a.BASE, a.BASE, [])
        with self.assertRaises(ValueError) as caught:
            attr.check_blobs(REPO, a.BASE, a.BASE, [
                entry(path, old=have, new=C)])
        self.assertIn(path, str(caught.exception))
        self.assertIn(have, str(caught.exception))


class Style(unittest.TestCase):
    def test_no_line_has_tabs_trailing_blanks_or_80_columns(self):
        for name in ("task31_attribution.py", "task31_attributed.json",
                     "test_task31_attribution.py"):
            for i, line in enumerate((a.HERE / name).read_text()
                                     .split("\n"), 1):
                self.assertNotIn("\t", line, name)
                self.assertEqual(line, line.rstrip(), (name, i))
                if not name.endswith(".json"):  # prose strings cannot wrap
                    self.assertLess(len(line), 80, (name, i))

    def test_the_cases_are_not_the_attribution(self):
        self.assertFalse(hasattr(c, "ATTRIBUTED"))


if __name__ == "__main__":
    unittest.main()
