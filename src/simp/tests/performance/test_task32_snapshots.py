#!/usr/bin/env python3
"""TASK32 snapshots (task32_snapshots.py): fake commands, real git.

A throw-away repository with a baseline and a candidate commit stands in for
HOL; a fake runner stands in for poly, smart-configure and bin/build and
leaves the products the real build would. Every guard of `verify` and
`compare` is killed by a case below."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import acceptance as a
import task32_snapshots as s

MKTOOL = s.MKTOOL_PATH
OLD = 'useB "theorystats";\n'
NEW = 'useB "theoryfiles";\nuseB "theorystats";\n'
TOOLCHAIN = {"poly_v": "Poly/ML 5.9.2 RTS version: x",
             "files": {"poly": {"path": "/p", "sha256": "1" * 64}},
             "cc": "gcc 1", "ld": "ld 1", "git": "git 1", "python3": "py"}
GIT_ENV = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True,
                          env=GIT_ENV, stdout=subprocess.PIPE,
                          text=True).stdout.strip()


def put(path, text):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def make_repo(path):
    put(path / ".gitignore", ".hol\n*.uo\n*.ui\nsigobj\nbin/hol*\n"
        "bin/Holmake\nSysteml.sml\n")
    put(path / "tools/smart-configure.sml", "(* configure *)\n")
    put(path / MKTOOL, OLD)
    put(path / "src/f.txt", "one\n")
    git(path, "init", "-q")
    git(path, "add", "-A")
    git(path, "commit", "-qm", "base")
    base = git(path, "rev-parse", "HEAD")
    put(path / MKTOOL, NEW)
    put(path / "src/f.txt", "two\n")
    git(path, "commit", "-qam", "cand")
    return base, git(path, "rev-parse", "HEAD")


class Fake:
    """A runner: real git, everything else leaves fake products."""

    def __init__(self):
        self.fail = None   # command name that exits 1
        self.drop = {}     # side -> {relative path: text} after checkout
        self.log = {}      # side -> text of every selftest log
        self.theory = {}   # side -> extra text in numTheory.sig

    def __call__(self, argv, cwd, env, stdin, log):
        side = Path(cwd).name if Path(cwd).name in s.LABELS else None
        Path(log).write_text("log %s\n" % argv[0])
        if argv[0] == "git":
            p = subprocess.run(argv, cwd=cwd, env=dict(GIT_ENV), check=False,
                               stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL)
            if argv[1] == "checkout":
                for rel, text in self.drop.get(side, {}).items():
                    put(Path(cwd) / rel, text)
            return p.returncode
        name = "configure" if argv[0] == s.POLY else "build"
        if name == self.fail:
            return 1
        root = Path(cwd)
        if name == "configure":
            put(root / s.SYSTEML, 'val HOLDIR = "%s"\n' % root)
            return 0
        for rel in s.BIN_PRODUCTS:
            put(root / rel, "binary %s %s\n" % (rel, root.name))
        objs = root / "src/num/theories/.hol/objs"
        put(objs / "numTheory.uo", "uo %s\n" % root)
        put(objs / "numTheory.dat", "dat %s\n" % root)
        put(root / "src/num/theories/numTheory.sig",
            "sig %s%s\n" % (root, self.theory.get(side, "")))
        (root / "sigobj").mkdir(exist_ok=True)
        os.symlink(objs / "numTheory.uo", root / "sigobj/numTheory.uo")
        for area in s.AREAS:
            put(root / "src" / area / ".hol/logs" / (area + "-selftest.log"),
                "\x1b[32mOK\x1b[0m %s (0.%ds)\n%s" %
                (root, len(side or ""), self.log.get(side, "")))
        return 0


class World:
    def __init__(self, test, mktool=True):
        self.dir = Path(tempfile.mkdtemp(prefix="t32-"))
        test.addCleanup(shutil.rmtree, self.dir, True)
        self.repo = self.dir / "repo"
        self.base_pin, self.cand_pin = make_repo(self.repo)
        self.root = self.dir / "snap"
        self.manifest = self.dir / "manifest.json"
        self.fake = Fake()
        self.mktool = mktool
        self.probe = lambda poly, env: copy.deepcopy(TOOLCHAIN)
        self.n = 0

    def build(self, side, **kw):
        base = side == "base"
        args = dict(mktool=base and self.mktool, cand_pin=self.cand_pin,
                    tmpdir=self.dir / "tmp", runner=self.fake,
                    probe=self.probe,
                    host=lambda: {"uname": ["Linux"], "nproc": 1})
        args.update(kw)
        return s.build_side(
            self.repo, side, self.base_pin if base else self.cand_pin,
            self.root, self.manifest, self.dir / "ev", self.dir / "scratch",
            **args)

    def both(self):
        self.build("base")
        self.build("cand")
        return self

    def doc(self):
        return json.loads(self.manifest.read_text())

    def verify(self, doc=None, **kw):
        kw.setdefault("probe", self.probe)
        return s.verify(doc if doc is not None else self.doc(), **kw)


class BuildTests(unittest.TestCase):
    def test_build_and_verify(self):
        w = World(self).both()
        doc = w.doc()
        self.assertEqual(doc["schema"], "task32-independent-build-v2")
        self.assertEqual(doc["sides"]["base"]["tree"],
                         git(w.repo, "rev-parse", w.base_pin + "^{tree}"))
        self.assertEqual(
            [c["name"] for c in doc["sides"]["cand"]["commands"]],
            ["clone", "checkout", "configure", "build"])
        build = doc["sides"]["cand"]["commands"][3]["argv"]
        self.assertEqual(build, ["bin/build", "--no-cache", "-t", "-j8",
                                 "--seq=tools/sequences/upto-parallel"])
        self.assertEqual(set(doc["sides"]["base"]["commands"][0]["env"]),
                         set(s.ENV_KEYS))
        out = w.verify(base_pin=w.base_pin, cand_pin=w.cand_pin)
        self.assertEqual(out["status"], "pass")
        # the baseline is patched, blob-equal to the candidate's mktool
        base = Path(doc["sides"]["base"]["root"])
        self.assertEqual(git(base, "hash-object", MKTOOL),
                         git(w.repo, "rev-parse", w.cand_pin + ":" + MKTOOL))

    def test_equal_length_labels_and_fresh_home(self):
        self.assertEqual(len(s.LABELS[0]), len(s.LABELS[1]))
        w = World(self)
        w.build("base")
        doc = w.doc()["sides"]["base"]
        self.assertTrue(Path(doc["home"]).name.startswith("home-"))
        with self.assertRaisesRegex(ValueError, "exists"):
            w.build("base")

    def test_dirty_or_stale_before_build(self):
        w = World(self)
        w.fake.drop["cand"] = {"src/stray.txt": "x"}
        with self.assertRaisesRegex(ValueError, "not clean"):
            w.build("cand")
        self.assertTrue(w.doc()["sides"]["cand"]["incomplete"])
        w = World(self)
        w.fake.drop["cand"] = {"old.uo": "x"}
        with self.assertRaisesRegex(ValueError, "ignored files"):
            w.build("cand")
        w = World(self)
        w.fake.drop["cand"] = {"src/x/hol.state0": "x", ".gitignore": "!x"}
        with self.assertRaisesRegex(ValueError, "not clean"):
            w.build("cand")

    def test_patch_must_equal_candidate_blob(self):
        w = World(self)
        w.build("base")
        self.assertEqual(w.doc()["sides"]["base"]["patch"]["name"], "mktool")
        w = World(self)
        with self.assertRaisesRegex(ValueError, "blob-equal"):
            w.build("base", cand_pin=w.base_pin)

    def test_failed_build_is_recorded_incomplete(self):
        w = World(self)
        w.fake.fail = "build"
        with self.assertRaisesRegex(ValueError, "build failed"):
            w.build("cand")
        doc = w.doc()
        self.assertTrue(doc["sides"]["cand"]["incomplete"])
        with self.assertRaisesRegex(ValueError, "both sides"):
            w.verify()

    def test_roots_and_scratch_not_nested(self):
        w = World(self)
        w.root = w.repo / "snap"
        with self.assertRaisesRegex(ValueError, "nested with repository"):
            w.build("cand")
        w = World(self)
        with self.assertRaisesRegex(ValueError, "inside a snapshot"):
            s.build_side(w.repo, "cand", w.cand_pin, w.root, w.manifest,
                         w.root / "cand" / "ev", w.dir / "sc",
                         runner=w.fake, probe=w.probe)
        self.assertTrue(s.nested("/a/b", "/a/b/c"))
        self.assertTrue(s.nested("/a/b", "/a/b"))
        self.assertFalse(s.nested("/a/base", "/a/cand"))

    def test_toolchain_must_match_between_sides(self):
        w = World(self)
        w.build("base")
        w.probe = lambda poly, env: dict(TOOLCHAIN, cc="gcc 2")
        with self.assertRaisesRegex(ValueError, "toolchain changed: cc"):
            w.build("cand")


class VerifyTests(unittest.TestCase):
    def setUp(self):
        self.w = World(self).both()
        self.doc = self.w.doc()
        self.base = Path(self.doc["sides"]["base"]["root"])
        self.cand = Path(self.doc["sides"]["cand"]["root"])

    def fails(self, pattern, doc=None, **kw):
        with self.assertRaisesRegex(ValueError, pattern):
            self.w.verify(doc, **kw)

    def test_passes(self):
        self.assertEqual(self.w.verify()["status"], "pass")

    def test_dirty_candidate(self):
        put(self.cand / "src/f.txt", "dirty\n")
        self.fails("dirty or patched")

    def test_staged_candidate(self):
        put(self.cand / "src/g.txt", "new\n")
        git(self.cand, "add", "src/g.txt")
        self.fails("input hash|staged")

    def test_unpatched_baseline(self):
        git(self.base, "checkout", "--", MKTOOL)
        self.fails("sealed patch|not patched")

    def test_patched_with_other_content(self):
        put(self.base / MKTOOL, NEW + "(* extra *)\n")
        self.fails("sealed patch")

    def test_baseline_patch_on_wrong_flag(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["mktool"] = True
        self.fails("only the baseline", doc)

    def test_wrong_pin(self):
        self.fails("expected", base_pin=self.w.cand_pin)
        self.fails("expected", cand_pin="0" * 40)
        self.fails("require exact", cand_pin="abc")

    def test_head_moved(self):
        git(self.cand, "checkout", "-q", "--detach", self.w.base_pin)
        self.fails("HEAD is not the pin")

    def test_wrong_tree_hash(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["tree"] = "0" * 40
        self.fails("tree hash", doc)

    def test_input_hash(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["input_hash"] = "0" * 64
        self.fails("input hash", doc)

    def test_stale_before_build_recorded(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["stale_before"] = ["x.uo"]
        self.fails("stale or ignored", doc)
        doc = self.w.doc()
        doc["sides"]["cand"]["root_existed_before"] = True
        self.fails("pre-existed", doc)

    def test_stale_mtime(self):
        path = self.cand / "src/num/theories/.hol/objs/numTheory.dat"
        os.utime(path, ns=(10**9, 10**9))
        self.fails("product changed")   # live seal differs from the record
        doc = self.w.doc()
        doc["sides"]["cand"]["products"][
            "src/num/theories/.hol/objs/numTheory.dat"]["mtime_ns"] = 10**9
        self.fails("stale product", doc)

    def test_changed_and_extra_products(self):
        put(self.cand / "bin/hol.state0", "tampered\n")
        self.fails("product changed")
        self.setUp()
        put(self.cand / "src/num/theories/.hol/objs/extra.uo", "x")
        self.fails("product set changed")

    def test_missing_product(self):
        doc = self.w.doc()
        del doc["sides"]["cand"]["products"]["bin/hol.state"]
        self.fails("product set changed", doc)
        (self.cand / "bin/hol.state").unlink()
        self.fails("missing product")

    def test_shared_inode(self):
        rel = "src/num/theories/.hol/objs/numTheory.dat"
        (self.cand / rel).unlink()
        os.link(self.base / rel, self.cand / rel)
        doc = self.w.doc()
        seal = doc["sides"]["cand"]["products"][rel]
        st = os.stat(self.base / rel)
        seal.update(ino=st.st_ino, dev=st.st_dev, mtime_ns=st.st_mtime_ns,
                    sha256=s.sha256_file(self.base / rel),
                    bytes=st.st_size)
        cand = doc["sides"]["cand"]
        cand["commands"][2]["start_ns"] = 1
        cand["build_interval_ns"][0] = 1
        cand["commands"][3]["end_ns"] = 2**62
        cand["build_interval_ns"][1] = 2**62
        self.fails("share inodes", doc)

    def test_different_argv(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["commands"][3]["argv"][3] = "-j4"
        self.fails("argv/env differ between sides: build", doc)

    def test_different_env(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["commands"][3]["env"]["TZ"] = "Europe/Rome"
        self.fails("argv/env differ between sides: build", doc)
        doc = self.w.doc()
        del doc["sides"]["cand"]["commands"][3]["env"]["TZ"]
        self.fails("env -i", doc)
        doc = self.w.doc()
        doc["sides"]["base"]["commands"][2]["stdin_hash"] = "0" * 64
        self.fails("argv/env differ between sides: configure", doc)

    def test_nested_roots(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["root"] = doc["sides"]["base"]["root"]
        self.fails("nested", doc)

    def test_unequal_length_roots(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["root"] += "x"
        self.fails("differ in length", doc)

    def test_changed_toolchain(self):
        self.w.probe = lambda p, e: dict(
            TOOLCHAIN, files={"poly": {"path": "/p", "sha256": "2" * 64}})
        self.fails("toolchain changed: files")
        self.w.probe = lambda p, e: dict(TOOLCHAIN,
                                         poly_v="Poly/ML 5.9.3 RTS version: x")
        self.fails("poly -v changed")

    def test_failed_command_and_changed_log(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["commands"][1]["exit"] = 1
        self.fails("exited 1", doc)
        Path(self.doc["sides"]["cand"]["commands"][3]["log"]).write_text("x")
        self.fails("log changed")

    def test_log_inside_root(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["commands"][0]["log"] = str(
            self.cand / "x.log")
        self.fails("log inside", doc)

    def test_parallel_builds_refused(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["commands"][2]["start_ns"] = 1
        doc["sides"]["cand"]["build_interval_ns"][0] = 1
        self.fails("stale product|not serial", doc)

    def test_systeml_changed(self):
        put(self.cand / s.SYSTEML, "different\n")
        self.fails("Systeml")

    def test_schema(self):
        doc = self.w.doc()
        doc["schema"] = "task32-independent-build-v1"
        self.fails("schema", doc)


class CompareTests(unittest.TestCase):
    def setUp(self):
        self.w = World(self).both()
        self.doc = self.w.doc()
        self.cand = Path(self.doc["sides"]["cand"]["root"])

    def run_compare(self, **kw):
        return s.compare(self.w.doc(), **kw)

    def test_identical_behaviour_passes(self):
        out = self.run_compare()
        self.assertEqual(out["status"], "pass", out["blocked"])
        self.assertEqual(out["theories"]["common"], 2)
        self.assertEqual(out["logs"]["common"], len(s.AREAS))

    def test_candidate_only_is_listed(self):
        put(self.cand / "src/simp/.hol/objs/simpMarkerTheory.dat", "x")
        put(self.cand / "src/simp/simpMarkerTheory.sig", "x")
        out = self.run_compare()
        self.assertEqual(out["status"], "pass")
        self.assertEqual(len(out["theories"]["candidate_only"]), 2)

    def test_differing_sig_blocks(self):
        put(self.cand / "src/num/theories/numTheory.sig", "changed\n")
        out = self.run_compare()
        self.assertEqual(out["status"], "blocked")
        self.assertIn("theory differs: src/num/theories/numTheory.sig",
                      out["blocked"])

    def test_differing_dat_blocks_unless_normalized(self):
        put(self.cand / "src/num/theories/.hol/objs/numTheory.dat", "z")
        self.assertEqual(self.run_compare()["status"], "blocked")
        out = self.run_compare(dat_normalizer=lambda x, y: True)
        self.assertEqual(out["status"], "pass")
        out = self.run_compare(dat_normalizer=lambda x, y: False)
        self.assertEqual(out["status"], "blocked")

    def test_missing_on_candidate_blocks(self):
        (self.cand / "src/num/theories/numTheory.sig").unlink()
        out = self.run_compare()
        self.assertIn("theory missing on cand: "
                      "src/num/theories/numTheory.sig", out["blocked"])

    def test_log_normalization_and_difference(self):
        log = self.cand / "src/real/.hol/logs/real-selftest.log"
        log.write_text(log.read_text().replace("(0.4s)", "(12.5s)"))
        self.assertEqual(self.run_compare()["status"], "pass")
        log.write_text(log.read_text() + "FAILED\n")
        out = self.run_compare()
        self.assertEqual(out["status"], "blocked")
        self.assertIn("log differs: src/real/.hol/logs/real-selftest.log",
                      out["blocked"])

    def test_missing_area_log_blocks(self):
        for p in (self.cand / "src/pred_set").rglob("*.log"):
            p.unlink()
        out = self.run_compare()
        self.assertEqual(out["status"], "blocked")
        self.assertTrue(any("src/pred_set/ on cand" in b
                            for b in out["blocked"]))

    def test_failed_build_blocks(self):
        doc = self.w.doc()
        doc["sides"]["base"]["commands"][3]["exit"] = 2
        self.assertIn("base build failed", s.compare(doc)["blocked"])

    def test_normalizers(self):
        text = "\x1b[1mok\x1b[0m /r/x (3.20s) (15ms)\n".encode()
        self.assertEqual(s.normalize_log(text, "/r"),
                         "ok $(HOLDIR)/x (<TIME>) (<TIME>)\n")


class StyleTests(unittest.TestCase):
    def test_no_tabs_or_long_lines(self):
        for name in ("task32_snapshots.py", "test_task32_snapshots.py"):
            for n, line in enumerate(Path(s.HERE / name).read_text()
                                     .splitlines(), 1):
                self.assertNotIn("\t", line, (name, n))
                self.assertEqual(line, line.rstrip(), (name, n))
                self.assertLess(len(line), 80, (name, n))


if __name__ == "__main__":
    unittest.main()
