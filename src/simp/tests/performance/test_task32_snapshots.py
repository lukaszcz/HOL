#!/usr/bin/env python3
"""TASK32 snapshots (task32_snapshots.py): fake commands, real git.

A throw-away repository with a baseline and a candidate commit stands in for
HOL; a fake runner stands in for poly, smart-configure and bin/build and
leaves the products the real build would. Every guard of `verify` and
`compare` is killed by a case below."""
import contextlib
import copy
import gzip
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time
import unittest
from unittest import mock

import acceptance as a
import startup_gate as sg
import task32_snapshots as s

MKTOOL = s.MKTOOL_PATH
OLD = 'useB "theorystats";\n'
NEW = 'useB "theoryfiles";\nuseB "theorystats";\n'
TOOLCHAIN = {"poly_v": "Poly/ML 5.9.2 RTS version: x",
             "files": {"poly": {"path": "/p", "sha256": "1" * 64}},
             "cc": "gcc 1", "ld": "ld 1", "git": "git 1", "python3": "py"}
GIT_ENV = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
DAT = "src/num/theories/.hol/objs/numTheory.dat"
SIG = "src/num/theories/numTheory.sig"
HEAP = "src/num/theories/numheap"
TRACKED_SIG = "src/real/trackedTheory.sig"


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True,
                          env=GIT_ENV, stdout=subprocess.PIPE,
                          text=True).stdout.strip()


def put(path, text):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def make_repo(path):
    """Commits A (baseline), B (candidate sources = the C31 of the tests)
    and C (B plus a test-only change). Returns A, B, C."""
    put(path / ".gitignore", ".hol\n*.uo\n*.ui\nsigobj\nbin/hol*\n"
        "bin/Holmake\nSysteml.sml\n.agent-files\n")
    put(path / "tools/smart-configure.sml", "(* configure *)\n")
    put(path / MKTOOL, OLD)
    put(path / "src/f.txt", "one\n")
    put(path / TRACKED_SIG, "a\n")
    git(path, "init", "-q")
    git(path, "add", "-A")
    git(path, "commit", "-qm", "base")
    base = git(path, "rev-parse", "HEAD")
    put(path / MKTOOL, NEW)
    put(path / "src/f.txt", "two\n")
    put(path / TRACKED_SIG, "b\n")
    git(path, "commit", "-qam", "cand sources")
    c31 = git(path, "rev-parse", "HEAD")
    put(path / "src/simp/tests/t.txt", "test only\n")
    git(path, "add", "-A")
    git(path, "commit", "-qm", "tests")
    return base, c31, git(path, "rev-parse", "HEAD")


class Fake:
    """A runner: real git, everything else leaves fake products."""

    def __init__(self):
        self.fail = None   # command name that exits 1
        self.drop = {}     # side -> {relative path: text} after checkout
        self.log = {}      # side -> text added to every selftest log
        self.during = None  # callable run inside the build step

    def __call__(self, argv, cwd, env, stdin, log):
        side = Path(cwd).name if Path(cwd).name in s.LABELS else None
        Path(log).write_text("log %s\n" % argv[0])
        if argv[0] == "git":
            p = subprocess.run(argv, cwd=cwd, env=dict(GIT_ENV), check=False,
                               stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL)
            if argv[1] == "checkout":
                for rel, text in self.drop.get(side, {}).items():
                    if rel.endswith("/"):
                        (Path(cwd) / rel).mkdir(parents=True)
                    else:
                        put(Path(cwd) / rel, text)
            return p.returncode
        name = "configure" if argv[0] == s.POLY else "build"
        if name == self.fail:
            return 1
        root = Path(cwd)
        if name == "configure":
            put(root / s.SYSTEML, 'val HOLDIR = "%s"\n' % root)
            return 0
        if self.during:
            self.during()
        for rel in s.BIN_PRODUCTS:
            put(root / rel, "binary %s %s\n" % (rel, root.name))
        for rel in (HEAP, "src/real/analysis/realheap",
                    "src/portableML/rawtheory/theorytool",
                    "src/num/arith/src/selftest.exe"):
            put(root / rel, "%s %s\n" % (rel, root.name))
        objs = root / "src/num/theories/.hol/objs"
        put(objs / "numTheory.uo", "uo %s\n" % root)
        put(objs / "numTheory.dat", "dat %s\n" % root)
        put(objs / "numTheory.sml", "sml %s\n" % root)
        put(root / SIG, "sig %s\n" % root)
        (root / "sigobj").mkdir(exist_ok=True)
        os.symlink(objs / "numTheory.uo", root / "sigobj/numTheory.uo")
        for area in s.AREAS:
            put(root / "src" / area / ".hol/logs" / (area + "-selftest.log"),
                "\x1b[32mOK\x1b[0m %s (0.%ds)\n%s" %
                (root, len(side or ""), self.log.get(side, "")))
        return 0


class World:
    def __init__(self, test, mktool=True, nested=False):
        self.dir = Path(tempfile.mkdtemp(prefix="t32-"))
        test.addCleanup(shutil.rmtree, self.dir, True)
        self.repo = self.dir / "repo"
        self.base_pin, self.c31, self.cand_pin = make_repo(self.repo)
        self.root = (self.repo / ".agent-files/snapshots/task32") \
            if nested else self.dir / "snap"
        self.manifest = self.dir / "manifest.json"
        self.fake = Fake()
        self.mktool = mktool
        self.probe = lambda poly, env: copy.deepcopy(TOOLCHAIN)

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
        kw.setdefault("base_pin", self.base_pin)
        kw.setdefault("cand_pin", self.cand_pin)
        kw.setdefault("c31", self.c31)
        return s.verify(doc if doc is not None else self.doc(), **kw)

    def argv(self, command, *more):
        return [command, "--repo", str(self.repo), "--manifest",
                str(self.manifest), "--base-pin", self.base_pin,
                "--cand-pin", self.cand_pin, "--c31", self.c31, *more]


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
        self.assertEqual(doc["sides"]["base"]["cand_pin"], w.cand_pin)
        self.assertEqual(w.verify()["status"], "pass")
        base = Path(doc["sides"]["base"]["root"])
        self.assertEqual(git(base, "hash-object", MKTOOL),
                         git(w.repo, "rev-parse", w.cand_pin + ":" + MKTOOL))
        # the product set covers heaps, tools, scripts and generated code
        products = doc["sides"]["cand"]["products"]
        for rel in (HEAP, "src/real/analysis/realheap",
                    "src/portableML/rawtheory/theorytool",
                    "src/num/arith/src/selftest.exe",
                    "src/num/theories/.hol/objs/numTheory.sml", "bin/hol",
                    "sigobj/numTheory.uo"):
            self.assertIn(rel, products)
        self.assertEqual(products["sigobj/numTheory.uo"]["kind"], "link")
        self.assertNotIn("ino", products[HEAP])

    def test_snapshot_inside_the_ignored_agent_files(self):
        w = World(self, nested=True).both()
        self.assertEqual(w.verify()["status"], "pass")

    def test_snapshot_inside_repo_elsewhere_refused(self):
        w = World(self)
        w.root = w.repo / "snap"
        with self.assertRaisesRegex(ValueError, "nested with repository"):
            w.build("cand")
        w = World(self, nested=True)
        put(w.repo / ".agent-files/snapshots/task32/base/x", "tracked")
        git(w.repo, "add", "-f", ".agent-files/snapshots/task32/base/x")
        with self.assertRaisesRegex(ValueError, "nested with repository"):
            w.build("cand")

    def test_repository_inside_the_target_refused(self):
        w = World(self)
        with self.assertRaisesRegex(ValueError, "nested with repository"):
            s.require_location(w.dir, w.repo)

    def test_equal_length_labels_and_fresh_home(self):
        self.assertEqual(len(s.LABELS[0]), len(s.LABELS[1]))
        w = World(self)
        w.build("base")
        doc = w.doc()["sides"]["base"]
        self.assertTrue(Path(doc["home"]).name.startswith("home-"))
        self.assertTrue(Path(doc["commands"][0]["log"]).name.startswith(
            "base-a0-"))
        with self.assertRaisesRegex(ValueError, "exists"):
            w.build("base")

    def test_alternates_recorded(self):
        w = World(self)
        w.build("cand")
        recorded = w.doc()["sides"]["cand"]["alternates"]
        self.assertEqual(len(recorded), 1)
        self.assertTrue(recorded[0].startswith(str(w.repo)))

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
        w.fake.drop["cand"] = {"src/x/hol.state0": "x"}
        with self.assertRaisesRegex(ValueError, "not clean"):
            w.build("cand")

    def test_empty_hol_directory_is_stale(self):
        w = World(self)
        w.fake.drop["cand"] = {"src/x/.hol/": ""}
        with self.assertRaisesRegex(ValueError,
                                    "ignored files|stale products"):
            w.build("cand")

    def test_patch_must_equal_candidate_blob(self):
        w = World(self)
        w.build("base")
        self.assertEqual(w.doc()["sides"]["base"]["patch"]["name"], "mktool")
        w = World(self)
        with self.assertRaisesRegex(ValueError, "blob-equal"):
            w.build("base", cand_pin=w.base_pin)

    def test_patch_seal_equals_apply_mktool(self):
        w = World(self)
        clone = w.dir / "clone"
        git(w.repo, "clone", "-q", "--shared", str(w.repo), str(clone))
        git(clone, "checkout", "-q", "--detach", w.base_pin)
        with mock.patch.dict(os.environ, {"GIT_DIR": "/nonexistent"}):
            with s.audit_process_environment():
                sealed = sg.apply_mktool(clone)
            self.assertNotIn("GIT_DIR", s.audit_environment())
            self.assertEqual(s.patch_seal(clone)["sha256"],
                             sealed["sha256"])
            self.assertEqual(s.patch_seal(clone)["bytes"], sealed["bytes"])
        self.assertNotIn("GIT_DIR", os.environ)
        env = s.audit_environment()
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], "/dev/null")
        self.assertEqual(env["HOME"], "/nonexistent")

    def test_failed_build_is_recorded_incomplete(self):
        w = World(self)
        w.fake.fail = "build"
        with self.assertRaisesRegex(ValueError, "build failed"):
            w.build("cand")
        self.assertTrue(w.doc()["sides"]["cand"]["incomplete"])
        with self.assertRaisesRegex(ValueError, "both sides"):
            w.verify()
        with self.assertRaisesRegex(ValueError, "target exists"):
            w.build("cand")

    def test_post_build_failure_is_incomplete(self):
        w = World(self)
        w.build("base")
        w.probe = lambda poly, env: dict(TOOLCHAIN, cc="gcc 2")
        with self.assertRaisesRegex(ValueError, "toolchain changed: cc"):
            w.build("cand")
        self.assertTrue(w.doc()["sides"]["cand"]["incomplete"])

    def test_discard_and_rebuild(self):
        w = World(self)
        w.fake.fail = "build"
        with self.assertRaises(ValueError):
            w.build("cand")
        w.fake.fail = None
        cand = Path(w.doc()["sides"]["cand"]["root"])
        home = Path(w.doc()["sides"]["cand"]["home"])
        self.assertTrue(cand.exists() and home.exists())
        s.discard_side(w.manifest, "cand")
        doc = w.doc()
        self.assertFalse(cand.exists() or home.exists())
        self.assertNotIn("cand", doc["sides"])
        self.assertEqual(doc["attempts"][0]["label"], "cand")
        w.build("base")
        w.build("cand")
        doc = w.doc()
        self.assertEqual(doc["sides"]["cand"]["attempt"], 1)
        self.assertIn("cand-a1-build", doc["sides"]["cand"]["commands"][3][
            "log"])
        self.assertNotEqual(doc["sides"]["cand"]["home"],
                            doc["attempts"][0]["home"])
        self.assertEqual(w.verify()["status"], "pass")
        with self.assertRaisesRegex(ValueError, "no such side"):
            s.discard_side(w.manifest, "nothing")

    def test_sigterm_records_incomplete_and_restores_handler(self):
        w = World(self)
        before = signal.getsignal(signal.SIGTERM)
        w.fake.during = lambda: os.kill(os.getpid(), signal.SIGTERM)
        with self.assertRaises(s.Terminated):
            w.build("cand")
        self.assertTrue(w.doc()["sides"]["cand"]["incomplete"])
        self.assertEqual(signal.getsignal(signal.SIGTERM), before)

    def test_ignored_signal_stays_ignored(self):
        before = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        self.addCleanup(signal.signal, signal.SIGHUP, before)
        with s.terminating():
            self.assertEqual(signal.getsignal(signal.SIGHUP),
                             signal.SIG_IGN)
            self.assertNotEqual(signal.getsignal(signal.SIGTERM),
                                signal.SIG_IGN)

    def test_roots_and_scratch_not_nested(self):
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

    def edit(self, side, *path, value):
        doc = self.w.doc()
        node = doc["sides"][side]
        for key in path[:-1]:
            node = node[key]
        node[path[-1]] = value
        return doc

    def test_passes(self):
        self.assertEqual(self.w.verify()["status"], "pass")

    def test_pins_are_required(self):
        with self.assertRaises(TypeError):
            s.verify(self.doc, probe=self.w.probe)
        with self.assertRaises(SystemExit):
            s.main(["verify", "--manifest", str(self.w.manifest)])

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
        self.fails("only the baseline",
                   self.edit("cand", "mktool", value=True))

    def test_mktool_blob_differing_at_verify(self):
        self.fails("blob differs", self.edit(
            "base", "patch", "candidate_blob", value="0" * 40))
        self.fails("baseline patch was made for another", self.edit(
            "base", "cand_pin", value=self.w.base_pin))

    def test_wrong_pin(self):
        self.fails("expected", base_pin=self.w.cand_pin)
        self.fails("expected", cand_pin="0" * 40)
        self.fails("require exact", cand_pin="abc")

    def test_compiled_sources_must_equal_c31(self):
        self.fails("compiled sources differ", c31=self.w.base_pin)
        self.fails("cannot compare", c31="1" * 40)
        self.assertEqual(self.w.verify(c31=self.w.c31)["status"], "pass")

    def test_head_moved(self):
        git(self.cand, "checkout", "-q", "--detach", self.w.base_pin)
        self.fails("HEAD is not the pin")

    def test_wrong_tree_hash(self):
        self.fails("tree hash", self.edit("cand", "tree", value="0" * 40))

    def test_input_hash(self):
        self.fails("input hash", self.edit("cand", "input_hash",
                                           value="0" * 64))

    def test_stale_before_build_recorded(self):
        self.fails("stale or ignored", self.edit(
            "cand", "stale_before", value=["x.uo"]))

    def test_incomplete_record(self):
        self.fails("incomplete", self.edit("cand", "incomplete", value=True))

    def test_root_not_named_by_label(self):
        doc = self.w.doc()
        other = self.cand.parent / "cxxx"
        shutil.copytree(self.cand, other, symlinks=True)
        doc["sides"]["cand"]["root"] = str(other)
        self.fails("not named by its label", doc)

    def test_stale_mtime(self):
        path = self.cand / DAT
        os.utime(path, ns=(10**9, 10**9))
        self.fails("product changed")
        self.fails("stale product", self.edit(
            "cand", "products", DAT, "mtime_ns", value=10**9))

    def test_stale_heap_replaced(self):
        old = self.cand / HEAP
        st = old.stat()
        put(old, "an old numheap\n")
        self.fails("product changed")
        os.utime(old, ns=(10**9, 10**9))
        doc = self.w.doc()
        doc["sides"]["cand"]["products"][HEAP].update(
            sha256=s.sha256_file(old), bytes=old.stat().st_size,
            mtime_ns=10**9)
        self.fails("stale product", doc)
        self.assertGreater(st.st_mtime_ns, 10**9)

    def test_changed_and_extra_products(self):
        put(self.cand / "bin/hol.state0", "tampered\n")
        self.fails("product changed")
        self.setUp()
        put(self.cand / "src/num/theories/.hol/objs/extra.uo", "x")
        self.fails("product set changed")
        self.setUp()
        put(self.cand / "src/real/realheap2", "x")
        self.fails("product set changed")

    def test_timing_driver_logs_are_not_products(self):
        put(self.cand / "src/num/.hol/logs/other.log", "x")
        put(self.cand / "src/num/.hol/build-logs/x", "x")
        self.assertEqual(self.w.verify()["status"], "pass")
        put(self.cand / "src/num/.hol/logs/num-selftest.log", "changed")
        self.fails("product changed")

    def test_missing_product(self):
        doc = self.w.doc()
        del doc["sides"]["cand"]["products"]["bin/hol.state"]
        self.fails("product set changed", doc)
        (self.cand / "bin/hol.state").unlink()
        self.fails("missing product")

    def test_no_sigobj_products(self):
        doc = self.w.doc()
        for rel in list(doc["sides"]["cand"]["products"]):
            if rel.startswith("sigobj/"):
                del doc["sides"]["cand"]["products"][rel]
        shutil.rmtree(self.cand / "sigobj")
        self.fails("no sigobj", doc)

    def widen(self, doc, side):
        record = doc["sides"][side]
        record["commands"][2]["start_ns"] = 1
        record["build_interval_ns"][0] = 1
        record["commands"][3]["end_ns"] = 2**62
        record["build_interval_ns"][1] = 2**62

    def test_shared_inode(self):
        (self.cand / DAT).unlink()
        os.link(self.base / DAT, self.cand / DAT)
        doc = self.w.doc()
        doc["sides"]["cand"]["products"][DAT] = copy.deepcopy(
            doc["sides"]["base"]["products"][DAT])
        self.widen(doc, "cand")
        self.fails("share inodes", doc)

    def test_hard_links_within_one_side(self):
        os.link(self.cand / HEAP, self.cand / (HEAP + "2"))
        doc = self.w.doc()
        doc["sides"]["cand"]["products"][HEAP + "2"] = copy.deepcopy(
            doc["sides"]["cand"]["products"][HEAP])
        self.fails("links a product twice", doc)

    def test_different_argv(self):
        self.fails("argv/env differ between sides: build", self.edit(
            "cand", "commands", 3, "argv", value=["bin/build", "-j4"]))

    def test_different_env(self):
        self.fails("argv/env differ between sides: build", self.edit(
            "cand", "commands", 3, "env", "TZ", value="Europe/Rome"))
        doc = self.w.doc()
        del doc["sides"]["cand"]["commands"][3]["env"]["TZ"]
        self.fails("env -i", doc)
        self.fails("argv/env differ between sides: configure", self.edit(
            "base", "commands", 2, "stdin_hash", value="0" * 64))

    def test_nested_roots(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["root"] = doc["sides"]["base"]["root"]
        self.fails("nested", doc)

    def test_unequal_length_roots(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["root"] += "x"
        self.fails("differ in length", doc)

    def test_home_inside_root_and_shared(self):
        self.fails("HOME inside", self.edit(
            "cand", "home", value=str(self.cand / "home")))
        self.fails("shared HOME", self.edit(
            "cand", "home", value=self.doc["sides"]["base"]["home"]))

    def test_changed_toolchain(self):
        self.w.probe = lambda p, e: dict(
            TOOLCHAIN, files={"poly": {"path": "/p", "sha256": "2" * 64}})
        self.fails("toolchain changed: files")
        self.w.probe = lambda p, e: dict(
            TOOLCHAIN, poly_v="Poly/ML 5.9.3 RTS version: x")
        self.fails("poly -v changed")

    def test_failed_command(self):
        self.fails("exited 1", self.edit("cand", "commands", 1, "exit",
                                         value=1))

    def test_logs_changed_missing_or_compressed(self):
        log = Path(self.doc["sides"]["cand"]["commands"][3]["log"])
        data = log.read_bytes()
        log.write_bytes(gzip.compress(data))
        shutil.move(log, str(log) + ".gz")
        self.assertEqual(self.w.verify()["status"], "pass")
        Path(str(log) + ".gz").write_bytes(gzip.compress(b"other"))
        self.fails("log changed")
        Path(str(log) + ".gz").unlink()
        self.fails("log missing")
        log.write_text("x")
        self.fails("log changed")

    def test_log_inside_root(self):
        self.fails("log inside", self.edit(
            "cand", "commands", 0, "log", value=str(self.cand / "x.log")))

    def test_alternates_gone_or_changed(self):
        self.fails("alternates", self.edit(
            "cand", "alternates", value=["/nonexistent/objects"]))

    def test_parallel_builds_refused(self):
        doc = self.w.doc()
        doc["sides"]["cand"]["commands"][2]["start_ns"] = 1
        doc["sides"]["cand"]["build_interval_ns"][0] = 1
        self.fails("stale product|not serial", doc)

    def test_systeml_changed_and_different_between_sides(self):
        put(self.cand / s.SYSTEML, "different\n")
        self.fails("Systeml")
        self.setUp()
        put(self.cand / s.SYSTEML, "different\n")
        doc = self.w.doc()
        record = doc["sides"]["cand"]
        record["systeml"] = s.systeml_hashes(self.cand)
        record["products"][s.SYSTEML] = s.seal_product(self.cand, s.SYSTEML)
        self.widen(doc, "cand")
        self.fails("Systeml.sml differs between sides", doc)

    def test_schema(self):
        doc = self.w.doc()
        doc["schema"] = "task32-independent-build-v1"
        self.fails("schema", doc)


class DatTool:
    """A fake dat-printer: the file without its `id` lines."""
    SCRIPT = "#!/bin/sh\ngrep -v '^id' \"$1\"\n"


class CompareTests(unittest.TestCase):
    def setUp(self):
        self.w = World(self).both()
        self.doc = self.w.doc()
        self.cand = Path(self.doc["sides"]["cand"]["root"])
        self.base = Path(self.doc["sides"]["base"]["root"])

    def run_compare(self, **kw):
        return s.compare(self.w.doc(), **kw)

    def install_tool(self, script=DatTool.SCRIPT, sides=s.LABELS):
        for label in sides:
            tool = Path(self.doc["sides"][label]["root"]) / s.DAT_PRINTER
            put(tool, script)
            tool.chmod(0o755)

    def test_identical_behaviour_passes(self):
        out = self.run_compare()
        self.assertEqual(out["status"], "pass", out["blocked"])
        self.assertEqual(out["theories"]["common"], 2)
        self.assertEqual(out["logs"]["common"], len(s.AREAS))
        self.assertEqual(out["normalization"]["logs"][1][0], "gc-tag")
        self.assertIsNone(out["dat_normalizer"])

    def test_tracked_theory_sources_are_not_compared(self):
        # TRACKED_SIG differs between the commits and is not a product
        out = self.run_compare()
        self.assertNotIn(TRACKED_SIG, out["theories"]["differing"])
        self.assertEqual(out["theories"]["common"], 2)

    def test_candidate_only_is_listed(self):
        put(self.cand / "src/simp/.hol/objs/simpMarkerTheory.dat", "x")
        put(self.cand / "src/simp/simpMarkerTheory.sig", "x")
        out = self.run_compare()
        self.assertEqual(out["status"], "pass")
        self.assertEqual(len(out["theories"]["candidate_only"]), 2)

    def test_differing_sig_blocks(self):
        put(self.cand / SIG, "changed\n")
        out = self.run_compare()
        self.assertEqual(out["status"], "blocked")
        self.assertIn("theory differs: " + SIG, out["blocked"])

    def test_realpath_spelling_is_masked_in_sig_and_dat(self):
        link = self.base.parent / "alias"
        os.symlink(self.base, link)
        put(self.base / SIG, "sig %s\n" % link)
        put(self.cand / SIG, "sig %s\n" % self.cand)
        put(self.base / DAT, "dat %s\n" % self.base)
        out = self.run_compare()
        # the alias is not the root spelling, so it still differs
        self.assertEqual(out["status"], "blocked")
        put(self.base / SIG, "sig %s\n" % os.path.realpath(self.base))
        self.assertEqual(self.run_compare()["status"], "pass")

    def test_differing_dat_blocks_without_the_flag(self):
        put(self.cand / DAT, "z")
        self.assertEqual(self.run_compare()["status"], "blocked")

    def test_dat_printer_explains_a_dat_difference(self):
        self.install_tool()
        put(self.base / DAT, "id 1\nthm %s\n" % self.base)
        put(self.cand / DAT, "id 2\nthm %s\n" % self.cand)
        printer = s.DatPrinter()
        out = self.run_compare(dat_normalizer=printer)
        self.assertEqual(out["status"], "pass", out["blocked"])
        self.assertEqual(out["dat_dumps"][0]["equal"], True)
        ident = out["dat_normalizer"]
        self.assertEqual(len(ident["source_sha256"]), 64)
        self.assertEqual(ident["cls"], "DatPrinter")
        self.assertEqual(len(ident["runs"]), 2)
        run = ident["runs"][0]
        self.assertEqual(run["argv"][1], DAT)
        self.assertEqual(len(run["tool"]["sha256"]), 64)
        json.dumps(out)

    def test_dat_printer_with_real_difference_blocks(self):
        self.install_tool()
        put(self.base / DAT, "thm a\n")
        put(self.cand / DAT, "thm b\n")
        out = self.run_compare(dat_normalizer=s.DatPrinter())
        self.assertEqual(out["status"], "blocked")
        self.assertFalse(out["dat_dumps"][0]["equal"])

    def test_dat_printer_missing_or_failing_is_an_error(self):
        put(self.cand / DAT, "z")
        with self.assertRaisesRegex(ValueError, "no dat-printer"):
            self.run_compare(dat_normalizer=s.DatPrinter())
        self.install_tool("#!/bin/sh\nexit 3\n")
        with self.assertRaisesRegex(ValueError, "failed"):
            self.run_compare(dat_normalizer=s.DatPrinter())

    def test_bool_only_hook_is_refused(self):
        put(self.cand / DAT, "z")
        with self.assertRaisesRegex(ValueError, "needs dump"):
            self.run_compare(dat_normalizer=lambda x, y: True)

    def test_missing_on_candidate_blocks(self):
        (self.cand / SIG).unlink()
        out = self.run_compare()
        self.assertIn("theory missing on cand: " + SIG, out["blocked"])

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

    def test_normalizers_on_real_log_lines(self):
        lines = [
            ("\x1b[1mok\x1b[0m /r/x (3.20s) (15ms)\n",
             "ok $(HOLDIR)/x (<TIME>) (<TIME>)\n"),
            ("simp: LOG 5 10653 (= 5) ...      \x1b[1;31m[GC = 0.002] "
             "\x1b[0m(0.002s)      OK\n",
             "simp: LOG 5 10653 (= 5) ...      (<TIME>)      OK\n"),
            ("Theory \"bit\" took 1.4s to build\n"
             "Theory \"numpair\" took 0.40605s to build\n",
             "Theory \"bit\" took <TIME> to build\n"
             "Theory \"numpair\" took <TIME> to build\n"),
            ("runtime: 0.00040s,    gctime: 0.00000s,     "
             "systime: 0.00003s.\n",
             "runtime: <TIME>,    gctime: <TIME>,     systime: <TIME>.\n"),
            ("     HOL4 [Trindemossen 2 (stdknl, built Thu Oct 22 "
             "07:02:54 2026)]\n",
             "     HOL4 [Trindemossen 2 (stdknl, built <DATE>)]\n"),
            ("Writing heap: /r/src/num/termination/numheap\n",
             "Writing heap: $(HOLDIR)/src/num/termination/numheap\n"),
            ("Prims: 597449; Total: 597474\n",
             "Prims: 597449; Total: 597474\n")]
        for text, want in lines:
            self.assertEqual(s.normalize_log(text.encode(), "/r"), want)


class MainTests(unittest.TestCase):
    def setUp(self):
        self.w = World(self).both()
        self.out = self.w.dir / "behavior.json"

    def run_main(self, *args):
        stream = io.StringIO()
        with mock.patch.object(s, "probe_toolchain", self.w.probe), \
                contextlib.redirect_stdout(stream):
            return s.main(list(args)), stream.getvalue()

    def test_verify_then_compare(self):
        code, text = self.run_main(*self.w.argv("verify"))
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(text)["status"], "pass")
        code, text = self.run_main(*self.w.argv(
            "compare", "--output", str(self.out)))
        self.assertEqual((code, json.loads(self.out.read_text())["status"]),
                         (0, "pass"))
        with self.assertRaises(FileExistsError):
            self.run_main(*self.w.argv("compare", "--output",
                                       str(self.out)))

    def test_compare_exit_code_when_blocked(self):
        cand = Path(self.w.doc()["sides"]["cand"]["root"])
        put(cand / SIG, "changed\n")
        # a product changed: verify blocks before any comparison
        with self.assertRaisesRegex(ValueError, "product changed"):
            self.run_main(*self.w.argv("compare", "--output",
                                       str(self.out)))
        self.assertFalse(self.out.exists())

    def test_blocked_comparison_exits_1(self):
        with mock.patch.object(s, "compare", return_value={
                "status": "blocked"}):
            code, _ = self.run_main(*self.w.argv(
                "compare", "--output", str(self.out)))
        self.assertEqual(code, 1)

    def test_discard_through_main(self):
        code, _ = self.run_main("discard", "--repo", str(self.w.repo),
                                "--manifest", str(self.w.manifest),
                                "--side", "cand")
        self.assertEqual(code, 0)
        self.assertNotIn("cand", self.w.doc()["sides"])


class ToolchainTests(unittest.TestCase):
    POLYC = ('#! /bin/sh\nprefix="/usr/local"\nexec_prefix="${prefix}"\n'
             'BINDIR="${exec_prefix}/bin"\nLINK="g++"\n'
             'LIBDIR="${exec_prefix}/lib"\nLIBS=""\n')
    LDD = ("\tlinux-vdso.so.1 (0x0000ffff9b3f0000)\n"
           "\tlibpolyml.so.16 => /usr/local/lib/libpolyml.so.16 "
           "(0x0000ffff9a000000)\n"
           "\tlibc.so.6 => /lib/aarch64-linux-gnu/libc.so.6 (0x1)\n"
           "\t/lib/ld-linux-aarch64.so.1 (0x0000ffff9b3f3000)\n")

    def test_polyc_libdir_is_expanded(self):
        self.assertEqual(s.parse_polyc_libdir(self.POLYC), "/usr/local/lib")
        self.assertIsNone(s.parse_polyc_libdir('LIBDIR="${nothing}/lib"\n'))

    def test_libpolymain_lookup(self):
        with tempfile.TemporaryDirectory() as tmp:
            put(Path(tmp) / "bin/polyc",
                self.POLYC.replace("/usr/local", tmp))
            put(Path(tmp) / "lib/libpolymain.a", "a")
            found = s._libpolymain(Path(tmp) / "bin/polyc")
            self.assertEqual(found, str(Path(tmp, "lib/libpolymain.a")
                                        .resolve()))
            (Path(tmp) / "lib/libpolymain.a").unlink()
            self.assertIsNone(s._libpolymain(Path(tmp) / "bin/polyc"))

    def test_ldd_parsing(self):
        with mock.patch("os.path.realpath", side_effect=lambda p: p):
            found = s.parse_ldd(self.LDD)
        self.assertEqual(set(found), {"libpolyml.so.16", "libc.so.6",
                                      "ld-linux-aarch64.so.1"})
        with self.assertRaisesRegex(ValueError, "unresolved"):
            s.parse_ldd("\tlibx.so => not found\n")

    def test_probe_toolchain_hashes_every_library(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            put(tmp / "bin/poly", "#!/bin/sh\necho Poly/ML 5.9.2\n")
            (tmp / "bin/poly").chmod(0o755)
            put(tmp / "bin/polyc", self.POLYC.replace("/usr/local", str(tmp)))
            put(tmp / "lib/libpolymain.a", "m")
            put(tmp / "lib/libpolyml.so.1", "l")
            ldd = "libpolyml.so.1 => %s (0x1)\n" % (tmp / "lib/libpolyml.so.1")
            real = subprocess.run

            def fake(argv, **kw):
                if argv[0] == "ldd":
                    return subprocess.CompletedProcess(argv, 0, ldd, "")
                return real(argv, **kw)

            with mock.patch.object(subprocess, "run", fake):
                record = s.probe_toolchain(str(tmp / "bin/poly"),
                                           s.environment("/nonexistent"))
        self.assertEqual(record["poly_v"], "Poly/ML 5.9.2")
        self.assertIn("lib:libpolyml.so.1", record["files"])
        self.assertIsNotNone(record["files"]["libpolymain.a"])


class RunCommandTests(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="t32-run-"))
        self.addCleanup(shutil.rmtree, self.dir, True)

    def test_stdin_is_dev_null_and_env_exact(self):
        log = self.dir / "log"
        code = s.run_command(["sh", "-c", "cat | wc -c; env | sort"],
                             self.dir, {"A": "1"}, None, log)
        self.assertEqual(code, 0)
        lines = log.read_text().split()
        self.assertEqual(lines[0], "0")
        self.assertIn("A=1", lines)
        self.assertFalse([l for l in lines if l.startswith("HOME=")])

    def test_stdin_file(self):
        src = self.dir / "in"
        src.write_text("hello")
        log = self.dir / "log"
        s.run_command(["cat"], self.dir, {}, src, log)
        self.assertEqual(log.read_text(), "hello")

    def test_timeout_kills_the_process_group(self):
        pidfile = self.dir / "pid"
        with mock.patch.object(s, "TIMEOUT", 1):
            with self.assertRaises(subprocess.TimeoutExpired):
                s.run_command(["sh", "-c", "echo $$ > pid; sleep 30"],
                              self.dir, {"PATH": s.PATH}, None,
                              self.dir / "log")
        pid = int(pidfile.read_text())
        for _ in range(50):
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                break
            time.sleep(0.1)
        else:
            self.fail("process still alive")


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
