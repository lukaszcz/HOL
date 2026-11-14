#!/usr/bin/env python3
"""TASK32 snapshots (task32_snapshots.py): fake commands, real git.

A throw-away repository with a baseline and a candidate commit stands in for
HOL; a fake runner stands in for poly, smart-configure and bin/build and
leaves the products the real build would. Every guard of `verify` and
`compare` is killed by a case below."""
import contextlib
import copy
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import posixpath
import re
import shutil
import signal
import subprocess
import tempfile
import time
import unittest
from unittest import mock

import acceptance as a
import startup_gate as sg
import task32_dat as dat
import task32_cases as cases
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
    put(path / "src/boss/tests/x/t.txt", "test only\n")
    git(path, "add", "-A")
    git(path, "commit", "-qm", "tests")
    return base, c31, git(path, "rev-parse", "HEAD")


REAL_DAT = (
    '(theory\n'
    ' ("basicSize" ("numeral" . "c5b9378dfb99f058873ae63010b3a2c3'
    '8e1f584f")\n'
    '  ("pairToolsContext" . "286b920811c2ee1cb3ccb47011db0831426'
    '63494")\n'
    '  ("option" . "7d325eb28d258de6d3f1ce44c4dbe34a127234b9"))\n'
    ' (core-data\n'
    '  (tables\n'
    '   (string-table "min" "bool" "fun" "num" "sum" "itself" "on'
    'e" "!"\n'
    '    "arithmetic" "+" "pair" "," "prod" "/\\\\" "0" "=" "BIT1" '
    '"INL" "INR"\n'
    '    "option" "NONE" "NUMERAL" "SOME" "ZERO" "basicSize" "boo'
    'l_size"\n'
    '    "full_sum_size" "itself_size" "min_pair_size" "one_size"'
    ' "option_size"\n'
    '    "pair_size" "sum_size" "sum_size_def" "pair_size_def" "o'
    'ption_size_def"\n'
    '    "one_size_def" "min_pair_size_def" "itself_size_def"\n'
    '    "full_sum_size_thm" "full_sum_size_def" "bool_size_def" '
    '"" "$(HOLDIR)"\n'
    '    "src" "theories" "basicSizeScript.sml")\n'
    '   (id-table (0 . 1) (0 . 2) (3 . 3) (4 . 4) (1 . 5) (6 . 6)'
    ' (1 . 7)\n'
    '    (8 . 9) (10 . 11) (10 . 12) (1 . 13) (3 . 14) (0 . 15) ('
    '8 . 16)\n'
    '    (4 . 17) (4 . 18) (19 . 20) (19 . 19) (8 . 21) (19 . 22)'
    ' (8 . 23)\n'
    '    (24 . 25) (24 . 26) (24 . 27) (24 . 28) (24 . 29) (24 . '
    '30) (24 . 31)\n'
    '    (24 . 32))\n'
    '   (type-table (0) (2) "\'a" (1 2 1) "\'b" (1 4 1) (3 2 4) (4 '
    '2) (5) (1 2 0)\n'
    '    (1 9 0) (1 4 0) (1 11 0) (1 0 0) (1 13 0) (1 3 0) (1 15 '
    '0) (1 5 0)\n'
    '    (1 17 0) (1 7 0) (1 19 0) (1 8 0) (1 21 0) (1 6 0) (1 23'
    ' 0) (1 1 1)\n'
    '    (1 1 25) (9 2 4) (1 4 27) (1 2 28) (1 0 13) (1 1 0) (1 1'
    ' 31) (1 2 6)\n'
    '    (1 4 6) (17 2) (1 2 35) (1 0 1) (1 6 1) (1 5 38) (1 3 39'
    ') (1 7 1)\n'
    '    (1 27 1) (1 5 42) (1 3 43) (1 8 1) (1 35 1) (1 3 46))\n'
    '   (term-table ("b" 0) ("f" 3) ("g" 5) ("sum" 6) ("x" 2) ("x'
    '" 7) ("x" 8)\n'
    '    ("y" 4) (6 10) (6 12) (6 14) (6 16) (6 18) (6 20) (6 22)'
    ' (6 24) (7 26)\n'
    '    (8 29) (10 30) (11 1) (12 32) (13 25) (14 33) (15 34) (1'
    '6 35) (18 25)\n'
    '    (19 36) (20 1) (21 37) (22 40) (23 41) (24 44) (25 45) ('
    '26 47) (27 44)\n'
    '    (28 40))) exports (nil) (nil)\n'
    '  ((33 (((24 5) (4 11)) "DISK_THM") (1 0)\n'
    '    ("%1%2%4$2$1B35$0U22@$0u2B20|U8|U12|U11%1%2%7$2$1B35$0U2'
    '3@$0u1B20|U9|U12|U11B18"))\n'
    '   (34 (((24 2) (10 22)) "DISK_THM") (1 0)\n'
    '    ("%1%2%4%7$3$2B34$1$0B17@%27U21U25$1u3$0u2B16B16B20|U9|U'
    '8|U12|U11"))\n'
    '   (35 (((24 8) (19 4)) "DISK_THM") (1 0)\n'
    '    ("%1$0%24B33%19B20|U11%1%4$1$0U26B33%27U21U25$0u1B16B20|'
    'U8|U11B18"))\n'
    '   (36 (((24 3))) (1 0) ("%6$0U32%19B20|U14"))\n'
    '   (37 (((24 1) (10 22)) "DISK_THM") (1 0)\n'
    '    ("%1%2%4%7$3$2B31$1$0B17@$1u3$0u2B16B20|U9|U8|U12|U11"))'
    '\n'
    '   (38 (((24 4))) (1 0) ("%5$0U30%19B20|U13"))\n'
    '   (39 (((24 7) (24 5 6) (1 25 50 56)) "DISK_THM")\n'
    '    (2 0 1 31 42 43 44 3 45 46)\n'
    '    ("%1%2B29%4U22@%27U21U25%4U1B16B20%1%2B29%7U23@%27U21U25'
    '%7U2B16B20B18"))\n'
    '   (40 (((24 6))) (1 0)\n'
    '    ("%1%2%3$2$1B29$0@%27U21U25$2$1B35$0@B16B20|U15|U12|U11"'
    '))\n'
    '   (41 (((24 0))) (1 0) ("%0$0U28%19B20|U10"))))\n'
    ' (incorporate (incorporate-types) incorporate-consts ("sum_s'
    'ize" . 40)\n'
    '  ("pair_size" . 44) ("option_size" . 47) ("one_size" . 45)\n'
    '  ("min_pair_size" . 44) ("itself_size" . 41) ("full_sum_siz'
    'e" . 40)\n'
    '  ("bool_size" . 37))\n'
    ' (loadable-thydata\n'
    '  ("userdef.deltas" (tag-knm 24 . 41) (tag-knm 24 . 37) (tag'
    '-knm 24 . 34)\n'
    '   (tag-knm 24 . 36) (tag-knm 24 . 38) (tag-knm 24 . 33) (ta'
    'g-knm 24 . 40)\n'
    '   (tag-knm 24 . 35))\n'
    '  ("grammardelta" (OO "bool_size" (tag-tm . "%28"))\n'
    '   (OO "min_pair_size" (tag-tm . "%31")) (OO "pair_size" (ta'
    'g-tm . "%34"))\n'
    '   (OO "one_size" (tag-tm . "%32")) (OO "itself_size" (tag-t'
    'm . "%30"))\n'
    '   (OO "sum_size" (tag-tm . "%35")) (OO "full_sum_size" (tag'
    '-tm . "%29"))\n'
    '   (OO "option_size" (tag-tm . "%33")))))\n'
)


def sexp_str(text):
    return '"%s"' % text


def mk_dat(name, parents=(), strings=None, types=None, terms=None,
           hyps=(), tags=("DISK_THM",), newsig_arity=1, deltas=None,
           extra=None, xname="x"):
    """A theory in the real .dat format with one theorem. `strings`,
    `types` and `terms` are orders of the sharing tables' entries."""
    strings = strings or ["min", "bool", "c", name, "x"]
    types = types or ["alpha", "bool"]
    terms = terms or ["x", "c", "ap"]
    sidx = {v: i for i, v in enumerate(strings)}
    ids = [("min", "bool"), (name, "c")]
    idx_id = {v: i for i, v in enumerate(ids)}
    tkey = {"alpha": "\"'a\"", "bool": "(%d)" % idx_id[ids[0]]}
    tyidx = {v: i for i, v in enumerate(types)}
    # a type entry's text may not mention a later type
    tytext = ["%s" % tkey[v] for v in types]
    tmtext = {"x": '("%s" %d)' % (xname, tyidx["bool"]),
              "c": "(%d %d)" % (idx_id[ids[1]], tyidx["bool"])}
    tmidx = {v: i for i, v in enumerate(terms)}
    tmtext["ap"] = "(ap %d %d)" % (tmidx["x"], tmidx["c"])
    enc = lambda key: "%%%d" % tmidx[key]
    deltas = sidx["c"] if deltas is None else deltas
    extra_text = "" if extra is None else " " + (
        extra(sidx, tmidx) if callable(extra) else extra)
    thm = '(%d (((%d 0)) %s) (2 0) (%s))' % (
        sidx["c"], sidx[name], " ".join(sexp_str(t) for t in tags),
        " ".join(sexp_str(t) for t in [enc("c")] + [enc(h) for h in hyps]))
    plist = "".join(' ("%s" . "%s")' % p for p in parents)
    return (
        '(theory\n ("%s"%s)\n (core-data (tables (string-table %s)\n'
        '  (id-table %s)\n  (type-table %s)\n  (term-table %s))\n'
        '  exports (nil) (nil) (%s))\n'
        ' (incorporate (incorporate-types ("T" . %d)) incorporate-consts '
        '("c" . %d))\n (loadable-thydata ("userdef.deltas" '
        '(tag-knm %d . %d)) ("grammardelta" (OO c (tag-tm . "%s")))%s))\n'
        % (name, plist, " ".join(sexp_str(x) for x in strings),
           " ".join("(%d . %d)" % (sidx[a], sidx[b]) for a, b in ids),
           " ".join(tytext), " ".join(tmtext[t] for t in terms), thm,
           newsig_arity, tyidx["bool"], sidx[name], deltas, enc("c"),
           extra_text))


class Fake:
    """A runner: real git, everything else leaves fake products."""

    def __init__(self):
        self.fail = None   # command name that exits 1
        self.drop = {}     # side -> {relative path: text} after checkout
        self.log = {}      # side -> text added to every selftest log
        self.during = None  # callable run inside the build step
        self.prime = None  # callable (cwd, side, again) run in a prime command

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
        if os.path.basename(argv[0]) == "Holmake":
            again = "-reprime-" in Path(log).name
            if self.fail == ("reprime" if again else "prime"):
                return 1
            if self.prime:
                self.prime(Path(cwd), side, again)
            return 0
        name = "configure" if os.path.basename(argv[0]) == "poly" \
            else "build"
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
        put(objs / "numTheory.cachekey", "key\n")
        put(root / "src/num/theories/.hol/docs/numTheory.html", "html\n")
        put(root / "src/num/theories/.hol/make-deps/numTheory.sml.d", "d\n")
        put(root / "src/num/theories/.hol/locks/numTheory.uo.lock",
            "%d\n" % os.getpid())
        put(root / SIG, "sig %s\n" % root)
        (root / "sigobj").mkdir(exist_ok=True)
        os.symlink(objs / "numTheory.uo", root / "sigobj/numTheory.uo")
        for area in s.AREAS:
            put(root / "src" / area / ".hol/logs" / (area + "-selftest.log"),
                "\x1b[32mOK\x1b[0m %s (0.%ds)\n%s" %
                (root, len(side or ""), self.log.get(side, "")))
        for kind, directory, name in s.REQUIRED_PRODUCTS:
            folder = root / directory
            if kind == "theory":
                put(folder / (".hol/objs/%sTheory.dat" % name), "dat\n")
            elif kind == "file":
                put(folder / name, "%s %s\n" % (name, root.name))
            else:
                put(folder / ".hol/logs" / name,
                    "\x1b[32mOK\x1b[0m %s (0.%ds)\n" %
                    (root, len(side or "")))
        return 0


def write_cache_once(cwd, side, again):
    """A prime command that writes a cache the first time only: a fixed
    point."""
    path = cwd / ".hol/make-deps/listTheory.sig.d"
    if str(cwd).endswith("src/list/src") and not path.exists():
        put(path, "d\n")


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
        self.harness = self.dir / "harness"
        put(self.harness / s.SEQUENCE_REL, Path(s.SEQUENCE).read_text())
        git(self.harness, "init", "-q")
        git(self.harness, "add", "-A")
        git(self.harness, "commit", "-qm", "seq")
        self.mktool = mktool
        self.probe = lambda poly, env: copy.deepcopy(TOOLCHAIN)

    def build(self, side, **kw):
        base = side == "base"
        args = dict(mktool=base and self.mktool, cand_pin=self.cand_pin,
                    tmpdir=self.dir / "tmp", runner=self.fake,
                    harness=(self.harness, s.SEQUENCE_REL),
                    probe=self.probe,
                    host=lambda: {"uname": ["Linux"], "nproc": 1})
        paths = dict(root=self.root, manifest=self.manifest,
                     logs=self.dir / "ev", scratch=self.dir / "scratch")
        for key in paths:
            paths[key] = kw.pop(key, paths[key])
        args.update(kw)
        return s.build_side(
            self.repo, side, self.base_pin if base else self.cand_pin,
            paths["root"], paths["manifest"], paths["logs"],
            paths["scratch"], **args)

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
    def test_every_theory_unit_is_primed_with_its_downstream_command(self):
        w = World(self).both()
        record = w.doc()["sides"]["cand"]
        units = cases.THEORY_UNITS
        for c, unit, name in zip(record["commands"][4:], 2 * units, [
                "prime-" + u["name"] for u in units] + [
                "reprime-" + u["name"] for u in units]):
            self.assertEqual(c["name"], name)
            self.assertEqual(c["argv"], cases.theory_argv(
                record["root"], unit["theory"]))
            self.assertIn("--no_prereqs", c["argv"])
            self.assertEqual(c["cwd"], str(Path(record["root"]) /
                                           unit["dir"]))
        self.assertEqual(record["build_interval_ns"][1],
                         record["commands"][-1]["end_ns"])
        self.assertEqual(record["primed"], [])

    def test_primed_caches_are_recorded_as_products(self):
        w = World(self)
        cache = "src/list/src/.hol/make-deps/listTheory.sig.d"
        w.fake.prime = write_cache_once
        w.both()
        doc = w.doc()
        self.assertEqual(doc["sides"]["cand"]["primed"],
                         sorted(r for r in doc["sides"]["cand"]["products"]
                                if r.endswith("listTheory.sig.d")))
        self.assertIn(cache, doc["sides"]["cand"]["products"])
        w.verify()

    def test_a_prime_that_changes_a_product_fails_the_build(self):
        w = World(self)
        w.fake.prime = lambda cwd, side, again: put(
            cwd / ".hol/objs/numTheory.uo", "changed\n") \
            if cwd.name == "theories" else None
        with self.assertRaisesRegex(ValueError, "prime commands changed"):
            w.build("base")
        self.assertTrue(w.doc()["sides"]["base"]["incomplete"])

    def test_a_prime_that_writes_another_file_fails_the_build(self):
        w = World(self)
        w.fake.prime = lambda cwd, side, again: put(
            cwd / "stray.txt", "x\n")
        with self.assertRaisesRegex(ValueError, "prime commands changed"):
            w.build("base")

    def test_a_second_pass_that_writes_again_is_not_a_fixed_point(self):
        w = World(self)
        count = []

        def hook(cwd, side, again):
            if str(cwd).endswith("src/list/src"):
                count.append(1)
                put(cwd / (".hol/make-deps/L%dTheory.sig.d" % len(count)),
                    "d\n")
        w.fake.prime = hook
        with self.assertRaisesRegex(ValueError, "not a fixed point"):
            w.build("base")

    def test_a_failing_reprime_fails_the_build(self):
        w = World(self)
        w.fake.fail = "reprime"
        with self.assertRaisesRegex(ValueError, "reprime-arithmetic failed"):
            w.build("base")

    def tampered(self, change, pattern, primed=True):
        w = World(self)
        w.fake.prime = write_cache_once if primed else None
        w.both()
        doc = w.doc()
        change(doc["sides"]["cand"])
        with self.assertRaisesRegex(ValueError, pattern):
            w.verify(doc)

    def test_verify_checks_the_primed_list(self):
        key = "src/list/src/.hol/make-deps/listTheory.sig.d"
        self.tampered(lambda r: r["primed"].append(key),
                      "bad list of primed")
        self.tampered(lambda r: r["primed"].append("nowhere.d"),
                      "bad list of primed")
        self.tampered(lambda r: r.update(primed=[key, "src/f.txt"]),
                      "bad list of primed")
        self.tampered(lambda r: r.update(primed=["bin/hol"]),
                      "bad list of primed")

    def test_verify_checks_when_products_were_written(self):
        def early(record):
            record["commands"][3]["end_ns"] = record["commands"][3][
                "start_ns"]
        self.tampered(early, "written after the build")

        def kind(record):
            record["primed"] = ["sigobj/numTheory.uo"]
        self.tampered(kind, "bad list of primed")

    def test_verify_checks_the_prime_window(self):
        w = World(self)
        w.fake.prime = write_cache_once
        w.both()
        doc = w.doc()
        record = doc["sides"]["cand"]
        rel = record["primed"][0]
        named = {c["name"]: c for c in record["commands"]}
        first = named[s.PRIME + cases.THEORY_UNITS[0]["name"]]["start_ns"]
        last = named[s.PRIME + cases.THEORY_UNITS[-1]["name"]]["end_ns"]
        path = w.root / "cand" / rel
        real = path.stat().st_mtime_ns
        for stamp in (first - 1, last + 1):
            os.utime(path, ns=(stamp, stamp))
            doc = w.doc()
            doc["sides"]["cand"]["products"][rel]["mtime_ns"] = stamp
            with self.assertRaisesRegex(ValueError, "primed cache outside"):
                w.verify(doc)
        os.utime(path, ns=(real, real))
        w.verify()

    def test_verify_checks_the_commands_in_order(self):
        def swap(record):
            c = record["commands"]
            c[5]["start_ns"], c[5]["end_ns"] = c[5]["end_ns"] + 1, \
                c[5]["start_ns"]
        self.tampered(swap, "out of order at")

        def overlap(record):
            c = record["commands"]
            c[6]["start_ns"] = c[5]["end_ns"] - 1
        self.tampered(overlap, "out of order at")

        def shifted(record):
            c = record["commands"]
            c[1]["end_ns"] = c[2]["start_ns"] + 1
        self.tampered(shifted, "out of order at")

    def test_check_prime_refuses_a_cache_that_is_not_a_regular_file(self):
        rel = "src/list/src/.hol/make-deps/listTheory.sig.d"
        seal = {"kind": "link", "link": "x", "mtime_ns": 1}
        with self.assertRaisesRegex(ValueError, "changed products"):
            s.check_prime({}, {rel: seal})
        good = {"kind": "file", "sha256": "0" * 64, "bytes": 1,
                "mtime_ns": 1}
        self.assertEqual(s.check_prime({}, {rel: good}), [rel])

    def test_check_primed_refuses_a_cache_that_is_a_link(self):
        rel = "src/list/src/.hol/make-deps/listTheory.sig.d"
        seal = {"kind": "link", "link": "x", "mtime_ns": 1}
        commands = [dict(name=n, start_ns=0, end_ns=2) for n in s.COMMANDS]
        with self.assertRaisesRegex(ValueError, "bad list of primed"):
            s.check_primed({"primed": [rel]}, commands, {rel: seal}, "x")

    def test_a_failing_prime_fails_the_build(self):
        w = World(self)
        w.fake.fail = "prime"
        with self.assertRaisesRegex(ValueError, "prime-arithmetic failed"):
            w.build("base")

    def test_verify_refuses_a_prime_that_is_not_the_units_command(self):
        w = World(self).both()
        doc = w.doc()
        doc["sides"]["cand"]["commands"][4]["argv"].remove("--no_prereqs")
        with self.assertRaisesRegex(ValueError, "downstream command"):
            w.verify(doc)

    def test_build_and_verify(self):
        w = World(self).both()
        doc = w.doc()
        self.assertEqual(doc["schema"], "task32-independent-build-v4")
        self.assertEqual(doc["sides"]["base"]["tree"],
                         git(w.repo, "rev-parse", w.base_pin + "^{tree}"))
        self.assertEqual(
            [c["name"] for c in doc["sides"]["cand"]["commands"]],
            s.COMMANDS)
        self.assertEqual(s.COMMANDS[:4],
                         ["clone", "checkout", "configure", "build"])
        self.assertEqual(len(s.COMMANDS), 4 + 2 * len(cases.THEORY_UNITS))
        build = doc["sides"]["cand"]["commands"][3]["argv"]
        seq = doc["sides"]["cand"]["sequence"]
        self.assertEqual(build, ["bin/build", "--no-cache", "-t", "-j8",
                                 "--seq=" + seq["path"]])
        data = Path(s.SEQUENCE).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        copy = w.dir / "scratch" / ("task32-%s.seq" % digest)
        self.assertEqual(seq, {
            "path": str(copy), "sha256": digest, "content": data.decode(),
            "source": s.SEQUENCE_REL, "blob": git(
                w.harness, "rev-parse", "HEAD:" + s.SEQUENCE_REL),
            "harness_head": git(w.harness, "rev-parse", "HEAD")})
        self.assertEqual(copy.read_bytes(), data)
        self.assertFalse(os.access(copy, os.W_OK))
        self.assertEqual(doc["sides"]["base"]["sequence"], seq)
        self.assertEqual(set(doc["sides"]["base"]["commands"][0]["env"]),
                         set(s.ENV_KEYS))
        self.assertEqual(doc["sides"]["base"]["cand_pin"], w.cand_pin)
        summary = w.verify(c31="HEAD~1")
        self.assertEqual((summary["status"], summary["base_pin"],
                          summary["cand_pin"], summary["c31"]),
                         ("pass", w.base_pin, w.cand_pin, w.c31))
        self.assertEqual(len(summary["c31"]), 40)
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

    def test_uncommitted_sequence_refused(self):
        w = World(self)
        seq = w.harness / s.SEQUENCE_REL
        seq.write_text(seq.read_text() + "src/extra\n")
        with self.assertRaisesRegex(ValueError, "differs from HEAD"):
            w.build("base")
        self.assertFalse(list((w.dir / "scratch").glob("*.seq")))
        self.assertTrue(w.doc()["sides"]["base"]["incomplete"])
        s.discard_side(w.manifest, "base")
        git(w.harness, "commit", "-qam", "more")
        w.build("base")
        self.assertEqual(
            w.doc()["sides"]["base"]["sequence"]["harness_head"],
            git(w.harness, "rev-parse", "HEAD"))

    def test_immutable_copy_is_shared_and_never_replaced(self):
        w = World(self).both()
        seqs = [w.doc()["sides"][x]["sequence"] for x in s.LABELS]
        self.assertEqual(seqs[0]["path"], seqs[1]["path"])
        self.assertEqual(len(list((w.dir / "scratch").glob("*.seq"))), 1)
        path = Path(seqs[0]["path"])
        path.chmod(0o644)
        path.write_text("other\n")
        with self.assertRaisesRegex(ValueError, "immutable sequence copy"):
            s.sequence_record(w.dir / "scratch", (w.harness,
                                                  s.SEQUENCE_REL))

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

    def test_relative_paths_are_resolved_to_absolute(self):
        w = World(self)
        here = os.getcwd()
        os.chdir(w.dir)
        try:
            w.build("base", tmpdir="tmp", scratch="scratch",
                    logs="ev", root="root", manifest="m.json")
        finally:
            os.chdir(here)
        doc = json.loads((w.dir / "m.json").read_text())["sides"]["base"]
        home, root = Path(doc["home"]), Path(doc["root"])
        self.assertEqual(doc["root"], str((w.dir / "root" / "base")
                                          .resolve()))
        self.assertTrue(home.is_absolute() and root.is_absolute())
        self.assertTrue(home.is_dir())
        self.assertFalse(s.nested(home, root))
        for c in doc["commands"]:
            self.assertTrue(Path(c["log"]).is_absolute())
            self.assertEqual(c["env"]["HOME"], str(home))

    def test_the_root_is_resolved_through_symlinks(self):
        w = World(self)
        link = w.dir / "link"
        link.symlink_to(w.dir / "real-root")
        (w.dir / "real-root").mkdir()
        w.build("base", root=link)
        self.assertEqual(w.doc()["sides"]["base"]["root"],
                         str((w.dir / "real-root" / "base").resolve()))

    def configure_argv(self, given):
        w = World(self)
        w.build("cand", poly=given)
        return [c["argv"] for c in w.doc()["sides"]["cand"]["commands"]
                if c["name"] == "configure"][0]

    def test_a_poly_path_is_made_absolute(self):
        self.assertEqual(self.configure_argv("bin/poly"),
                         [os.path.abspath("bin/poly")])

    def test_a_bare_poly_name_stays_a_path_lookup(self):
        self.assertEqual(self.configure_argv("poly"), ["poly"])

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

    def edit_manifest(self, w, side, **changes):
        doc = w.doc()
        doc["sides"][side].update(changes)
        s.store_manifest(w.manifest, doc)

    def test_discard_guards(self):
        w = World(self).both()
        with self.assertRaisesRegex(ValueError, "--force"):
            s.discard_side(w.manifest, "cand")
        self.edit_manifest(w, "cand", home=str(w.dir / "elsewhere"))
        with self.assertRaisesRegex(ValueError, "scratch home"):
            s.discard_side(w.manifest, "cand", force=True)
        doc = w.doc()
        home = Path(doc["sides"]["base"]["home"])
        self.edit_manifest(w, "cand", home=str(
            home.parent / "home-cand-a0x"))
        with self.assertRaisesRegex(ValueError, "scratch home"):
            s.discard_side(w.manifest, "cand", force=True)
        self.edit_manifest(w, "cand", home=str(home.parent / "home-cand-a0"),
                           alternates=["/elsewhere"])
        with self.assertRaisesRegex(ValueError, "alternates differ"):
            s.discard_side(w.manifest, "cand", force=True)
        root = Path(w.doc()["sides"]["cand"]["root"])
        self.assertTrue(root.exists())
        self.edit_manifest(w, "cand", alternates=w.doc()["sides"]["base"][
            "alternates"])
        s.discard_side(w.manifest, "cand", force=True)
        self.assertFalse(root.exists())

    def test_discard_after_a_killed_clone(self):
        w = World(self)
        w.fake.during = None
        real = w.fake.__call__

        def killed(argv, cwd, env, stdin, log):
            if argv[:2] == ["git", "clone"]:
                Path(log).write_text("")
                raise s.Terminated("SIGTERM")
            return real(argv, cwd, env, stdin, log)

        with self.assertRaises(s.Terminated):
            w.build("cand", runner=killed)
        record = w.doc()["sides"]["cand"]
        self.assertTrue(record["incomplete"])
        self.assertNotIn("alternates", record)
        self.assertEqual(record["commands"], [])
        target = Path(record["root"])
        # nothing was cloned yet
        s.discard_side(w.manifest, "cand")
        self.assertEqual(len(w.doc()["attempts"]), 1)
        # a half-made clone: .git without alternates, or borrowing the
        # recorded repository's objects, is accepted; any other is not
        for text, ok in (("", True), ("%s/.git/objects\n" % w.repo, True),
                         ("/elsewhere/objects\n", False)):
            doc = w.doc()
            doc["sides"]["cand"] = dict(record, home=record["home"])
            s.store_manifest(w.manifest, doc)
            Path(record["home"]).mkdir(parents=True, exist_ok=True)
            put(target / ".git/objects/info/alternates", text) \
                if text else (target / ".git").mkdir(parents=True)
            if ok:
                s.discard_side(w.manifest, "cand")
                self.assertFalse(target.exists())
            else:
                with self.assertRaisesRegex(ValueError, "partial clone"):
                    s.discard_side(w.manifest, "cand")
                shutil.rmtree(target)

    def test_partial_clone_of_a_linked_worktree(self):
        w = World(self)
        wt = w.dir / "linked"
        git(w.repo, "worktree", "add", "-q", "--detach", str(wt))

        def killed(argv, cwd, env, stdin, log):
            Path(log).write_text("")
            raise s.Terminated("SIGTERM")

        with self.assertRaises(s.Terminated):
            s.build_side(wt, "cand", w.cand_pin, w.root, w.manifest,
                         w.dir / "ev", w.dir / "scratch", runner=killed,
                         probe=w.probe, harness=(w.harness, s.SEQUENCE_REL))
        record = w.doc()["sides"]["cand"]
        self.assertEqual(record["repo"], str(wt.resolve()))
        target = Path(record["root"])
        subprocess.run(["git", "clone", "-q", "--shared", "--no-checkout",
                        str(wt), str(target)], check=True, env=GIT_ENV)
        alt = (target / ".git/objects/info/alternates").read_text().strip()
        # the alternate is the common objects directory, not the worktree's
        self.assertEqual(os.path.realpath(alt),
                         os.path.realpath(w.repo / ".git/objects"))
        self.assertNotEqual(os.path.realpath(alt),
                            os.path.realpath(wt / ".git"))
        s.discard_side(w.manifest, "cand")
        self.assertFalse(target.exists())

    def test_directories_are_made_inside_the_guarded_part(self):
        w = World(self)
        (w.dir / "ev").write_text("a file, not a directory")
        with self.assertRaises(OSError):
            w.build("cand")
        record = w.doc()["sides"]["cand"]
        self.assertTrue(record["incomplete"])
        self.assertTrue(Path(record["home"]).exists())
        s.discard_side(w.manifest, "cand")
        self.assertFalse(Path(record["home"]).exists())
        self.assertEqual(len(w.doc()["attempts"]), 1)

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


# the fake build's theories (num and basicSize) and selftest logs: the
# area logs plus the required ones, which share boss and real
THEORIES = 2 + len([1 for k, _, _ in s.REQUIRED_PRODUCTS if k == "theory"])
THEORIES -= 2
LOGS = len({"src/%s/.hol/logs/%s-selftest.log" % (a, a) for a in s.AREAS} |
           {d + "/.hol/logs/" + n for k, d, n in s.REQUIRED_PRODUCTS
            if k == "log"})
BASE_OBJECT = "cccaa27d7099"
REPO = Path(__file__).resolve().parents[4]


def seq_entries(read, name, bang=False):
    """The directories of sequence file `name` (relative to tools/) in
    order, as buildutils.read_buildsequence expands them: `#include`
    against <root>/tools, `[sys]`/`(knl)` selectors (poly, stdknl),
    leading `!` (with `bang`, entries are (number of `!`, directory)
    pairs). `read(path)` returns the text of a repo path."""
    out = []
    for raw in read(posixpath.normpath("tools/" + name)).splitlines():
        line = raw.strip()
        if line.startswith("#include "):
            out += seq_entries(read, line[len("#include "):].strip(), bang)
            continue
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        m = re.match(r"(\[(\w+)\])?(\((\w+)\))?(!*)(.*)", line)
        if m.group(2) in (None, "poly") and \
                m.group(4) in (None, "stdknl"):
            out.append(((len(m.group(5)), m.group(6)) if bang
                        else m.group(6)))
    return out


def holmake_includes(read, directory, strict=True):
    """The INCLUDES of a Holmakefile (as repo-relative directories):
    backslash continuations joined, `ifeq ($(KERNELID),otknl)` blocks
    skipped, `include $(HOLDIR)/src/TeX/mungedeps.hmf` taken as src/TeX."""
    text = read(directory + "/Holmakefile")
    if text is None:
        return []
    out, skip = [], 0
    for line in text.replace("\\\n", " ").splitlines():
        line = line.strip()
        if re.match(r"ifeq\s*\(\$\(KERNELID\),otknl\)", line):
            skip += 1
        elif skip and re.match(r"if(n?eq|n?def)\b", line):
            skip += 1
        elif skip and line == "endif":
            skip -= 1
        elif not skip:
            m = re.match(r"include\s+\$\(HOLDIR\)/(\S+)", line)
            if m and m.group(1) == "src/TeX/mungedeps.hmf":
                out.append("src/TeX")
            m = re.match(r"INCLUDES\s*\+?=\s*(.*)", line)
            for word in (m.group(1).split() if m else []):
                if word.startswith("#"):
                    break
                word = word.replace("$(HOLDIR)", "/H")
                if "$" in word and not strict:
                    continue
                if "$" in word:
                    raise AssertionError("unexpanded %s in %s" %
                                         (word, directory))
                out.append(os.path.relpath(os.path.normpath(
                    os.path.join("/H", directory, word)), "/H"))
    return out


def links_to_sigobj(read, directory):
    """Whether the Holmakefile of `directory` links its own products into
    sigobj: an uncommented `$(HOL_LNSIGOBJ)` recipe line or
    `all: link-to-sigobj` inside an `ifdef HOLBUILD` block."""
    text = read(directory + "/Holmakefile") or ""
    stack = []
    for line in text.replace("\\\n", " ").splitlines():
        line = line.split("#", 1)[0].strip()
        if re.match(r"if(n?eq|n?def)\b", line):
            stack.append(re.match(r"ifdef\s+HOLBUILD\s*$", line) is not None)
        elif line == "endif":
            if stack:
                stack.pop()
        elif any(stack) and (re.match(r"\$\(HOL_LNSIGOBJ\)", line) or
                             re.match(r"all\s*:\s*link-to-sigobj\b", line)):
            return True
    return False


def check_closure(read, exists):
    """Problems of the directories task32.seq adds to upto-parallel:
    each must exist, and each INCLUDES must be an upto-parallel directory,
    one that an upto-parallel directory itself INCLUDES (Holmake builds
    prerequisites), or an earlier addition."""
    base = seq_entries(read, "sequences/upto-parallel")
    own = read(s.SEQUENCE_REL)
    both = seq_entries(read, "../" + s.SEQUENCE_REL)
    assert both[:len(base)] == base
    added = both[len(base):]
    implicit = {i for d in base
                for i in holmake_includes(read, d, False)}
    known = set(base) | implicit
    problems = []
    for d in added:
        if not exists(d):
            problems.append("missing directory " + d)
        for inc in holmake_includes(read, d):
            if inc not in known:
                problems.append("%s: INCLUDES %s is not built before" %
                                (d, inc))
        known.add(d)
    assert own
    # `!` (built at -t, never uploaded by bin/build) exactly for the
    # directories that link themselves to sigobj, else bin/build's upload
    # fails with "File exists"; and for test directories, which must not
    # be uploaded (they only run at -t).
    bangs = {d: n for n, d in
             seq_entries(read, "../" + s.SEQUENCE_REL, True)[len(base):]}
    marked = {d for d, n in bangs.items() if n}
    for d in added:
        want = links_to_sigobj(read, d) or \
            bool({"test", "tests", "testing"} & set(d.split("/")))
        if want and d not in marked:
            problems.append("%s: needs a leading `!`" % d)
        if bangs[d] > 1:
            problems.append("%s: must be exactly one `!`" % d)
        if d in marked and not want:
            problems.append("%s: has `!` but no link-to-sigobj rule" % d)
    return added, problems


class SequenceClosureTests(unittest.TestCase):
    def test_current_tree(self):
        def read(path):
            f = REPO / path
            return f.read_text() if f.is_file() else None
        added, problems = check_closure(read, lambda d: (REPO / d).is_dir())
        self.assertEqual(problems, [])
        self.assertEqual(len(added), len(set(added)))
        for need in ("src/integer", "src/rational", "src/real",
                     "src/real/analysis", "src/integer/testing"):
            self.assertIn(need, added)
        self.assertEqual(added[-1], "src/integer/testing")
        self.assertTrue(any(
            l.startswith("!src/integer/testing")
            for l in Path(s.SEQUENCE).read_text().splitlines()))

    def test_marking_rule(self):
        link = ("ifdef HOLBUILD\nall: link-to-sigobj\n"
                "link-to-sigobj: $(DEFAULT_TARGETS)\n\t$(HOL_LNSIGOBJ)\n"
                "endif\n")
        files = {
            "tools/sequences/upto-parallel": "src/base\n",
            "src/base/Holmakefile": "",
            "src/plain/Holmakefile": link,
            "src/bang/Holmakefile": "",
            "src/bangs/Holmakefile": link,
            "src/quiet/Holmakefile": "# ifdef HOLBUILD\n"
                "# all: link-to-sigobj\n# link-to-sigobj:\n"
                "# \t$(HOL_LNSIGOBJ)\n# endif\n",
        }

        def check(seq):
            files[s.SEQUENCE_REL] = \
                "#include sequences/upto-parallel\n" + seq
            return check_closure(files.get, lambda d: True)[1]
        self.assertEqual(check("src/plain\n"),
                         ["src/plain: needs a leading `!`"])
        self.assertEqual(check("!src/bang\n"),
                         ["src/bang: has `!` but no link-to-sigobj rule"])
        self.assertEqual(check("!!src/bangs\n"),
                         ["src/bangs: must be exactly one `!`"])
        self.assertEqual(check("src/quiet\n!src/bangs\n"), [])

    def test_base_tree(self):
        have = subprocess.run(["git", "-C", str(REPO), "cat-file", "-e",
                               BASE_OBJECT], stdin=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL).returncode == 0
        if not have:
            self.skipTest("base object %s is not in this repository"
                          % BASE_OBJECT)

        def show(path):
            r = subprocess.run(["git", "-C", str(REPO), "show",
                                "%s:%s" % (BASE_OBJECT, path)],
                               stdin=subprocess.DEVNULL,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.DEVNULL)
            return r.stdout.decode() if r.returncode == 0 else None

        def read(path):
            if path == s.SEQUENCE_REL:   # the sequence is not in the base
                return (REPO / path).read_text()
            return show(path)

        def exists(d):
            return subprocess.run(
                ["git", "-C", str(REPO), "cat-file", "-e",
                 "%s:%s" % (BASE_OBJECT, d)], stdin=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL).returncode == 0
        added, problems = check_closure(read, exists)
        self.assertEqual(problems, [])
        self.assertTrue(added)


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
        self.fails("cannot resolve", c31="1" * 40)
        self.fails("cannot resolve", c31="nosuchrev")
        self.assertEqual(self.w.verify(c31=self.w.c31)["status"], "pass")

    def c31_differing_in(self, path):
        """A commit equal to the candidate pin plus one file, built with
        commit-tree so the shared fixture's HEAD never moves."""
        repo = self.w.repo
        with tempfile.TemporaryDirectory() as scratch:
            env = dict(os.environ, GIT_INDEX_FILE=scratch + "/index")
            def run(*args, **kw):
                return subprocess.run(
                    ["git", "-C", str(repo), *args], env=env, check=True,
                    stdout=subprocess.PIPE, **kw).stdout.decode().strip()
            run("read-tree", self.w.cand_pin)
            blob = run("hash-object", "-w", "--stdin", input=b"x\n")
            run("update-index", "--add", "--cacheinfo",
                "100644," + blob + "," + path)
            tree = run("write-tree")
        return git(repo, "commit-tree", tree, "-p", self.w.cand_pin,
                   "-m", "boundary")

    def test_test_only_boundary(self):
        c31 = self.c31_differing_in("src/num/tests/x.sml")
        self.assertEqual(self.w.verify(c31=c31)["status"], "pass")
        for path in ("src/boss/theory_tests/x.sml", "src/boss/tests.sml",
                     "src/mytests/x", "tools/Holmake/tests/x",
                     "src/boss/bossLib.sml"):
            with self.subTest(path=path):
                self.fails("compiled sources differ",
                           c31=self.c31_differing_in(path))

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

    def test_theory_rerun_restores_to_a_passing_tree(self):
        folder = self.cand / "src/num/theories"
        files = s.theory_target_files(folder, "num")
        self.assertEqual(sorted(files), sorted([
            ".hol/objs/numTheory.sml", ".hol/objs/numTheory.dat",
            ".hol/objs/numTheory.uo", ".hol/objs/numTheory.cachekey",
            ".hol/docs/numTheory.html",
            ".hol/make-deps/numTheory.sml.d"]))
        self.assertEqual(s.theory_target_files(folder, "nothing"), [])
        backup = {rel: ((folder / rel).read_bytes(),
                        (folder / rel).stat().st_mtime_ns) for rel in files}
        # a rerun rewrites the lock (process ids) and every target file
        put(folder / ".hol/locks/numTheory.uo.lock", "99999\n")
        put(folder / ".hol/locks/numTheoryScript.lock", "1\n")
        self.assertEqual(self.w.verify()["status"], "pass")
        for rel in files:
            put(folder / rel, "rewritten %s\n" % rel)
        self.fails("product changed")
        for rel, (data, mtime) in backup.items():
            (folder / rel).write_bytes(data)
            os.utime(folder / rel, ns=(mtime, mtime))
        self.assertEqual(self.w.verify()["status"], "pass")

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
        for c in record["commands"][:2]:
            c["start_ns"] = c["end_ns"] = 1
        record["commands"][2]["start_ns"] = 1
        record["build_interval_ns"][0] = 1
        record["commands"][3]["end_ns"] = 2**62
        for c in record["commands"][4:]:
            c["start_ns"] = c["end_ns"] = 2**62
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
            "cand", "commands", 3, "argv",
            value=["bin/build", "-j4", "--seq=" + self.doc["sides"]["cand"][
                "sequence"]["path"]]))

    def reseal(self, doc, side, **fields):
        seq = doc["sides"][side]["sequence"]
        seq.update(fields)
        if "content" in fields:
            seq["sha256"] = hashlib.sha256(
                seq["content"].encode()).hexdigest()

    def test_sequence_mismatch_refused(self):
        doc = self.w.doc()
        cand = doc["sides"]["cand"]
        cand["sequence"]["path"] = "/x/other.seq"
        cand["commands"][3]["argv"][-1] = "--seq=/x/other.seq"
        self.fails("build sequence differs between sides", doc)
        doc = self.w.doc()
        self.reseal(doc, "base", content="src/extra\n")
        self.fails("build sequence differs between sides", doc)
        doc = self.w.doc()
        doc["sides"]["cand"]["sequence"]["sha256"] = "0" * 64
        self.fails("does not match its digest", doc)
        doc = self.w.doc()
        for side in s.LABELS:
            self.reseal(doc, side, content="src/extra\n")
        self.fails("immutable sequence file changed", doc)
        doc = self.w.doc()
        doc["sides"]["cand"]["sequence"]["blob"] = "1" * 40
        self.fails("build sequence differs between sides", doc)

    def test_sequence_file_changed_or_gone(self):
        path = Path(self.doc["sides"]["cand"]["sequence"]["path"])
        path.chmod(0o644)
        path.write_text("tampered\n")
        self.fails("immutable sequence file changed")
        path.unlink()
        self.fails("immutable sequence file changed")

    def test_sequence_must_be_the_one_built_with(self):
        doc = self.w.doc()
        del doc["sides"]["cand"]["sequence"]
        self.fails("no build sequence record", doc)
        doc = self.w.doc()
        for side in s.LABELS:
            doc["sides"][side]["sequence"]["path"] = "/x/other.seq"
        self.fails("did not use the recorded sequence", doc)

    def test_sequence_path_must_be_absolute(self):
        doc = self.w.doc()
        for side in s.LABELS:
            doc["sides"][side]["sequence"]["path"] = "task32.seq"
            doc["sides"][side]["commands"][3]["argv"][-1] = \
                "--seq=task32.seq"
        self.fails("sequence path is not absolute", doc)

    def test_required_products_are_verified(self):
        for kind, directory, name in s.REQUIRED_PRODUCTS:
            path = s.required_path(self.cand, kind, directory, name)
            self.assertIsNotNone(path, name)
        victim = self.cand / s.required_path(
            self.cand, "file", "src/real/analysis", "realheap")
        victim.unlink()
        doc = self.w.doc()
        del doc["sides"]["cand"]["products"][
            "src/real/analysis/realheap"]
        self.fails("cand: required products missing: "
                   "file src/real/analysis/realheap", doc)

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

    def test_changed_toolchain_is_reported_in_report_mode(self):
        self.assertEqual(self.w.verify()["toolchain"],
                         {"status": "same", "changed": []})
        self.w.probe = lambda p, e: dict(
            TOOLCHAIN, files={"poly": {"path": "/p", "sha256": "2" * 64}},
            poly_v="Poly/ML 5.9.3 RTS version: x", extra="1")
        summary = self.w.verify(toolchain="report")
        self.assertEqual(summary["status"], "pass")
        self.assertEqual(summary["toolchain"], {
            "status": "changed", "changed": ["extra", "files", "poly_v"]})
        self.fails("toolchain", toolchain="refuse")
        self.fails("toolchain")

    def test_poly_v_is_compared_by_poly_version_matches(self):
        with mock.patch.object(a, "poly_version_matches",
                               return_value=True) as same:
            self.w.probe = lambda p, e: dict(TOOLCHAIN, poly_v="other")
            for mode in ("refuse", "report"):
                self.assertEqual(self.w.verify(toolchain=mode)[
                    "toolchain"]["status"], "same")
        self.assertEqual(same.call_count, 2)

    def test_other_checks_still_refuse_in_report_mode(self):
        put(self.cand / "src/f.txt", "dirty\n")
        self.fails("dirty or patched", toolchain="report")

    def test_unknown_toolchain_mode(self):
        self.fails("toolchain mode", toolchain="ignore")

    def test_toolchain_option_of_the_command_line(self):
        self.w.probe = lambda p, e: dict(TOOLCHAIN, cc="gcc 2")
        stream = io.StringIO()
        with mock.patch.object(s, "probe_toolchain", self.w.probe), \
                contextlib.redirect_stdout(stream):
            code = s.main(self.w.argv("verify", "--toolchain", "report"))
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(stream.getvalue())["toolchain"],
                         {"status": "changed", "changed": ["cc"]})
        with mock.patch.object(s, "probe_toolchain", self.w.probe), \
                self.assertRaisesRegex(ValueError, "toolchain changed: cc"):
            s.main(self.w.argv("verify"))
        with self.assertRaises(SystemExit):
            s.main(self.w.argv("compare", "--toolchain", "report"))

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
        self.fails("out of order", doc)

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
        doc["schema"] = "task32-independent-build-v3"
        self.fails("moved aside.*fresh manifest and a fresh evidence "
                   "directory", doc)
        with self.assertRaisesRegex(ValueError, "moved aside"):
            s.require_schema(doc)


class CompareTests(unittest.TestCase):
    def setUp(self):
        self.w = World(self).both()
        self.doc = self.w.doc()
        self.cand = Path(self.doc["sides"]["cand"]["root"])
        self.base = Path(self.doc["sides"]["base"]["root"])

    def run_compare(self, **kw):
        return s.compare(self.w.doc(), **kw)

    def test_identical_behaviour_passes(self):
        out = self.run_compare()
        self.assertEqual(out["status"], "pass", out["blocked"])
        self.assertEqual(out["theories"]["common"], 2 + THEORIES)
        self.assertEqual(out["logs"]["common"], LOGS)
        names = [n for n, _, _ in s.LOG_RULES]
        self.assertEqual(out["normalization"]["logs"][
            names.index("gc-tag")][0], "gc-tag")

    def test_tracked_theory_sources_are_not_compared(self):
        # TRACKED_SIG differs between the commits and is not a product
        out = self.run_compare()
        self.assertNotIn(TRACKED_SIG, out["theories"]["differing"])
        self.assertEqual(out["theories"]["common"], 2 + THEORIES)

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

    def write_dat(self, rel, base_text, cand_text):
        put(self.base / rel, base_text)
        put(self.cand / rel, cand_text)

    def dat_files(self, out):
        return {r["path"]: r for r in out["dat_canonical"]["files"]}

    def test_unparsable_dat_difference_blocks(self):
        put(self.cand / DAT, "z")
        out = self.run_compare()
        self.assertEqual(out["status"], "blocked")
        self.assertIn("parse failure", self.dat_files(out)[DAT]["error"])

    def test_table_reorder_is_equal(self):
        self.write_dat(DAT.replace("num", "t"), mk_dat("t"), mk_dat(
            "t", strings=["x", "t", "bool", "c", "min"],
            types=["bool", "alpha"], terms=["c", "x", "ap"]))
        out = self.run_compare()
        rel = DAT.replace("num", "t")
        self.assertEqual(out["status"], "pass", out["blocked"])
        record = self.dat_files(out)[rel]
        self.assertTrue(record["equal"])
        self.assertEqual(record["base"], record["cand"])
        self.assertEqual(len(out["dat_canonical"]["module_sha256"]), 64)
        json.dumps(out)

    def test_content_differences_block(self):
        rel = DAT.replace("num", "t")
        variants = {
            "hyp": mk_dat("t", hyps=("x",)),
            "tag": mk_dat("t", tags=("DISK_THM", "ORACLE")),
            "newsig": mk_dat("t", newsig_arity=2),
            "thydata": mk_dat("t", deltas=4),
            "parent": mk_dat("t", parents=[("a", "h")]),
            "name": mk_dat("u")}
        for what, text in variants.items():
            self.write_dat(rel, mk_dat("t"), text)
            out = self.run_compare()
            self.assertEqual(out["status"], "blocked", what)
            self.assertFalse(self.dat_files(out)[rel]["equal"], what)

    THYDATA = {
        "tag-knm": '("k" (tag-knm 3 . 5))',
        "tag-str": '("k" (tag-str . 5))',
        "tag-ty": '("k" (tag-ty . "%0"))',
        "tag-th": '("k" (tag-th ("t" 0 nil nil) ("%0") "t" 1))',
        "raw ints": '("GrammarAncestry" 5)'}
    STRINGS = ["min", "bool", "c", "t", "x", "e1"]

    def test_changed_table_entry_behind_an_unchanged_index_blocks(self):
        rel = DAT.replace("num", "t")
        for what, extra in self.THYDATA.items():
            same = mk_dat("t", strings=self.STRINGS, extra=extra)
            by_string = mk_dat("t", strings=self.STRINGS[:5] + ["e2"],
                               extra=extra)
            by_term = mk_dat("t", strings=self.STRINGS, extra=extra,
                             xname="y")
            uses = "term" if what in ("tag-ty", "tag-th") else "string"
            other = by_term if uses == "term" else by_string
            self.write_dat(rel, same, other)
            out = self.run_compare()
            self.assertEqual(out["status"], "blocked", what)
            self.assertFalse(self.dat_files(out)[rel]["equal"], what)
        # the string table behind a raw integer list and a tag-str
        self.write_dat(rel, mk_dat("t", strings=self.STRINGS,
                                   extra=self.THYDATA["raw ints"]),
                       mk_dat("t", strings=self.STRINGS[:5] + ["e2"],
                              extra=self.THYDATA["raw ints"]))
        record = self.dat_files(self.run_compare())[rel]
        self.assertEqual(record["fallback"], {"base": True, "cand": True})

    def test_a_quoted_string_is_not_a_tag(self):
        for tag in ("tag-str", "tag-tm", "tag-ty", "tag-ch", "tag-knm"):
            text = mk_dat("t", strings=self.STRINGS, extra={
                "tag-knm": '("k" ("tag-knm" 3 . 5))',
                "tag-ch": '("k" ("tag-ch" . 5))',
                "tag-str": '("k" ("tag-str" . 5))',
                "tag-tm": '("k" ("tag-tm" . "%0"))',
                "tag-ty": '("k" ("tag-ty" . "%0"))'}[tag])
            canon = dat.canonical(text)
            self.assertTrue(canon["fallback"], tag)
            self.assertIn(["t", tag], json.loads(json.dumps(
                canon["thydata"]))[-1][1][1][1], tag)
        # the same data with a symbol tag does not need the fallback
        self.assertFalse(dat.canonical(mk_dat(
            "t", strings=self.STRINGS,
            extra='("k" (tag-str . 5))'))["fallback"])

    def test_resolved_references_survive_a_table_reorder(self):
        rel = DAT.replace("num", "t")

        def extra(sidx, tmidx):
            return ('("k" (tag-knm %d . %d) (tag-str . %d) (tag-ty . "%%%d")'
                    ' (tag-th ("t" 0 nil nil) ("%%%d") "t" 1))'
                    % (sidx["t"], sidx["e1"], sidx["e1"], tmidx["x"],
                       tmidx["x"]))

        self.write_dat(rel, mk_dat("t", strings=self.STRINGS, extra=extra),
                       mk_dat("t", strings=["e1", "x", "t", "c", "bool",
                                            "min"],
                              terms=["c", "x", "ap"], types=["bool", "alpha"],
                              extra=extra))
        out = self.run_compare()
        self.assertEqual(out["status"], "pass", out["blocked"])
        self.assertEqual(self.dat_files(out)[rel]["fallback"],
                         {"base": False, "cand": False})

    def test_real_format_fixture(self):
        c = dat.canonical(REAL_DAT)
        self.assertEqual(c["name"], "basicSize")
        self.assertEqual(len(c["parents"]), 3)
        self.assertEqual(len(c["thms"]), 9)
        self.assertEqual(c["thms"][0]["tags"], ["DISK_THM"])
        base = dat.digest(c)[0]
        for old, new in (
                ('("%0$0U28%19B20|U10")', '("%0$0U28%19B20|U10" "%0")'),
                ('"DISK_THM") (1 0)\n    ("%1%2%4$2', '"OTHER") (1 0)\n'
                 '    ("%1%2%4$2'),
                ('("bool_size" . 37)', '("bool_size" . 38)'),
                ('(tag-knm 24 . 41)', '(tag-knm 24 . 42)'),
                ('(tag-tm . "%28")', '(tag-tm . "%29")'),
                ('("sum_size" . 40)\n  ("pair_size" . 44)',
                 '("sum_size" . 41)\n  ("pair_size" . 44)')):
            self.assertIn(old, REAL_DAT)
            other = dat.digest(dat.canonical(REAL_DAT.replace(old, new, 1)))
            self.assertNotEqual(other[0], base, old)

    def test_parent_hash_masked_only_for_an_equal_parent(self):
        a_rel, b_rel = (DAT.replace("numTheory", n + "Theory")
                        for n in ("a", "b"))
        a_same = mk_dat("a")
        a_reordered = mk_dat("a", strings=["x", "a", "bool", "c", "min"])
        # the parent compares equal, so the hash of it may differ
        self.write_dat(a_rel, a_same, a_reordered)
        self.write_dat(b_rel, mk_dat("b", parents=[("a", "h1")]),
                       mk_dat("b", parents=[("a", "h2")]))
        out = self.run_compare()
        self.assertEqual(out["status"], "pass", out["blocked"])
        self.assertEqual(self.dat_files(out)[b_rel]["masked_parents"],
                         ["a"])
        # the parent differs: its hash is not masked and the child blocks
        self.write_dat(a_rel, a_same, mk_dat("a", hyps=("x",)))
        out = self.run_compare()
        files = self.dat_files(out)
        self.assertFalse(files[a_rel]["equal"])
        self.assertFalse(files[b_rel]["equal"])
        self.assertEqual(files[b_rel]["masked_parents"], [])
        # a parent that is not compared at all is not masked either
        self.write_dat(a_rel, a_same, a_same)
        self.write_dat(b_rel, mk_dat("b", parents=[("zz", "h1")]),
                       mk_dat("b", parents=[("zz", "h2")]))
        self.assertEqual(self.run_compare()["status"], "blocked")
        # equal bytes need no canonical form
        self.write_dat(b_rel, mk_dat("b"), mk_dat("b"))
        self.assertEqual(self.run_compare()["status"], "pass")

    def test_pins_are_recorded(self):
        out = s.compare(self.w.doc(), {"c31": "c" * 40})
        self.assertEqual(out["pins"], {"c31": "c" * 40})

    def test_only_selftest_logs_are_compared(self):
        self.write_dat("src/num/.hol/logs/other.log", "a", "b")
        out = self.run_compare()
        self.assertEqual(out["status"], "pass", out["blocked"])
        self.assertNotIn("src/num/.hol/logs/other.log",
                         [d["path"] for d in out["logs"]["differing"]])
        self.assertEqual(out["logs"]["common"], LOGS)

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

    def test_required_products_block_compare(self):
        for kind, directory, name in s.REQUIRED_PRODUCTS:
            label = "base" if len(name) % 2 else "cand"
            root = self.base if label == "base" else self.cand
            victim = root / s.required_path(root, kind, directory, name)
            saved = victim.read_bytes()
            victim.unlink()
            out = s.compare(self.w.doc())
            self.assertIn("missing required product on %s: %s %s/%s"
                          % (label, kind, directory, name), out["blocked"])
            victim.write_bytes(saved)
        self.assertEqual(s.compare(self.w.doc())["status"], "pass")

    def test_required_products_follow_the_workloads(self):
        names = {(d, n) for _, d, n in s.REQUIRED_PRODUCTS}
        for need in (("src/rational", "rat"), ("src/integer", "integer"),
                     ("src/integer", "integer_word"),
                     ("src/real", "real"), ("src/real", "real_sigma"),
                     ("src/real/analysis", "lim"),
                     ("src/real/analysis", "realheap"),
                     ("src/num/theories", "arithmetic"),
                     ("src/num/extra_theories", "logroot"),
                     ("src/list/src", "rich_list"),
                     ("src/pred_set/src", "pred_set"),
                     ("src/integer/testing", "integer2-selftest.log"),
                     ("src/real/analysis", "real-selftest2.log")):
            self.assertIn(need, names)
        self.assertIn("rational", s.AREAS)

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

    def test_pad_and_backspaces_are_presentation(self):
        head = b"EL_CONV 5 fEL [a; b; c] 1 ..." + b" " * 20
        base = head + 27 * b"\x08" + b"[GC = 0.075] (0.000s)      OK\n"
        cand = head + 14 * b"\x08" + b"(0.000s)      OK\n"
        self.assertNotEqual(base, cand)
        self.assertEqual(s.normalize_log(base, "/r"),
                         s.normalize_log(cand, "/r"))
        other = head + 14 * b"\x08" + b"(0.000s)      FAILED\n"
        self.assertNotEqual(s.normalize_log(other, "/r"),
                            s.normalize_log(cand, "/r"))
        moved = b"EL_CONV 5 fEL [a; b; d] 1 ..." + b" " * 20 + \
            14 * b"\x08" + b"(0.000s)      OK\n"
        self.assertNotEqual(s.normalize_log(moved, "/r"),
                            s.normalize_log(cand, "/r"))

    def test_name_is_compared_when_the_tail_is_longer(self):
        pad = b" " * 4
        one = b"EL_CONV 5 fEL" + pad + 9 * b"\x08" + b"(0.000s) OK\n"
        two = b"EL_CONV 6 fEL" + pad + 9 * b"\x08" + b"(0.000s) OK\n"
        self.assertNotEqual(s.normalize_log(one, "/r"),
                            s.normalize_log(two, "/r"))
        self.assertEqual(s.normalize_log(one, "/r"),
                         "EL_CONV 5 fEL (<TIME>) OK\n")

    def test_rule_order_is_fixed(self):
        names = [n for n, _, _ in s.LOG_RULES]
        self.assertEqual(names, [n for n, _, _ in s.NORMALIZERS])
        self.assertEqual(len(names), len(set(names)))
        self.assertLess(names.index("ansi"), names.index("pad-backspace"))
        self.assertLess(names.index("pad-backspace"),
                        names.index("gc-tag"))

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
        result = json.loads(self.out.read_text())
        self.assertEqual((code, result["status"]), (0, "pass"))
        self.assertEqual(result["pins"]["c31"], self.w.c31)
        self.assertEqual(result["pins"]["cand_pin"], self.w.cand_pin)
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
        args = ["discard", "--repo", str(self.w.repo), "--manifest",
                str(self.w.manifest), "--side", "cand"]
        with self.assertRaisesRegex(ValueError, "--force"):
            self.run_main(*args)
        code, _ = self.run_main(*args, "--force")
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
        for name in ("task32_snapshots.py", "task32_dat.py",
                     "test_task32_snapshots.py"):
            for n, line in enumerate(Path(s.HERE / name).read_text()
                                     .splitlines(), 1):
                self.assertNotIn("\t", line, (name, n))
                self.assertEqual(line, line.rstrip(), (name, n))
                self.assertLess(len(line), 80, (name, n))


if __name__ == "__main__":
    unittest.main()
