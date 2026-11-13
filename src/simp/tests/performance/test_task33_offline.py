"""task33_offline.py on fake trees, fake logs and a fake archive: no HOL,
no build, no measurement."""
import contextlib
import copy
import gzip
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import acceptance as a
import task33_offline as t
import task32_downstream as d

FILES = {
    "src/1/ThmAttribute.sig": "signature ThmAttribute =\nsig\n"
                              "  val is_attribute : string -> bool\nend\n",
    "src/1/ThmAttribute.sml": "structure ThmAttribute :> ThmAttribute =\n"
                              "struct\n  fun is_attribute a = true\nend\n",
    "src/simp/src/Cond_rewr.sig": "signature Cond_rewr =\nsig\n"
                                  "  val with_tracking : int -> int\nend\n",
    "src/simp/src/Cond_rewr.sml": "structure Cond_rewr :> Cond_rewr =\n"
                                  "struct\n  fun with_tracking x = x\nend\n",
    "src/simp/src/simpLib.sml": "structure simpLib =\nstruct\nend\n",
    "src/simp/src/congLib.sml": "structure congLib =\nstruct\nend\n",
    "src/simp/src/simpLib.sig": "signature simpLib =\nsig\nend\n",
    "src/simp/src/congLib.sig": "signature congLib =\nsig\nend\n",
    "src/boss/bossLib.sig": "signature bossLib =\nsig\nend\n",
    "src/boss/bossLib.sml": "structure bossLib =\nstruct\nend\n",
    "src/boss/Holmakefile": "boss_deps = listTheory\nall: x\n"
                            "\t$(HOL) buildheap -o $(T) -b $(H) $(boss_deps)"
                            " bossLib\n",
    "src/list/listScript.sml": "val _ = new_theory \"list\";\n",
}
# module -> (directory, dependencies)
MODULES = {
    "ThmAttribute": ("src/1", []),
    "Cond_rewr": ("src/simp/src", ["ThmAttribute"]),
    "simpLib": ("src/simp/src", ["Cond_rewr"]),
    "congLib": ("src/simp/src", ["simpLib"]),
    "bossLib": ("src/boss", ["simpLib"]),
    "listTheory": ("src/list", []),
}
SPECS = {"hol.state": dict(dir="src/boss", vars=("boss_deps",),
                           recipe=True)}
S2 = dict(
    structures=[dict(structure="X", parts=["sig"], paths=["p.sig"],
                     mechanism="m", allowed_kinds=["code"],
                     forbidden_kinds=["state"], reference="r")],
    total_delta=[dict(
        heap="bin/hol.state", kinds=["state-empty", "first-use"],
        rule="r", value=5, unit="words", mechanism="m", reference="r",
        observed=dict(base=100, cand=105, d_base=10, d_cand=11, exclusive={
            "simpLib": [3, 2], "Traverse": [1, 1], "Travrules": [1, 1],
            "Opening": [1, 1], "boolSimps": [1, 1], "pureSimps": [1, 1]}),
        paths=["p.sig"], allowed_kinds=["code"],
        forbidden_kinds=["state", "per-object"])])
E2C = dict(rule="r", probe_support=dict(
    justification="j", registers=dict(structures=["P"])),
    extension_state=[dict(
        name="n", created_by="c", where="w", source="s", required=True,
        observable=True, registers=dict(structures=["X"]))])
# every marker-less required log has the one OK line, `Ran` block or
# manifest line that HarvestTest writes
COUNTS = {n: 1 for n in t.LOGS_REQUIRED if t.needs_count(n)}
# The OK lines the shared theory scripts of the pooled logs print, and the
# scripts (one tprint string per OK line, as in the real ones).
SHARED_LINES = [
    "parent persistent addition and same-theory removal",
    "child sees fresh parent addition/removal replay",
    "child persistent named retraction and addition",
    "fresh descendant preserves qualified REMOVE keys"]
SHARED_SCRIPTS = {
    "src/simp/tests/split-persistence/splitParentScript.sml":
        SHARED_LINES[:1],
    "src/simp/tests/split-persistence/splitChildScript.sml":
        SHARED_LINES[1:3],
    "src/simp/tests/split-persistence/splitDescendantScript.sml":
        SHARED_LINES[3:]}
POOL_ID = "E1.logs.split-lifecycle+split-persistence"


def shared_script(lines):
    return "(* tprint \"in a comment\" *)\n" + "".join(
        'val _ = testutils.tprint "%s"\nval _ = testutils.OK ()\n' % x
        for x in lines)


def pooled_log(own, shared):
    """A log of a pooled suite: `own` OK lines of its own, the OK lines of
    the `shared` theory-script strings."""
    return "".join("own %d ...  OK\n" % i for i in range(own)) + "".join(
        "%s ...                 OK\n" % x for x in shared) + \
        "OBS result=pass\n"
DECLARED_PATH = "src/1/ThmAttribute.sig"
ADDED_VAL = "  val attribute_fns : string -> int option\n"


def git(repo, *argv):
    p = subprocess.run(["git", "-C", str(repo), *argv],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       stdin=subprocess.DEVNULL, check=True)
    return p.stdout.decode().strip()


def write(root, files):
    for rel, text in files.items():
        f = Path(root) / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)


def write_uo(root, modules, extra=None):
    """sigobj/<m>.uo and .ui in the format of a Holmake build."""
    for name, (directory, deps) in modules.items():
        deps = list(deps) + list((extra or {}).get(name, ()))
        lines = ["$(HOLDIR)/sigobj/" + d for d in deps]
        lines.append("$(HOLDIR)/%s/%s" % (directory, name))
        src = "%s/%s.sml" % (directory, name)
        uo = lines + ["$(HOLDIR)/" + src]
        sig = "$(HOLDIR)/%s/%s.sig" % (directory, name)
        # as Holmake builds: the objects in the directory, linked from
        # sigobj
        objs = Path(root) / directory / ".hol" / "objs"
        objs.mkdir(parents=True, exist_ok=True)
        (Path(root) / "sigobj").mkdir(parents=True, exist_ok=True)
        for ext, text in ((".uo", uo), (".ui", lines + [sig])):
            (objs / (name + ext)).write_text("\n".join(text) + "\n")
            link = Path(root) / "sigobj" / (name + ext)
            if link.is_symlink() or link.exists():
                link.unlink()
            link.symlink_to(objs / (name + ext))


class World:
    """A git repository with a base and a candidate commit, and a root
    (snapshot) tree for each: `change` maps path -> new text."""

    def __init__(self, raw, change=None, new_modules=None, extra_deps=None):
        self.raw = Path(raw)
        self.repo = self.raw / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.email", "t@example.invalid")
        git(self.repo, "config", "user.name", "t")
        write(self.repo, FILES)
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "base")
        self.base = git(self.repo, "rev-parse", "HEAD")
        self.change = dict(change or {})
        write(self.repo, self.change)
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "cand", "--allow-empty")
        self.cand = git(self.repo, "rev-parse", "HEAD")
        self.roots = {}
        for side, files in (("base", FILES), ("cand",
                                              {**FILES, **self.change})):
            root = self.raw / side
            write(root, files)
            mods = dict(MODULES)
            if side == "cand":
                mods.update(new_modules or {})
            write_uo(root, mods, extra_deps if side == "cand" else None)
            self.roots[side] = root
            self.write_products(root)

    PRODUCTS = {"listTheory.sml": "structure listTheory = struct end\n",
                "listTheory.sig": "signature listTheory = sig end\n",
                "listTheory.dat": "dat\n"}

    def write_products(self, root, **override):
        for name, text in {**self.PRODUCTS, **override}.items():
            f = Path(root) / "src/list/.hol/objs" / name
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(text.replace("$ROOT", str(root)))

    # ---- pooled logs (split-lifecycle + split-persistence)

    def pool(self, life, pers, decl=None):
        """The harvest rows with the two pooled logs given as (own lines,
        shared lines) pairs."""
        with tempfile.TemporaryDirectory() as raw:
            root = self.tree(raw, **{"split-lifecycle": pooled_log(*life),
                                     "split-persistence":
                                     pooled_log(*pers)})
            checks = t.Checks()
            data = t.harvest(root, Path(raw) / "out", checks,
                             decl or self.DECL)
            return data, {c["id"]: c for c in checks.rows}

    def test_a_pooled_group_passes_with_either_race_outcome(self):
        decl = dict(log_counts=dict(COUNTS, **{"split-lifecycle": 2221,
                                               "split-persistence": 166}))
        # lifecycle won the race (2221/166), then persistence did
        # (2217/170): the same 2387 OK lines either way
        for life, pers in (((2217, SHARED_LINES), (166, [])),
                           ((2217, []), (166, SHARED_LINES)),
                           ((2217, SHARED_LINES[:3]),
                            (166, SHARED_LINES[3:]))):
            with self.subTest(life=len(life[1]), pers=len(pers[1])):
                data, rows = self.pool(life, pers, decl)
                self.assertEqual(ok_ids(rows), [])
                self.assertEqual(rows[POOL_ID]["status"], "pass")
        decl = dict(log_counts=dict(COUNTS, **{"split-lifecycle": 2217,
                                               "split-persistence": 170}))
        data, rows = self.pool((2217, []), (166, SHARED_LINES), decl)
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["pooled"][0]["total"], 2387)

    def test_a_pooled_group_replaces_the_per_log_checks(self):
        data, rows = self.pool((1, SHARED_LINES), (1, []))
        self.assertEqual(ok_ids(rows), [])
        self.assertIn(POOL_ID, rows)
        self.assertEqual([i for i in rows if "split-" in i
                          and "registration" not in i], [POOL_ID])
        self.assertTrue(all(f["passed"] for f in data["files"]))
        self.assertEqual(
            sorted(f["counts"]["ok_lines"] for f in data["files"]
                   if "split-l" in f["path"] or "split-p" in f["path"]),
            [1, 5])

    def test_a_pooled_group_fails_when_the_sum_differs(self):
        for life, pers in (((1, SHARED_LINES), (2, [])),
                           ((0, SHARED_LINES), (1, [])),
                           ((1, SHARED_LINES), (0, []))):
            with self.subTest(life=life[0], pers=pers[0]):
                _, rows = self.pool(life, pers)
                self.assertEqual(ok_ids(rows), [POOL_ID])
                self.assertIn("reviewed 6", rows[POOL_ID]["reason"])

    def test_a_shared_line_twice_or_missing_fails(self):
        # the sum is right in both
        for life, pers, what in (
                ((1, SHARED_LINES), (0, SHARED_LINES[:1]), "twice"),
                ((1, SHARED_LINES[:3]), (1, []), "missing")):
            with self.subTest(what):
                decl = dict(log_counts=dict(COUNTS, **{
                    "split-lifecycle": 1 + len(life[1]),
                    "split-persistence": pers[0] + len(pers[1])}))
                if what == "missing":
                    life = (2, SHARED_LINES[:3])  # same sum, a filler
                    decl["log_counts"]["split-lifecycle"] = 5
                _, rows = self.pool(life, pers, decl)
                self.assertEqual(ok_ids(rows), [POOL_ID])
                reason = rows[POOL_ID]["reason"]
                self.assertNotIn("in all", reason)
                self.assertIn(SHARED_LINES[0] if what == "twice"
                              else SHARED_LINES[3], reason)
                self.assertIn("0 times" if what == "missing" else
                              "2 times", reason)

    def test_a_pooled_log_still_fails_its_other_checks(self):
        _, rows = self.pool((1, SHARED_LINES), (1, []))
        self.assertEqual(ok_ids(rows), [])
        with tempfile.TemporaryDirectory() as raw:
            root = self.tree(raw, **{"split-persistence":
                                     "own ... OK\nb ... FAILED\n"})
            checks = t.Checks()
            t.harvest(root, Path(raw) / "out", checks, self.DECL)
            rows = {c["id"]: c for c in checks.rows}
        self.assertEqual(ok_ids(rows), [POOL_ID])
        self.assertIn("split-persistence", rows[POOL_ID]["reason"])

    def test_a_missing_pooled_log_fails_the_group(self):
        _, _, rows = self.harvest(raw := tempfile.mkdtemp(),
                                  **{"split-persistence": None})
        self.addCleanup(__import__("shutil").rmtree, raw, True)
        self.assertEqual(ok_ids(rows), ["E1.logs.split-lifecycle+"
                                        "split-persistence",
                                        "E1.required-logs"])
        self.assertIn("no split-persistence log",
                      rows[POOL_ID]["reason"])

    def test_the_shared_lines_are_derived_from_the_scripts(self):
        group = t.POOLED_LOGS[0]
        with tempfile.TemporaryDirectory() as raw:
            root = self.tree(raw)
            self.assertEqual(t.shared_ok_lines(root, group), SHARED_LINES)
            # a changed script changes the lines expected
            script = root / "src/simp/tests/split-persistence" / \
                "splitChildScript.sml"
            script.write_text(shared_script(["something else"]))
            self.assertEqual(
                t.shared_ok_lines(root, group),
                SHARED_LINES[:1] + ["something else"] + SHARED_LINES[3:])

    def test_a_pool_whose_lines_cannot_be_derived_is_refused(self):
        base = "src/simp/tests/split-persistence/"
        for what, edit, message in (
                ("no script",
                 lambda r: (r / base / "splitChildScript.sml").unlink(),
                 "no script"),
                ("no string",
                 lambda r: (r / base / "splitChildScript.sml").write_text(
                     "val _ = 1\n(* tprint \"x\" *)\n"), "no tprint"),
                ("an escape",
                 lambda r: (r / base / "splitChildScript.sml").write_text(
                     'val _ = tprint "a\\n"\n'), "escape"),
                ("a repeat",
                 lambda r: (r / base / "splitChildScript.sml").write_text(
                     shared_script(SHARED_LINES[:1])), "twice")):
            with self.subTest(what), tempfile.TemporaryDirectory() as raw:
                root = self.tree(raw)
                edit(root)
                with self.assertRaisesRegex(t.Refusal, message):
                    t.harvest(root, Path(raw) / "out", t.Checks(),
                              self.DECL)

    def test_logs_outside_a_pool_are_judged_alone(self):
        # a changed count of a log not in the pool fails its own check
        decl = dict(log_counts=dict(self.DECL["log_counts"]))
        decl["log_counts"]["replay-order"] = 2
        with tempfile.TemporaryDirectory() as raw:
            root = self.tree(raw)
            checks = t.Checks()
            t.harvest(root, Path(raw) / "out", checks, decl)
            rows = {c["id"]: c for c in checks.rows}
        self.assertEqual(ok_ids(rows), [
            "E1.log.src/simp/src/.hol/logs/replay-order"])
        # and the pool does not need scripts when none of its logs is there
        self.assertEqual(
            [g["logs"] for g in t.POOLED_LOGS],
            [("split-lifecycle", "split-persistence")])

    def manifest(self, name="snapshots.json", exits=None, pins=None):
        """A fake TASK32 manifest of the two roots."""
        sides = {}
        for side in ("base", "cand"):
            sides[side] = dict(
                label=side, root=str(self.roots[side]),
                pin=(pins or {}).get(side, getattr(self, side)),
                tree="0" * 40, commands=[
                    dict(name="clone", exit=0),
                    dict(name="build", exit=(exits or {}).get(side, 0))])
        path = self.raw / name
        path.write_text(json.dumps(dict(schema=d.snap.SCHEMA,
                                        sides=sides)))
        return path

    def declared(self, paths=(DECLARED_PATH,), kinds=("val",), **flags):
        entries = []
        for p in paths:
            entries.append(dict(
                path=p, base_blob=git(self.repo, "rev-parse",
                                      "%s:%s" % (self.base, p)),
                cand_blob=git(self.repo, "rev-parse",
                              "%s:%s" % (self.cand, p)),
                mechanism="m", justification="j",
                allowed_kinds=list(kinds), type_change=False,
                new_root=False))
        data = dict(schema=t.DECLARED_SCHEMA, base=self.base,
                    cand=self.cand, l2=entries, allowlist=[], s2=S2,
                    e2c=E2C, log_counts=dict(COUNTS))
        data.update(flags)
        return data

    def run(self, declared=None, specs=SPECS):
        checks = t.Checks()
        declared = declared or self.declared()
        t.check_declaration(declared, checks)
        data = t.audit(self.repo, self.roots["base"], self.roots["cand"],
                       declared, checks, specs=specs)
        return {c["id"]: c for c in checks.rows}, data


def ok_ids(rows):
    return sorted(i for i, c in rows.items() if c["status"] == "fail")


SIG_PLUS = FILES[DECLARED_PATH] .replace(
    "end\n", ADDED_VAL + "end\n")


class AuditTest(unittest.TestCase):
    def world(self, **kw):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        return World(tmp.name, **kw)

    def test_declared_val_only_diff_passes(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["differing"], [DECLARED_PATH])
        self.assertEqual(data["r3"][DECLARED_PATH]["kinds"], ["val"])
        self.assertIn("ThmAttribute", data["closure"]["base"]["modules"])
        self.assertIn("listTheory", data["closure"]["base"]["modules"])

    def test_identical_trees_fail_the_declared_set(self):
        # declared but equal: a declaration of a difference that is not
        # there is not the closure's diff
        w = self.world()
        rows, _ = w.run(w.declared())
        self.assertEqual(ok_ids(rows), ["L2.diff-is-declared",
                                        "L2.modified-explained"])

    def test_undeclared_diff_fails(self):
        w = self.world(change={
            DECLARED_PATH: SIG_PLUS,
            "src/simp/src/Cond_rewr.sml": FILES[
                "src/simp/src/Cond_rewr.sml"] + "val x = 1\n"})
        rows, data = w.run()
        self.assertEqual(ok_ids(rows),
                         ["L2.diff-is-declared", "L2.modified-explained",
                          "R3.kinds-declared"])
        self.assertIn("undeclared: ['src/simp/src/Cond_rewr.sml']",
                      rows["L2.diff-is-declared"]["reason"])

    def test_diff_outside_the_closure_is_not_the_closure(self):
        w = self.world(change={
            DECLARED_PATH: SIG_PLUS, "src/other/Unrelated.sml": "val x=1\n"})
        rows, _ = w.run()
        self.assertEqual(ok_ids(rows), [])

    def test_stale_declared_blob_fails(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        declared = w.declared()
        declared["l2"][0]["cand_blob"] = "0" * 40
        rows, _ = w.run(declared)
        self.assertEqual(ok_ids(rows), ["L2.declared-blobs"])

    def test_new_top_level_ref_fails(self):
        w = self.world(change={
            "src/1/ThmAttribute.sml": FILES["src/1/ThmAttribute.sml"]
            .replace("struct\n", "struct\n  val cache = ref []\n"),
            DECLARED_PATH: SIG_PLUS})
        declared = w.declared(
            paths=(DECLARED_PATH, "src/1/ThmAttribute.sml"), kinds=("val",
                                                                    "fun"))
        rows, data = w.run(declared)
        self.assertEqual(ok_ids(rows), ["R2.no-new-root"])
        self.assertEqual(data["r2"]["src/1/ThmAttribute.sml"][0][0], "ref")

    def test_other_roots_fail(self):
        for text, name in (
                ("val t = Array.array (3, 0)\n", "Array"),
                ("val _ = Listener.add_listener l f\n",
                 "Listener.add_listener"),
                ("val _ = Theory.register_hook (n, f)\n", "register_hook"),
                ("val _ = ThmAttribute.register_attribute (n, a)\n",
                 "attribute-registration"),
                ("val w = Weak.weak NONE\n", "Weak")):
            with self.subTest(name):
                w = self.world(change={
                    "src/1/ThmAttribute.sml":
                    FILES["src/1/ThmAttribute.sml"].replace(
                        "struct\n", "struct\n  " + text)})
                rows, data = w.run(w.declared(
                    paths=("src/1/ThmAttribute.sml",), kinds=("val",)))
                self.assertIn("R2.no-new-root", ok_ids(rows))
                self.assertEqual(
                    data["r2"]["src/1/ThmAttribute.sml"][0][0], name)

    def test_comment_text_is_not_a_root(self):
        w = self.world(change={
            DECLARED_PATH: SIG_PLUS.replace(
                "  val is_attribute",
                "  (* a ref to the registry, an Array,\n"
                "     register_hook: only words *)\n  val is_attribute")})
        rows, _ = w.run()
        self.assertEqual(ok_ids(rows), [])

    def test_extension_name_in_closure_fails(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS},
                       new_modules={"splitLib": ("src/simp/src", [])},
                       extra_deps={"simpLib": ["splitLib"]})
        rows, _ = w.run()
        self.assertEqual(
            ok_ids(rows), ["L2.names-equal", "L2.no-extension.cand",
                           "L2.sources-tracked"])
        self.assertIn("splitLib", rows["L2.no-extension.cand"]["reason"])

    def test_extension_pattern_names_fail(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS},
                       new_modules={"fooExt": ("src/simp/src", [])},
                       extra_deps={"bossLib": ["fooExt"]})
        rows, _ = w.run()
        self.assertIn("L2.no-extension.cand", ok_ids(rows))

    def test_new_module_breaks_name_equality(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS},
                       new_modules={"Helper": ("src/simp/src", [])},
                       extra_deps={"simpLib": ["Helper"]})
        write(w.repo, {"src/simp/src/Helper.sml": "val x = 1\n"})
        rows, _ = w.run()
        self.assertIn("L2.names-equal", ok_ids(rows))

    def test_type_change_fails(self):
        for text in ("  datatype t = A | B\n", "  exception Boom of int\n",
                     "  type t = {a : int, b : bool}\n"):
            with self.subTest(text):
                w = self.world(change={
                    DECLARED_PATH: FILES[DECLARED_PATH].replace(
                        "end\n", ADDED_VAL + text + "end\n")})
                rows, data = w.run()
                self.assertEqual(ok_ids(rows), [
                    "R3.kinds-declared", "R3.no-type-change"])
                self.assertTrue(
                    data["r3"][DECLARED_PATH]["type_changes"])

    def test_changed_type_in_place_fails(self):
        # a datatype present on both sides and changed on one: base has
        # `datatype t = A`, the candidate `datatype t = A | B`
        base = FILES[DECLARED_PATH].replace("end\n",
                                            "  datatype t = A\nend\n")
        with tempfile.TemporaryDirectory() as raw:
            files = dict(FILES, **{DECLARED_PATH: base})
            with mock.patch.dict(FILES, files):
                w = World(raw, change={DECLARED_PATH: base.replace(
                    "= A\n", "= A | B\n")})
            rows, data = w.run(w.declared(kinds=("datatype", "val")))
        self.assertIn("R3.no-type-change", ok_ids(rows))
        self.assertEqual(data["r3"][DECLARED_PATH]["type_changes"],
                         ["datatype t = A", "datatype t = A | B"])

    def test_declaring_a_type_change_is_invalid(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        for flags in (dict(type_change=True), dict(new_root=True),
                      dict(allowed_kinds=["datatype"])):
            with self.subTest(flags):
                declared = w.declared()
                declared["l2"][0].update(flags)
                rows, _ = w.run(declared)
                self.assertIn("declared.valid", ok_ids(rows))

    def test_snapshot_not_matching_git_fails(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        (w.roots["cand"] / DECLARED_PATH).write_text("changed\n")
        rows, _ = w.run()
        self.assertIn("L2.snapshot-is-git", ok_ids(rows))

    def test_unresolved_module_fails(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS},
                       extra_deps={"simpLib": ["Missing"]})
        rows, _ = w.run()
        self.assertIn("L2.resolved.cand", ok_ids(rows))

    def test_dangling_or_escaping_link_is_refused(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        link = w.roots["cand"] / "sigobj" / "simpLib.uo"
        link.unlink()
        outside = w.raw / "outside.uo"
        outside.write_text("")
        link.symlink_to(outside)
        with self.assertRaises(t.Refusal):
            w.run()

    # ---- hol.state0: the UOARGS of src/proofman/Holmakefile are roots

    UOARGS = ("UOARGS = $(protect $(SIGOBJ)/ThmSetData) proofManagerLib \\\n"
              "\t $(protect $(SIGOBJ)/Gone)\n")
    STATE0 = dict(SPECS, **{"hol.state0": dict(
        dir="src/proofman", vars=("UOARGS",), extra=())})
    EXTRA_FILES = {
        "src/1/ThmSetData.sig": "signature ThmSetData =\nsig\nend\n",
        "src/1/ThmSetData.sml": "structure ThmSetData =\nstruct\nend\n",
        "src/proofman/proofManagerLib.sig":
            "signature proofManagerLib =\nsig\nend\n",
        "src/proofman/proofManagerLib.sml":
            "structure proofManagerLib =\nstruct\nend\n"}
    EXTRA_MODULES = {"ThmSetData": ("src/1", []),
                     "proofManagerLib": ("src/proofman", [])}

    def state0_world(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        with mock.patch.dict(FILES, self.EXTRA_FILES), \
                mock.patch.dict(MODULES, self.EXTRA_MODULES):
            w = World(tmp.name, change={DECLARED_PATH: SIG_PLUS})
        for root in w.roots.values():
            write(root, {"src/proofman/Holmakefile": self.UOARGS})
        return w

    def test_uoargs_are_roots_and_unresolved_ones_fail(self):
        w = self.state0_world()
        heaps = t.heap_deps(w.roots["base"], self.STATE0)
        self.assertEqual(heaps["hol.state0"],
                         ["Gone", "ThmSetData", "proofManagerLib"])
        rows, data = w.run(specs=self.STATE0)
        self.assertEqual(ok_ids(rows), ["L2.resolved.base",
                                        "L2.resolved.cand"])
        for side in ("base", "cand"):
            self.assertEqual(data["closure"][side]["unresolved"], ["Gone"])
            self.assertIn("proofManagerLib",
                          data["closure"][side]["modules"])
            self.assertIn("ThmSetData", data["closure"][side]["roots"])
        # a reviewed name compiled into bin/hol is no failure
        with mock.patch.object(t, "BASIS_ONLY", ("Gone",)):
            rows, data = w.run(specs=self.STATE0)
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["closure"]["cand"]["basis_only"], ["Gone"])

    def test_hol_state0_is_a_real_heap_spec(self):
        self.assertEqual(t.HEAP_SPECS["hol.state0"]["dir"], "src/proofman")
        self.assertEqual(t.HEAP_SPECS["hol.state0"]["vars"], ("UOARGS",))

    # ---- every modified tracked file is declared or allowlisted

    def allow(self, w, *paths):
        return [dict(path=p, base_blob=git(w.repo, "rev-parse", "%s:%s" % (
            w.base, p)), cand_blob=git(w.repo, "rev-parse", "%s:%s" % (
                w.cand, p)), justification="build file")
                for p in paths]

    HOLMAKE = "src/boss/Holmakefile"

    def test_modified_build_file_must_be_allowlisted(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS,
                               self.HOLMAKE: FILES[self.HOLMAKE] + "# x\n"})
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), ["L2.modified-explained"])
        self.assertIn(self.HOLMAKE, rows["L2.modified-explained"]["reason"])
        declared = w.declared()
        declared["allowlist"] = self.allow(w, self.HOLMAKE)
        rows, data = w.run(declared)
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["modified"]["allowlisted"], [self.HOLMAKE])

    def test_allowlist_entries_are_pinned_and_used(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS,
                               self.HOLMAKE: FILES[self.HOLMAKE] + "# x\n"})
        declared = w.declared()
        declared["allowlist"] = self.allow(w, self.HOLMAKE)
        declared["allowlist"][0]["cand_blob"] = "0" * 40
        self.assertEqual(ok_ids(w.run(declared)[0]),
                         ["L2.modified-explained"])
        # allowlisted but not modified
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        declared = w.declared()
        declared["allowlist"] = self.allow(w, "src/list/listScript.sml")
        self.assertEqual(ok_ids(w.run(declared)[0]),
                         ["L2.modified-explained"])

    def test_added_and_test_directory_files_need_no_entry(self):
        with mock.patch.dict(FILES, {"src/x/tests/t.sml": "a\n"}):
            w = self.world(change={
                DECLARED_PATH: SIG_PLUS, "src/x/tests/t.sml": "b\n",
                "src/new/New.sml": "val x = 1\n"})
        self.assertEqual(ok_ids(w.run()[0]), [])

    def test_declaration_overlap_with_allowlist_is_invalid(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        declared = w.declared()
        declared["allowlist"] = self.allow(w, DECLARED_PATH)
        self.assertIn("declared.valid", ok_ids(w.run(declared)[0]))

    def test_missing_tracked_closure_file_fails_not_skips(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        (w.roots["cand"] / "src/1/ThmAttribute.sml").unlink()
        rows, _ = w.run()
        self.assertEqual(ok_ids(rows), ["L2.snapshot-is-git"])
        self.assertIn("missing on disk",
                      rows["L2.snapshot-is-git"]["reason"])
        self.assertIn("cand:src/1/ThmAttribute.sml",
                      rows["L2.snapshot-is-git"]["reason"])

    # ---- nominal dependencies

    BOSS_UO = "src/boss/.hol/objs/bossLib.uo"

    def nominal_world(self, sides, listed=(), module="ThmAttribute"):
        """A world whose bossLib lists `src/z/<module>` (a directory
        with no object of it) on `sides`, and sigobj/<module> too when
        `listed`."""
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        for side in sides:
            f = w.roots[side] / self.BOSS_UO
            text = f.read_text()
            if listed:
                text += "$(HOLDIR)/sigobj/%s\n" % module
            f.write_text(text + "$(HOLDIR)/src/z/%s\n" % module)
        return w

    def test_nominal_dependency_must_also_be_listed_from_sigobj(self):
        rows, data = self.nominal_world(("base", "cand")).run()
        self.assertEqual(ok_ids(rows), ["L2.nominal"])
        self.assertIn("src/z/ThmAttribute", rows["L2.nominal"]["reason"])
        rows, data = self.nominal_world(("base", "cand"), listed=True).run()
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["closure"]["cand"]["nominal"],
                         {"bossLib": ["src/z/ThmAttribute"]})

    def test_nominal_dependencies_must_be_equal_on_both_sides(self):
        for side in ("base", "cand"):
            with self.subTest(side):
                rows, _ = self.nominal_world((side,), listed=True).run()
                self.assertEqual(ok_ids(rows), ["L2.nominal"])
                self.assertIn("differ", rows["L2.nominal"]["reason"])

    def test_nominal_overload_is_allowed_unlisted(self):
        extra = {"src/thm/Overlay.sml": "structure Overlay = struct end\n",
                 "src/thm/Overlay.sig": "signature Overlay = sig end\n"}
        with mock.patch.dict(FILES, extra), mock.patch.dict(
                MODULES, {"Overlay": ("src/thm", [])}):
            w = self.nominal_world(("base", "cand"), module="Overlay")
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["closure"]["base"]["nominal"],
                         {"bossLib": ["src/z/Overlay"]})

    # ---- an allowlisted Holmakefile does not change a heap

    def test_allowlisted_holmakefile_may_not_touch_heap_lines(self):
        base = FILES[self.HOLMAKE]
        edits = {
            "INCLUDES": base + "INCLUDES = ../x\n",
            "HOLHEAP": base + "HOLHEAP = $(HOLDIR)/x\n",
            "OPTIONS": base + "OPTIONS = QUIT_ON_FAILURE\n",
            "deps": base + "extra_DEPS += a.uo\n",
            "UOARGS": base + "UOARGS = a b\n",
            "deps use": base + "t: $(DEPS)\n",
            "buildheap": base.replace("-o $(T)", "-o $(U)")}
        for name, text in edits.items():
            with self.subTest(name):
                w = self.world(change={DECLARED_PATH: SIG_PLUS,
                                       self.HOLMAKE: text})
                declared = w.declared()
                declared["allowlist"] = self.allow(w, self.HOLMAKE)
                rows, data = w.run(declared)
                self.assertEqual(ok_ids(rows), ["L2.allowlist-build-safe"])
                self.assertTrue(data["allowlist_hazards"])
        # targets, comments and test targets are not hazards
        w = self.world(change={DECLARED_PATH: SIG_PLUS, self.HOLMAKE:
                               base + "all: y\n# INCLUDES = z\n"})
        declared = w.declared()
        declared["allowlist"] = self.allow(w, self.HOLMAKE)
        rows, data = w.run(declared)
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["allowlist_hazards"], [])

    def test_hazard_lines_join_continuations(self):
        before = "boss_deps = a \\\n b\nall: x\n"
        self.assertEqual(t.hazard_changes(before, before), [])
        self.assertEqual(
            t.hazard_changes(before, before.replace(" b", " c")),
            ["boss_deps = a b", "boss_deps = a c"])

    # ---- the buildheap recipe line gives the extra roots

    def test_recipe_names_from_the_buildheap_line(self):
        line = "\t$(protect $(HOLDIR)/bin/hol) buildheap $(DEBUG_FLAG) " \
            "-o $(TARGET) -b $(HOLHEAP) $(boss_deps) bossLib holTheory\n"
        names = t.recipe_names("boss_deps = a\nall: x\n" + line,
                               ("boss_deps",), "h")
        self.assertEqual(names, ["bossLib", "holTheory"])
        names = t.recipe_names(
            line.replace("holTheory", "$(protect $(SIGOBJ)/Z) \\\n  Y"),
            ("boss_deps",), "h")
        self.assertEqual(names, ["bossLib", "Z", "Y"])
        for what, text in (
                ("no line", "boss_deps = a\n"),
                ("two lines", line + line),
                ("not a recipe", line.lstrip()),
                ("unknown variable", line.replace("bossLib", "$(more)")),
                ("unknown option", line.replace("-o", "--odd")),
                ("variable unused", line.replace("$(boss_deps)", "")),
                ("dangling option", line.rstrip() + " -o\n")):
            with self.subTest(what), self.assertRaises(t.Refusal):
                t.recipe_names(text, ("boss_deps",), "h")

    def test_a_name_added_to_the_recipe_line_is_a_root(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        for root in w.roots.values():
            f = root / "src/boss/Holmakefile"
            f.write_text(f.read_text().replace("bossLib\n",
                                               "bossLib Elsewhere\n"))
        self.assertIn("Elsewhere",
                      t.heap_deps(w.roots["cand"], SPECS)["hol.state"])
        rows, _ = w.run()
        self.assertEqual(ok_ids(rows), ["L2.resolved.base",
                                        "L2.resolved.cand"])

    def test_real_heap_spec_reads_the_recipe(self):
        self.assertTrue(t.HEAP_SPECS["hol.state"]["recipe"])
        self.assertNotIn("extra", t.HEAP_SPECS["hol.state"])

    # ---- sources: per line, and what is generated

    def test_every_source_line_must_be_tracked(self):
        # Half.sml is tracked, Half.sig is not: the module was tracked
        # before this was per line
        with mock.patch.dict(FILES, {"src/simp/src/Half.sml": "val x=1\n"}):
            w = self.world(change={DECLARED_PATH: SIG_PLUS})
        for root in w.roots.values():
            write_uo(root, {"Half": ("src/simp/src", [])},
                     {"simpLib": ["Half"]})
            write_uo(root, {"simpLib": ("src/simp/src",
                                        ["Cond_rewr", "Half"])})
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), ["L2.sources-tracked"])
        self.assertIn("Half: src/simp/src/Half.sig",
                      data["no_tracked_source"])

    def test_generated_table_has_the_reviewed_entries(self):
        self.assertEqual(t.GENERATED["sigobj/Systeml.sig"],
                         ("tools/Holmake/Systeml.sig",))
        self.assertEqual(
            sorted(t.GENERATED["src/portableML/poly/SHA1_ML.sml"]),
            ["src/portableML/poly/SHA1-byexec.ML",
             "src/portableML/poly/w64-SHA1.ML"])
        for rel in ("sigobj/Systeml.sml", "src/thm/Thm.sml",
                    "src/thm/Thm-sig.sml"):
            self.assertIn(rel, t.GENERATED)

    SYSTEML = {
        "tools/Holmake/Systeml.sig": "signature Systeml = sig end\n",
        "tools/Holmake/unix-systeml.sml": "structure Systeml = struct end\n",
        "tools-poly/Holmake/unix-systeml.sml":
            "structure Systeml = struct end\n"}

    def systeml_world(self, drop=None):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        files = {k: v for k, v in self.SYSTEML.items() if k != drop}
        with mock.patch.dict(FILES, files), mock.patch.dict(
                MODULES, {"Systeml": ("sigobj", []),
                          "simpLib": ("src/simp/src",
                                      ["Cond_rewr", "Systeml"])}):
            w = World(tmp.name, change={DECLARED_PATH: SIG_PLUS})
        for root in w.roots.values():
            write(root, {
                "sigobj/Systeml.sig":
                    self.SYSTEML["tools/Holmake/Systeml.sig"],
                "sigobj/Systeml.sml": 'val HOLDIR = "%s"\n' % root})
        return w

    def test_systeml_is_a_generated_source_made_from_tracked_files(self):
        w = self.systeml_world()
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), [])
        self.assertIn("sigobj/Systeml.sml", data["generated"]["root_masked"])
        # a missing input of a GENERATED line leaves it untracked
        w = self.systeml_world(drop="tools-poly/Holmake/unix-systeml.sml")
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), ["L2.sources-tracked"])
        self.assertIn("Systeml: sigobj/Systeml.sml",
                      data["no_tracked_source"])

    def test_generated_copy_must_equal_a_tracked_input(self):
        w = self.systeml_world()
        (w.roots["cand"] / "sigobj/Systeml.sig").write_text("other\n")
        rows, _ = w.run()
        self.assertEqual(ok_ids(rows), ["L2.generated-copies",
                                        "L2.generated-products"])
        self.assertIn("cand:sigobj/Systeml.sig",
                      rows["L2.generated-copies"]["reason"])

    # ---- generated products compare byte for byte

    def test_products_are_compared_and_listed(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["generated"]["products"], 3)
        self.assertEqual(data["generated"]["differing"], [])

    def test_a_differing_theory_product_fails(self):
        for name in ("listTheory.dat", "listTheory.sml", "listTheory.sig"):
            with self.subTest(name):
                w = self.world(change={DECLARED_PATH: SIG_PLUS})
                w.write_products(w.roots["cand"], **{name: "changed\n"})
                rows, data = w.run()
                self.assertEqual(ok_ids(rows), ["L2.generated-products"])
                self.assertEqual(
                    [x[1] for x in data["generated"]["differing"]],
                    ["differs"])

    def test_a_missing_product_fails(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        (w.roots["base"] / "src/list/.hol/objs/listTheory.dat").unlink()
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), ["L2.generated-products"])
        self.assertEqual(data["generated"]["differing"][0][1],
                         "missing on base")

    def test_root_dependent_products_compare_after_masking(self):
        w = self.world(change={DECLARED_PATH: SIG_PLUS})
        for root in w.roots.values():
            w.write_products(root, **{
                "listTheory.sml": 'val here = "$ROOT/src/list"\n'})
        rows, data = w.run()
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(data["generated"]["root_masked"],
                         ["src/list/listTheory.sml"])
        # any other difference still fails
        w.write_products(w.roots["cand"], **{
            "listTheory.sml": 'val here = "$ROOT/src/lisp"\n'})
        self.assertEqual(ok_ids(w.run()[0]), ["L2.generated-products"])

    # ---- R2 on the whole list, and provenance

    def test_new_roots_of_every_kind_fail(self):
        lines = {
            "Array": ["val a = Word8Array.array (3, 0w0)",
                      "val a = CharArray.array (3, #\"a\")"],
            "assignment": ["val _ = (cnt := 1)"],
            "thread-or-lock": ["val m = Mutex.mutex ()",
                               "val _ = Thread.fork (f, [])",
                               "val c = ConditionVar.conditionVar ()",
                               "val _ = Synchronized.var \"x\" 0"],
            "context-data": ["val s = Context.Data.new {name=\"a\"}",
                             "val _ = Context.Data.put s v ctxt",
                             "val _ = Context.Data.write s v",
                             "val _ = Context.Data.modify s f",
                             "val c = Context.Data.update s f c"],
            "thmsetdata-registration": [
                "val x = ThmSetData.new_exporter r",
                "val x = ThmSetData.export_with_ancestry r",
                "val x = ThmSetData.export_simple_dictionary r",
                "val x = ThmSetData.export_alist r",
                "val x = ThmSetData.export_list r"],
            "register_hook": ["val _ = Theory.register_onload f"],
            "ancestry-data": ["val x = AncestryData.make r",
                              "val x = AncestryData.fullmake r"],
            "attribute-registration": ["val _ = define_abbreviation a"],
            "cache": ["val (c, r) = Cache.CACHE cap f",
                      "val (c, r) = Cache.RCACHE (rel, cap) f",
                      "val c = CACHE cap f"],
            "memoize": ["val f = mlibUseful.memoize (fn () => 1)"],
            "Susp.delay": ["val s = Susp.delay (fn () => 1)"],
            "grammar-write": [
                "val _ = Parse.overload_on (\"x\", t)",
                "val _ = temp_overload_on (\"x\", t)",
                "val _ = Parse.inferior_overload_on (\"x\", t)",
                "val _ = set_fixity \"x\" (Infixl 500)",
                "val _ = Parse.temp_set_fixity \"x\" f",
                "val _ = add_rule {term_name = \"x\"}",
                "val _ = temp_add_rule r",
                "val _ = add_infix (\"x\", 1, LEFT)",
                "val _ = Parse.temp_add_infix x",
                "val _ = add_listform l",
                "val _ = add_numeral_form (#\"n\", NONE)",
                "val _ = temp_set_grammars (tyg, tmg)",
                "val _ = add_record_field (\"x\", t)",
                "val _ = add_user_printer (\"x\", t)",
                "val _ = Parse.type_abbrev (\"x\", ty)",
                "val _ = clear_overloads_on \"x\"",
                "val _ = remove_ovl_mapping \"x\" r"],
            "trace-registration": [
                "val _ = Feedback.register_trace (n, r, 1)",
                "val _ = Feedback.register_ftrace (n, f, 1)",
                "val _ = Feedback.register_btrace (n, r)"]}
        for name, texts in lines.items():
            for text in texts:
                with self.subTest(text):
                    self.assertEqual(
                        [n for n, _ in t.scan_roots([text])], [name])
        # words that merely contain the names are no pattern
        self.assertEqual(t.scan_roots([
            "val x = CACHED_ARITH c", "val overload_only = 1",
            "val x = Cache.new_cache_name", "val y = memoized"]), [])
        # the names that do not exist in the tree are not patterns
        self.assertEqual(t.scan_roots(["val x = register_settype y"]), [])

    def test_provenance_binds_roots_pins_and_build(self):
        w = self.world()
        declared = w.declared()
        roots = dict(base=w.roots["base"], cand=w.roots["cand"])

        def check(**kw):
            checks = t.Checks()
            roots_ = kw.pop("roots", roots)
            decl = kw.pop("declared", declared)
            t.check_provenance(w.manifest(**kw), roots_, decl, checks)
            return {c["id"]: c for c in checks.rows}
        self.assertEqual(ok_ids(check()), [])
        # another root of the same side
        other = dict(roots, cand=w.roots["base"])
        self.assertEqual(ok_ids(check(roots=other)), ["manifest.roots"])
        # pins of the declaration that are not the manifest's
        self.assertEqual(ok_ids(check(pins=dict(cand=w.base))),
                         ["manifest.pins"])
        # a failed build command of the candidate
        rows = check(exits=dict(cand=2))
        self.assertEqual(ok_ids(rows), ["manifest.build"])
        self.assertIn("cand: failed build", rows["manifest.build"]["reason"])
        # a malformed manifest is refused
        bad = w.raw / "bad.json"
        bad.write_text(json.dumps(dict(schema="x")))
        with self.assertRaises(t.Refusal):
            t.check_provenance(bad, roots, declared, t.Checks())

    def test_audit_requires_the_manifest_and_binds_it(self):
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(
                io.StringIO()):
            t.build_parser().parse_args(
                ["audit", "--base-root", "b", "--cand-root", "c",
                 "--out", "o"])
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(
                io.StringIO()):
            t.build_parser().parse_args(
                ["harvest", "--cand-root", "c", "--out", "o"])

    def test_heap_deps_from_the_holmakefile(self):
        w = self.world()
        self.assertEqual(t.heap_deps(w.roots["base"], SPECS),
                         {"hol.state": ["bossLib", "listTheory"]})
        bad = dict(SPECS, x=dict(dir="src/boss", vars=("NOPE",), extra=()))
        with self.assertRaises(t.Refusal):
            t.heap_deps(w.roots["base"], bad)


class TextTest(unittest.TestCase):
    def test_strip_comments(self):
        text = "a (* x (* ref *) y *) b \"(* ref\" c\n(* ref\n*) d"
        out = t.strip_comments(text)
        self.assertNotIn("ref *", out)
        self.assertEqual(out.count("ref"), 1)  # the string's
        self.assertEqual(out.count("\n"), text.count("\n"))

    def test_chunks_and_kinds(self):
        kinds, types = t.classify(
            "fun f x = x\nval y = 1\n", "fun f x = x\nval y = 2\nfun g = 1\n")
        self.assertEqual(kinds, ["fun", "val"])
        self.assertEqual(types, [])
        kinds, types = t.classify("datatype t = A\n", "datatype t = A | B\n")
        self.assertEqual(types, ["datatype t = A", "datatype t = A | B"])

    def test_abstype_is_a_type_kind(self):
        self.assertIn("abstype", t.TYPE_KINDS)
        kinds, types = t.classify(
            "abstype t = A with val x = 1 end\n",
            "abstype t = A | B with val x = 1 end\n")
        self.assertEqual(kinds, ["abstype"])
        self.assertEqual(len(types), 2)

    def test_closing_end_belongs_to_no_chunk(self):
        before = "signature S =\nsig\n  datatype t = A\nend\n"
        after = "signature S =\nsig\n  datatype t = A\n" \
                "  val x : int\nend\n"
        kinds, types = t.classify(before, after)
        self.assertEqual((kinds, types), (["val"], []))
        # an indented `end` (of a let) still belongs to its declaration
        kinds, types = t.classify("val x = let val y = 1 in y\n  end\n",
                                  "val x = let val y = 2 in y\n  end\n")
        self.assertEqual(kinds, ["val"])
        self.assertEqual(t.chunks("structure S =\nstruct\nval x = 1\nend\n")
                         [-1], ("val", "val x = 1"))

    def test_deps_by_directory_are_resolved_by_directory(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "sigobj").mkdir()
            uo = root / "sigobj/A.uo"
            uo.write_text("$(HOLDIR)/sigobj/B\n$(HOLDIR)/src/x/B\n"
                          "$(HOLDIR)/src/x/A\n$(HOLDIR)/src/x/A.sml\n")
            names, local, sources = t.read_deps(uo, root)
            self.assertEqual((names, local, sources), (
                ["B"], ["src/x/B", "src/x/A"], ["src/x/A.sml"]))
            # B built in src/y is the sigobj module B; B built in src/x is
            # a private module of src/x, followed in place (its own list
            # names C and a source)
            for d_, text in (("src/y", ""), ("src/x",
                                             "$(HOLDIR)/sigobj/C\n"
                                             "$(HOLDIR)/src/x/B.sml\n")):
                objs = root / d_ / ".hol/objs"
                objs.mkdir(parents=True)
                (objs / "B.uo").write_text(text)
            (root / "sigobj/B.uo").symlink_to(root / "src/y/.hol/objs/B.uo")
            self.assertEqual(t.local_deps(root, "src/y/B", set()),
                             (["B"], []))
            self.assertEqual(t.local_deps(root, "src/x/B", set()),
                             (["C"], ["src/x/B.sml"]))
            # no object in the directory: the line names the sigobj module
            nominal = []
            self.assertEqual(t.local_deps(root, "src/z/C", set(), nominal),
                             (["C"], []))
            self.assertEqual(nominal, [("src/z/C", False)])
            # a line that names C from sigobj too is a listed one
            nominal = []
            t.local_deps(root, "src/z/C", set(), nominal, {"C"})
            self.assertEqual(nominal, [("src/z/C", True)])

    def test_refs_are_words(self):
        self.assertEqual(t.scan_roots(["val refs = 1", "val prefix = 2"]),
                         [])
        self.assertEqual(t.scan_roots(["val x = ref 0"])[0][0], "ref")
        self.assertEqual(t.scan_roots(["x : int ref"])[0][0], "ref")


class ReportTest(unittest.TestCase):
    def test_seal_file_and_no_overwrite(self):
        with tempfile.TemporaryDirectory() as raw:
            checks = t.Checks()
            checks.add("x", "L1", "pass")
            report, path, seal = t.write_report(raw, "audit", checks, {}, {})
            self.assertEqual(path, Path(raw) / "audit.json")
            self.assertEqual(a.seal(path), seal)
            self.assertEqual(json.loads(
                Path(str(path) + ".seal").read_text()), seal)
            self.assertEqual(report["exit"], 0)
            with self.assertRaises(FileExistsError):
                t.write_report(raw, "audit", checks, {}, {})
            checks.add("y", "L1", "fail", "why")
            report, path, _ = t.write_report(
                Path(raw) / "b.json", "audit", checks, {}, {})
            self.assertEqual((report["success"], report["exit"]),
                             (False, t.FAIL))

    def test_every_report_carries_checkable_code(self):
        with tempfile.TemporaryDirectory() as raw:
            checks = t.Checks()
            report, _, _ = t.write_report(raw, "audit", checks, {}, {})
        self.assertEqual(sorted(report["code"]), sorted(t.CODE))
        for name in ("task33_offline.py", "task33_declared.json",
                     "task32_downstream.py", "acceptance.py"):
            self.assertIn(name, report["code"])
        t.check_code(report["code"])
        changed = dict(report["code"])
        changed["task33_offline.py"] = dict(sha256="0" * 64, bytes=1)
        with self.assertRaises(t.Refusal):
            t.check_code(changed)
        with self.assertRaises(t.Refusal):
            t.check_code({"task33_offline.py": changed["task33_offline.py"]})
        # a seal that TASK32's history names is accepted, as TASK32 does
        name = "task32_downstream.py"
        old = dict(report["code"])
        old[name] = dict(sha256="1" * 64, bytes=1)
        with mock.patch.dict(d.HISTORY, {name: [old[name]]}):
            t.check_code(old)

    def test_exit_codes_pass_inconclusive_fail(self):
        for rows, code in (([("a", "pass")], 0), ([("a", "skipped")], 2),
                           ([("a", "skipped"), ("b", "fail")], 3)):
            checks = t.Checks()
            for ident, status in rows:
                checks.add(ident, "L1", status)
            self.assertEqual(t.exit_of(checks), code)

    def test_report_that_cannot_be_written_exits_3_without_traceback(self):
        with tempfile.TemporaryDirectory() as raw:
            tree = HarvestTest().tree(raw)
            out = Path(raw) / "out"
            out.mkdir()
            (out / "harvest.json").write_text("old")
            argv = ["harvest", "--cand-root", str(tree), "--manifest",
                    str(Path(raw) / "m.json"), "--out", str(out)]
            (Path(raw) / "m.json").write_text("{}")
            err = io.StringIO()
            with contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(err):
                code = t.main(argv)
            self.assertEqual(code, 3)
            self.assertIn("cannot write the report", err.getvalue())
            self.assertNotIn("Traceback", err.getvalue())
            self.assertEqual((out / "harvest.json").read_text(), "old")

    def test_harvest_main_is_bound_to_the_manifest(self):
        with tempfile.TemporaryDirectory() as raw:
            raw = Path(raw)
            tree = HarvestTest().tree(raw)
            decl = t.load_declared()
            # the committed pins and counts of this tree's logs
            dpath = raw / "declared.json"
            dpath.write_text(json.dumps(dict(
                decl, log_counts=HarvestTest.DECL["log_counts"],
                log_skips={})))
            roots = {s: raw / s for s in ("base", "cand")}
            roots["cand"] = tree
            roots["base"].mkdir()
            sides = {s: dict(label=s, root=str(roots[s]), pin=decl[s],
                             tree="0" * 40, commands=[
                                 dict(name="build", exit=0)])
                     for s in roots}
            manifest = raw / "m.json"
            manifest.write_text(json.dumps(dict(schema=d.snap.SCHEMA,
                                                sides=sides)))
            argv = ["harvest", "--cand-root", str(tree), "--manifest",
                    str(manifest), "--declared", str(dpath)]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(t.main(argv + ["--out", str(raw / "o1")]),
                                 0)
                report = json.loads((raw / "o1/harvest.json").read_text())
                self.assertEqual(report["inputs"]["manifest"]["seal"],
                                 a.seal(manifest))
                ids = {c["id"]: c["status"] for c in report["checks"]}
                self.assertEqual(ids["manifest.build"], "pass")
                # a failed candidate build exit fails the harvest
                sides["cand"]["commands"][0]["exit"] = 1
                manifest.write_text(json.dumps(dict(schema=d.snap.SCHEMA,
                                                    sides=sides)))
                self.assertEqual(t.main(argv + ["--out", str(raw / "o2")]),
                                 3)

    def test_usage_errors_exit_3_not_2(self):
        for argv in ([], ["nosuchcommand"], ["audit"], ["harvest", "--x"],
                     ["archive", "--out", "o"]):
            with self.subTest(argv):
                err = io.StringIO()
                with self.assertRaises(SystemExit) as caught, \
                        contextlib.redirect_stderr(err):
                    t.build_parser().parse_args(argv)
                self.assertEqual(caught.exception.code, 3)
                self.assertIn("usage:", err.getvalue())
                self.assertIn("error:", err.getvalue())
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as caught:
                t.main(["audit"])
        self.assertEqual(caught.exception.code, 3)

    def test_any_exception_is_a_refusal_not_a_traceback(self):
        with tempfile.TemporaryDirectory() as raw:
            raw = Path(raw)
            tree = HarvestTest().tree(raw)
            decl = t.load_declared()
            sides = {s: dict(label=s, root=str(raw / s), pin=decl[s],
                             tree="0" * 40, commands=["build"])
                     for s in ("base", "cand")}  # strings, not records
            sides["cand"]["root"] = str(tree)
            manifest = raw / "m.json"
            manifest.write_text(json.dumps(dict(schema=d.snap.SCHEMA,
                                                sides=sides)))
            out = io.StringIO()
            err = io.StringIO()
            with contextlib.redirect_stdout(out), \
                    contextlib.redirect_stderr(err):
                code = t.main(["harvest", "--cand-root", str(tree),
                               "--manifest", str(manifest), "--out",
                               str(raw / "o")])
            self.assertEqual(code, 3)
            self.assertEqual(err.getvalue(), "")
            report = json.loads((raw / "o/harvest.json").read_text())
            self.assertEqual(report["checks"][-1]["id"], "refused")
            self.assertIn("AttributeError",
                          report["checks"][-1]["reason"])
            self.assertEqual(report["exit"], 3)

    def test_main_exit_codes_on_the_audit(self):
        with tempfile.TemporaryDirectory() as raw:
            w = World(raw, change={DECLARED_PATH: SIG_PLUS})
            decl = Path(raw) / "decl.json"
            decl.write_text(json.dumps(w.declared()))
            argv = ["audit", "--base-root", str(w.roots["base"]),
                    "--cand-root", str(w.roots["cand"]), "--repo",
                    str(w.repo), "--declared", str(decl), "--manifest",
                    str(w.manifest())]
            # the fake tree has no real heap Holmakefiles: refused (3)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = t.main(argv + ["--out", str(Path(raw) / "o.json")])
            self.assertEqual(code, 3)
            self.assertIn("FAIL", out.getvalue())
            report = json.loads((Path(raw) / "o.json").read_text())
            self.assertEqual(report["checks"][-1]["id"], "refused")
            self.assertEqual(
                [c["status"] for c in report["checks"]
                 if c["id"].startswith("manifest.")], ["pass"] * 3)


class LogTest(unittest.TestCase):
    def judge(self, name, text):
        return t.judge_log("src/simp/src/.hol/logs/" + name, text)

    def test_tprint_suite(self):
        good = "a ...   OK\nb ...  (0.0s)      OK\n" \
               "Cond_rewrExt focused checks: 2\n"
        self.assertTrue(self.judge("cond-rewr-ext", good)[0])
        self.assertFalse(self.judge("cond-rewr-ext",
                                    good + "c ...   FAILED\n")[0])
        self.assertFalse(self.judge("cond-rewr-ext", "a ...   OK\n")[0])
        self.assertFalse(self.judge("cond-rewr-ext", "")[0])
        self.assertFalse(self.judge(
            "cond-rewr-ext", good.replace("checks: 2", "checks: 0"))[0])

    def test_obs_suite(self):
        good = "x ...  OK\nOBS result=pass\n"
        self.assertTrue(self.judge("split-persistence", good)[0])
        self.assertFalse(self.judge(
            "split-persistence", good + "OBS result=fail\n")[0])
        self.assertFalse(self.judge("split-persistence", "x ... OK\n")[0])
        self.assertTrue(self.judge(
            "exclusion-contracts",
            good + "OBS setup.result=ready\nOBS assertion.result=pass\n")[0])

    def test_marker_python_suites(self):
        ok = "....\n---\nRan 4 tests in 0.1s\n\nOK\n"
        for name in ("fragments-python-tests",
                     "compiled-core-python-tests",
                     "interfaces-design-check"):
            self.assertTrue(self.judge(name, ok)[0], name)
            for bad in (ok.replace("Ran 4", "Ran 0"),
                        ok.replace("OK", "FAILED (errors=1)"),
                        ok.replace("OK", "FAILED (failures=1)"),
                        ok.replace("\nOK\n", "\n")):
                self.assertFalse(self.judge(name, bad)[0], name + bad)

    def test_unittest_and_audit(self):
        ok = "....\n---\nRan 4 tests in 0.1s\n\nOK\n"
        self.assertTrue(self.judge("ordinary-tactics", ok)[0])
        self.assertFalse(self.judge(
            "ordinary-tactics", ok.replace("OK", "FAILED (failures=1)"))[0])
        self.assertFalse(self.judge("ordinary-tactics", "cmd\n")[0])
        audit = "".join("%s/attribute/%s: PASS\n" % (s, w) for s in
                        ("simp-first", "cong-first") for w in
                        ("before", "after")) * 2 + "Receipt: /x\n"
        self.assertTrue(self.judge("api-audit", audit)[0])
        self.assertFalse(self.judge("api-audit", audit.replace(
            "cong-first/attribute/after: PASS", "cong-first/attribute/"
            "after: FAIL"))[0])
        self.assertFalse(self.judge("api-audit", "x: PASS\n")[0])

    ESC = "\x1b"
    # what testutils prints for a failed test: the test name, the
    # backspaced timing, then ESC[31m ESC[1m ESC[2C FAILED! ESC[0m
    FAILED = "t ...     \x08\x08(0.000s)      " + ESC + "[31m" + ESC + \
        "[1m" + ESC + "[2CFAILED!" + ESC + "[0m\n"

    def test_real_testutils_failure_is_a_failure(self):
        ok = "a ...   \x08\x08(0.0s)    OK\n"
        self.assertTrue(self.judge("native-extension", ok)[0])
        for name, text in (
                ("native-extension", ok + self.FAILED + ok),
                ("native-extension", ok + "Failure count = 2\n" + ok),
                ("cond-rewr-ext", ok + self.FAILED +
                 "Cond_rewrExt focused checks: 3\n"),
                ("split-persistence", ok + self.FAILED +
                 "OBS result=pass\n"),
                ("native-extension", ok + "Exception- Fail \"x\" raised\n"),
                ("native-extension", ok + "Static Errors\n" + ok),
                ("split-lifecycle", ok + "OBS result=pass\nOBS repair=fail\n"),
                ("native-extension", ok + "OBS result=fail\n" + ok)):
            with self.subTest(name, text=text[-40:]):
                passed, reasons, _ = self.judge(name, text)
                self.assertFalse(passed, reasons)
        self.assertIn("failure text: FAILED!",
                      self.judge("native-extension", self.FAILED + ok)[1])
        # a count of zero is no failure
        self.assertTrue(self.judge("native-extension",
                                   ok + "Failure count = 0\n" + ok)[0])

    def test_truncated_logs_do_not_pass(self):
        ok = "a ... OK\n"
        for name, text in (
                ("native-extension", ok + "b ...    "),
                ("native-extension", ok + "b ... \x08\x08(0.0s)"),
                ("split-persistence", "a ... OK\nb ...\nOBS result=pass\n"),
                ("ordinary-tactics", "Ran 4 tests in 0.1s\n\n"),
                ("cond-rewr-ext", ok + "b ...   \n")):
            with self.subTest(name, text=text):
                self.assertFalse(self.judge(name, text)[0])
        # a single OK line followed by a cut-off test is not a pass; the
        # same log completed is
        self.assertTrue(self.judge("native-extension", ok + "b ... OK\n")[0])

    def test_path_rules_for_the_recipe_suites_and_src1(self):
        cases = {"src/integer": "INTEGER_RECIPE_CHECKS=3",
                 "src/real": "REAL_RECIPE_CHECKS=3",
                 "src/list/src": "LIST_TRACKED_RECIPE_CHECKS=3",
                 "src/num/arith/src": "NUMERAL_RECIPE_CHECKS=3",
                 "src/pred_set/src": "PRED_SET_TRACKED_RECIPE_CHECKS=3"}
        for directory, line in cases.items():
            path = directory + "/.hol/logs/tracked-recipes"
            with self.subTest(directory):
                self.assertTrue(t.judge_log(path, "a ... OK\n" + line +
                                            "\n")[0])
                # the line of another directory's suite is no completion
                other = next(v for k, v in cases.items() if k != directory)
                self.assertFalse(t.judge_log(path, "a ... OK\n" + other +
                                             "\n")[0])
                self.assertFalse(t.judge_log(path, "a ... OK\n")[0])
                self.assertFalse(t.judge_log(
                    path, "a ... OK\n" + line.replace("=3", "=0"))[0])
        selftest = "src/1/.hol/logs/selftest.log"
        self.assertTrue(t.judge_log(
            selftest, "x ...   \x08\x08(0.000s)      OK\n")[0])
        self.assertFalse(t.judge_log(selftest, "x ... OK\ny ...  ")[0])
        self.assertFalse(t.judge_log(selftest, "x ... OK\n" + self.FAILED)[0])

    def test_unknown_log_has_no_criterion(self):
        passed, reasons, _ = self.judge("mystery", "all fine\n")
        self.assertFalse(passed)
        self.assertIn("no pass criterion", reasons[0])


class HarvestTest(unittest.TestCase):
    GOOD = {
        "api-audit": "".join("%s: PASS\n" % x for x in (
            "s/a/before", "s/a/after", "s/e/before", "s/e/after",
            "c/a/before", "c/a/after", "c/e/before", "c/e/after")) +
        "Receipt: /x\n",
        "cond-rewr-ext": "a ... OK\nCond_rewrExt focused checks: 1\n",
        "congruence-ext": "a ... OK\nCongruence extension focused "
                          "checks: 1\n",
        "simp-ext": "a ... OK\nTraverseExt lifetime checks: 1\n",
        "traverse-ext": "a ... OK\nTraverseExt focused checks: 1\n",
        "split-lifecycle": pooled_log(1, SHARED_LINES),
        "split-persistence": pooled_log(1, []),
        "split-registration": "a ... OK\n",
        "native-extension": "a ... OK\n",
        "fresh-load-regressions": "a ... OK\nOBS result=pass\n",
        "standard-recipes": "a ... OK\nSTANDARD_RECIPE_CHECKS=1\n",
        "replay-order": "a ... OK\n",
        "exclusion-contracts": "a ... OK\nOBS assertion.result=pass\n",
        "legacy-contracts": "Ran 1 tests in 1s\n\nOK\nOriginalScope: 1 "
                            "checks\n",
        "simp-marker-tests": "a ... OK\n",
        "simp-selftest.log": "a ... OK\n",
        "traversal-contracts": "a ... OK\n",
        "literal-exclusions": "Ran 1 tests in 1s\n\nOK\n",
        "ordinary-tactics": "Ran 1 tests in 1s\n\nOK\n",
        "fragments-python-tests": "Ran 1 tests in 1s\n\nOK\n",
        "compiled-core-python-tests": "Ran 1 tests in 1s\n\nOK\n",
        "interfaces-design-check": "Ran 1 tests in 1s\n\nOK\n",
        "compiled-core": "x/manifest.json\n",
        "fragment-contracts": "x/manifest.json\n",
    }
    DECL = dict(log_counts=dict(COUNTS, **{"split-lifecycle": 5,
                                           "split-persistence": 1}))

    RECIPES = {"src/integer": "INTEGER_RECIPE_CHECKS=1",
               "src/real": "REAL_RECIPE_CHECKS=1",
               "src/list/src": "LIST_TRACKED_RECIPE_CHECKS=1",
               "src/num/arith/src": "NUMERAL_RECIPE_CHECKS=1",
               "src/pred_set/src": "PRED_SET_TRACKED_RECIPE_CHECKS=1"}

    def tree(self, raw, **override):
        root = Path(raw) / "cand"
        logs = {**self.GOOD, **override}
        for script, lines in SHARED_SCRIPTS.items():
            f = root / script
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(shared_script(lines))
        for name, text in logs.items():
            if text is None:
                continue
            f = root / "src/simp/src/.hol/logs" / name
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(text)
        boss = root / "src/boss/.hol/logs"
        boss.mkdir(parents=True)
        (boss / "tracked-defaults").write_text(
            "a ... OK\nTRACKED_DEFAULTS_COMPLETE checks=3\n")
        (boss / "boss-selftest.log").write_text("a ... OK\n")
        for directory, line in self.RECIPES.items():
            f = root / directory / ".hol/logs/tracked-recipes"
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("a ... OK\n" + line + "\n")
        f = root / "src/1/.hol/logs/selftest.log"
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text("a ...   \x08\x08(0.0s)    OK\n")
        full = root / "src/simp/tests/native-extension/.hol/logs"
        full.mkdir(parents=True)
        (full / "check-full").write_text(
            "a ... OK\nNative coverage: 3 original + 1 registry checks\n")
        return root

    def harvest(self, raw, **override):
        root = self.tree(raw, **override)
        checks = t.Checks()
        out = Path(raw) / "out"
        data = t.harvest(root, out, checks, self.DECL)
        return out, data, {c["id"]: c for c in checks.rows}

    def test_passing_logs_are_copied_sealed_and_listed(self):
        with tempfile.TemporaryDirectory() as raw:
            out, data, rows = self.harvest(raw)
            self.assertEqual(ok_ids(rows), [])
            self.assertEqual(len(data["files"]), len(self.GOOD) + 3 + 6)
            for f in data["files"]:
                gz = out / f["gz"]
                self.assertEqual(a.seal(gz), f["gz_seal"])
                original = gzip.decompress(gz.read_bytes())
                self.assertEqual(len(original), f["bytes"])
            sums = (out / "SHA256SUMS").read_text().splitlines()
            self.assertEqual(len(sums), len(data["files"]))
            self.assertTrue(all(s.split()[1].startswith("logs/")
                                for s in sums))

    def test_failing_suite_fails(self):
        with tempfile.TemporaryDirectory() as raw:
            _, _, rows = self.harvest(
                raw, **{"simp-ext": "a ... OK\nb ... FAILED\n"
                        "TraverseExt lifetime checks: 2\n"})
            self.assertEqual(ok_ids(rows), [
                "E1.log.src/simp/src/.hol/logs/simp-ext"])

    def test_real_failure_format_fails_the_harvest(self):
        with tempfile.TemporaryDirectory() as raw:
            _, _, rows = self.harvest(
                raw, **{"simp-ext": "a ... OK\nb ... \x1b[2CFAILED!\n"
                        "Failure count = 1\n"
                        "TraverseExt lifetime checks: 2\n"})
            self.assertEqual(ok_ids(rows), [
                "E1.log.src/simp/src/.hol/logs/simp-ext"])

    def test_recipe_logs_and_src1_log_are_required(self):
        for rel in ("src/real/.hol/logs/tracked-recipes",
                    "src/1/.hol/logs/selftest.log"):
            with self.subTest(rel), tempfile.TemporaryDirectory() as raw:
                root = self.tree(raw)
                (root / rel).unlink()
                checks = t.Checks()
                t.harvest(root, Path(raw) / "out", checks, self.DECL)
                rows = {c["id"]: c for c in checks.rows}
                self.assertEqual(ok_ids(rows), ["E1.required-logs"])
                self.assertIn(rel, rows["E1.required-logs"]["reason"])

    def test_truncated_recipe_log_fails(self):
        with tempfile.TemporaryDirectory() as raw:
            root = self.tree(raw)
            (root / "src/integer/.hol/logs/tracked-recipes").write_text(
                "a ... OK\nb ...  ")
            checks = t.Checks()
            t.harvest(root, Path(raw) / "out", checks, self.DECL)
            self.assertEqual(ok_ids({c["id"]: c for c in checks.rows}), [
                "E1.log.src/integer/.hol/logs/tracked-recipes"])

    def test_harvest_is_byte_for_byte_reproducible(self):
        outs = []
        for i in range(2):
            with tempfile.TemporaryDirectory() as raw:
                out, data, _ = self.harvest(raw)
                outs.append((
                    (out / "SHA256SUMS").read_text(),
                    {f["path"]: (out / f["gz"]).read_bytes()
                     for f in data["files"]},
                    [(f["path"], f["sha256"], f["gz_seal"], f["passed"])
                     for f in data["files"]]))
        self.assertEqual(outs[0], outs[1])

    def test_missing_suite_fails(self):
        with tempfile.TemporaryDirectory() as raw:
            _, _, rows = self.harvest(raw, **{"replay-order": None})
            self.assertEqual(ok_ids(rows), ["E1.required-logs"])

    def test_nonempty_output_directory_is_refused(self):
        with tempfile.TemporaryDirectory() as raw:
            root = self.tree(raw)
            out = Path(raw) / "out"
            out.mkdir()
            (out / "x").write_text("x")
            with self.assertRaises(t.Refusal):
                t.harvest(root, out, t.Checks(), self.DECL)


# ----------------------------------------------------- the fake archive

class Archive:
    """A tiny downstream archive: one unit, 4 pairs x 1 rep, both phases;
    `edit(receipt)` may change any receipt before it is sealed."""
    SIDES = {"base": "/s/base", "cand": "/s/cand"}

    def __init__(self, raw, edit=None, loaded_cand=None):
        self.folder = Path(raw) / "first"
        self.folder.mkdir()
        runs, receipts = [], []
        for pair in range(4):
            for phase in ("control", "candidate"):
                for sel in ("baseline", "candidate"):
                    side = "cand" if phase == "candidate" and \
                        sel == "candidate" else "base"
                    r = self.receipt(pair, phase, sel, side,
                                     loaded_cand if side == "cand" else None)
                    if edit:
                        edit(r)
                    receipts.append(r)
        for r in receipts:
            label = "lim-%s-%03d-%s-%02d" % (
                r["phase"], r["pair"], r["selection"], r["rep"])
            path = self.folder / (label + ".json.gz")
            path.write_bytes(gzip.compress(json.dumps(r).encode(),
                                           mtime=0))
            runs.append(dict(receipt=path.name, seal=a.seal(path),
                             workload="lim", phase=r["phase"],
                             pair=r["pair"], selection=r["selection"],
                             rep=0, accepted=True))
        self.receipts = receipts
        self.report = dict(
            schema="task32-downstream-v1", success=True, workloads=["lim"],
            mode="first", stage="first", repo="/nonexistent", references={},
            roots=self.SIDES, base="b", cand="c", manifest={},
            reporter={s: {"dir": "/r/" + s} for s in self.SIDES},
            runs=runs, outcome=dict(results=dict(lim=self.results())))
        (self.folder / "downstream.json").write_text(
            json.dumps(self.report))

    def receipt(self, pair, phase, sel, side, loaded):
        slow = 1.1 if side == "cand" else 1.0
        root = self.SIDES[side]
        return dict(
            workload="lim", phase=phase, pair=pair, selection=sel, rep=0,
            side=side, accepted=True,
            usage=dict(maxrss=1000 + pair),
            stats=dict(
                gc_full=13, gc_partial=170 + pair, gc_share=0,
                gc_time=(1.0 + 0.1 * pair) * slow,
                size_heap=700 + pair, holdir=root,
                loaded_before=["A", "B"], loaded=loaded or ["C"],
                files=[["C.uo", root + "/src"], ["R.uo", "/r/" + side]]))

    def results(self):
        def metric(f):
            rs = t.ratios(t.pair_means(self.receipts, "lim", f))
            m = dict(median_paired_ratio=t.median(rs), decision="reported",
                     paired_ratio_bootstrap_95_percent=[min(rs), max(rs)])
            return m
        metrics = {"gc_cpu": metric("gc_time"), "maxrss": metric("maxrss")}
        return dict(candidate=dict(metrics=metrics),
                    control=dict(metrics=metrics))


def fake_check_receipt(folder, report, entry, refs):
    """What the fake archive can say of d.check_receipt: seal, label and
    agreement with the report (the command and layout checks need real
    receipts and are TASK32's)."""
    path = a.safe_child(folder, entry["receipt"])
    if a.seal(path) != entry["seal"]:
        raise d.Refusal("changed process receipt")
    r = a.load(path)
    if not all(r[k] == entry[k] for k in (
            "workload", "phase", "pair", "selection", "rep")):
        raise d.Refusal("disagrees with the report")
    return r


class ArchiveTest(unittest.TestCase):
    def setUp(self):
        self.ledger_calls = []
        for target, value in (
                ("check_receipt", fake_check_receipt),
                ("check_ledger", lambda *x: self.ledger_calls.append(x)),
                ("stage_status", lambda results: 0)):
            patch = mock.patch.object(d, target, value)
            patch.start()
            self.addCleanup(patch.stop)

    def build(self, **kw):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        return Archive(tmp.name, **kw)

    def run_archive(self, arch, replay=False, repo=None, ledger=None):
        checks = t.Checks()
        inputs, data = t.archive_report(arch.folder, repo, replay, checks,
                                        ledger)
        return {c["id"]: c for c in checks.rows}, inputs, data

    def test_fake_archive_passes_and_reports(self):
        arch = self.build()
        rows, inputs, data = self.run_archive(arch)
        self.assertEqual(ok_ids(rows), [])
        self.assertEqual(rows["archive.replay"]["status"], "skipped")
        self.assertEqual(rows["archive.ledger"]["status"], "pass")
        self.assertEqual(inputs["receipts"], 16)
        unit = data["units"]["lim"]
        self.assertEqual(unit["sides"]["base"]["fields"]["gc_full"],
                         dict(n=4, median=13, min=13, max=13))
        self.assertEqual(unit["sides"]["cand"]["n"], 4)
        self.assertEqual(unit["sides"]["control"]["n"], 8)
        self.assertAlmostEqual(
            unit["paired"]["gc_time"]["median_paired_ratio"], 1.1)
        self.assertTrue(data["loaded"]["lim"]["equal"])
        self.assertIn("lim", data["attribution"])
        att = data["attribution"]["lim"]
        self.assertAlmostEqual(
            att["ratios_of_medians"]["gc_time"]["cand_over_base"], 1.1)
        self.assertEqual(
            att["ratios_of_medians"]["gc_full"]["cand_over_base"], 1.0)

    def test_changed_receipt_is_refused(self):
        arch = self.build()
        victim = next(arch.folder.glob("lim-candidate-000-*"))
        victim.write_bytes(gzip.compress(b"{}", mtime=0))
        with self.assertRaises(t.Refusal):
            self.run_archive(arch)

    def test_loaded_set_mismatch_fails(self):
        arch = self.build(loaded_cand=["C", "D"])
        rows, _, data = self.run_archive(arch)
        self.assertIn("L1.masked-sets-equal.lim", ok_ids(rows))
        self.assertIn("L1.new-stems", ok_ids(rows))
        self.assertFalse(data["loaded"]["lim"]["equal"])

    def test_same_names_from_another_directory_fails(self):
        def edit(r):
            if r["side"] == "cand":
                r["stats"]["files"][0][1] = "/s/cand/elsewhere"
        rows, _, _ = self.run_archive(self.build(edit=edit))
        self.assertEqual(ok_ids(rows), ["L1.masked-sets-equal.lim"])

    def test_a_baseline_that_differs_from_itself_fails(self):
        def edit(r):
            if r["side"] == "base" and r["pair"] == 0 and \
                    r["selection"] == "baseline" and \
                    r["phase"] == "control":
                r["stats"]["loaded"].append("Flaky")
        rows, _, data = self.run_archive(self.build(edit=edit))
        self.assertIn("L1.masked-sets-equal.lim", ok_ids(rows))
        self.assertIn("harness fault",
                      rows["L1.masked-sets-equal.lim"]["reason"])
        self.assertFalse(data["loaded"]["lim"]["equal"])

    def test_a_misplaced_prefix_is_refused_by_the_drivers_masked_view(
            self):
        def edit(r):
            r["stats"]["files"].append(["P.sml", r["stats"]["holdir"] +
                                        "2/x"])
        with self.assertRaisesRegex(d.Refusal, "misplaced"):
            self.run_archive(self.build(edit=edit))

    def test_the_archive_is_task32s_whichever_table_is_active(self):
        self.assertEqual(t.T32, d.TABLES["task32"])
        self.assertEqual(t.CODE, t.OWN_CODE + d.TABLES["task32"].code)
        self.assertFalse(any("task33_cases" in n or "task33_records" in n
                             for n in t.CODE))
        arch = self.build()
        seen = []

        def replay(folder, ledger=None, repo=None, **kw):
            seen.append((d.ACTIVE.name, d.TABLE, d.CODE, d.HISTORY))
            return dict(replayed=16, exit=0), {}
        for name in ("task32", "task33"):
            with d.using_table(name), \
                    mock.patch.object(d, "replay_one", replay):
                rows, _, _ = self.run_archive(arch, replay=True,
                                              repo=Path("/tool"))
                self.assertEqual(d.ACTIVE.name, name)
            self.assertEqual(rows["archive.replay"]["status"], "pass")
        self.assertEqual(seen[0], seen[1])
        self.assertEqual(seen[0][0], "task32")
        self.assertEqual(seen[0][2], d.TABLES["task32"].code)
        self.assertIs(seen[0][3], d.TABLES["task32"].history)

    def test_the_code_seals_use_task32s_history_under_task33(self):
        seals = t.code_seals()
        old = dict(seals, **{"task32_downstream.py": dict(
            seals["task32_downstream.py"], sha256="0" * 64)})
        with d.using_table("task33"):
            with self.assertRaises(t.Refusal):
                t.check_code(old)
            history = d.TABLES["task32"].history["task32_downstream.py"]
            t.check_code(dict(seals, **{"task32_downstream.py": history[0]}))
            # the TASK33 driver's seal is accepted by the S3 reports only
            driver = d.TASK33_DRIVER_SEALS[0]
            t.check_code(dict(seals, **{"task32_downstream.py": driver}))
            self.assertNotIn(driver, history)
            t.check_code(dict(seals, **{
                "task33_offline.py": d.TASK33_HISTORY[
                    "task33_offline.py"][0]}))
            t.check_code(seals)

    def test_extension_module_loaded_fails(self):
        def edit(r):
            if r["side"] == "cand":
                r["stats"]["loaded"].append("splitLib")
        rows, _, _ = self.run_archive(self.build(edit=edit))
        self.assertIn("L1.paths-and-extensions", ok_ids(rows))

    def test_path_outside_the_root_fails(self):
        def edit(r):
            if r["side"] == "base":
                r["stats"]["files"][0][1] = "/elsewhere"
        rows, _, _ = self.run_archive(self.build(edit=edit))
        self.assertIn("L1.paths-and-extensions", ok_ids(rows))

    def test_report_not_tied_to_receipts_fails(self):
        arch = self.build()
        report = json.loads((arch.folder / "downstream.json").read_text())
        report["outcome"]["results"]["lim"]["candidate"]["metrics"][
            "gc_cpu"]["median_paired_ratio"] = 1.5
        (arch.folder / "downstream.json").write_text(json.dumps(report))
        rows, _, _ = self.run_archive(arch)
        self.assertEqual(ok_ids(rows), ["S3.ties-to-report.lim.gc_time"])

    def test_interval_above_one_is_listed(self):
        arch = self.build()
        rows, _, data = self.run_archive(arch)
        # the fake candidate is 1.1 times slower in every pair: the whole
        # interval is above 1 and above the margin
        gc = [x for x in data["above"] if x["field"] == "gc_cpu"]
        self.assertEqual([x["unit"] for x in gc], ["lim"])
        self.assertAlmostEqual(gc[0]["low"], 1.1)
        self.assertTrue(gc[0]["wholly_above_margin"])
        self.assertEqual(gc[0]["decision"], "reported")

    def test_every_reported_metric_is_listed_with_attribution(self):
        arch = self.build()
        report = json.loads((arch.folder / "downstream.json").read_text())
        metrics = report["outcome"]["results"]["lim"]["candidate"][
            "metrics"]
        metrics["maxrss"] = dict(metrics["maxrss"],
                                 paired_ratio_bootstrap_95_percent=[1.02,
                                                                    1.2])
        metrics["gc_cpu"] = dict(metrics["gc_cpu"],
                                 paired_ratio_bootstrap_95_percent=[0.9, 1.2])
        metrics["wall"] = dict(metrics["gc_cpu"],
                               paired_ratio_bootstrap_95_percent=[1.2, 1.3])
        (arch.folder / "downstream.json").write_text(json.dumps(report))
        _, _, data = self.run_archive(arch)
        found = {x["field"]: x for x in data["above"]}
        self.assertEqual(sorted(found), ["maxrss", "wall"])
        self.assertAlmostEqual(found["maxrss"]["low"], 1.02)
        self.assertFalse(found["maxrss"]["wholly_above_margin"])
        self.assertTrue(found["wall"]["wholly_above_margin"])
        self.assertIn("lim", data["attribution"])
        self.assertIn("maxrss", data["attribution"]["lim"]["groups"]["base"])

    def test_pair_series_cover_the_same_pairs(self):
        def edit(r):
            # pair 1 has no baseline size_heap: it is out of every series
            if r["pair"] == 1 and r["selection"] == "baseline" and \
                    r["phase"] == "candidate":
                r["stats"]["size_heap"] = 0
        _, _, data = self.run_archive(self.build(edit=edit))
        att = data["attribution"]["lim"]
        self.assertEqual(att["pairs_kept"], [0, 2, 3])
        self.assertEqual(att["pairs_total"], 4)
        self.assertEqual({len(v) for v in att["pair_ratios"].values()},
                         {3})

    def test_ledger_is_always_checked_against_the_report_seal(self):
        arch = self.build()
        self.run_archive(arch, ledger=Path("/x/attempts.jsonl"))
        (path, report, seal, status), = self.ledger_calls
        self.assertEqual(path, Path("/x/attempts.jsonl"))
        self.assertEqual(seal, a.seal(arch.folder / "downstream.json"))
        self.assertEqual(status, 0)

    def test_ledger_refusal_fails(self):
        arch = self.build()
        with mock.patch.object(d, "check_ledger",
                               side_effect=d.Refusal("not closed")):
            rows, _, _ = self.run_archive(arch)
        self.assertEqual(ok_ids(rows), ["archive.ledger"])

    def test_replay_gets_the_tools_repository(self):
        arch = self.build()
        seen = []

        def replay(folder, ledger=None, repo=None, **kw):
            seen.append((Path(folder), ledger, repo))
            return dict(replayed=16, exit=0), {}
        with mock.patch.object(d, "replay_one", replay):
            rows, _, _ = self.run_archive(arch, replay=True,
                                          repo=Path("/tool"),
                                          ledger=Path("/l"))
        self.assertEqual(seen, [(arch.folder.resolve(), Path("/l"),
                                 Path("/tool"))])
        self.assertEqual(rows["archive.replay"]["status"], "pass")
        with mock.patch.object(d, "replay_one",
                               side_effect=d.Refusal("changed")):
            rows, _, _ = self.run_archive(arch, replay=True)
        self.assertEqual(ok_ids(rows), ["archive.replay"])

    def test_no_replay_is_inconclusive(self):
        arch = self.build()
        with tempfile.TemporaryDirectory() as raw:
            argv = ["archive", "--archive", str(arch.folder), "--no-replay",
                    "--out", str(Path(raw) / "a.json")]
            out = io.StringIO()
            with contextlib.redirect_stdout(out), mock.patch.object(
                    t, "default_repo", lambda: Path("/tool")):
                code = t.main(argv)
            report = json.loads((Path(raw) / "a.json").read_text())
        self.assertEqual(code, 2)
        self.assertEqual((report["success"], report["exit"]), (False, 2))
        self.assertEqual({c["id"]: c["status"] for c in report["checks"]}[
            "archive.replay"], "skipped")
        self.assertIn("INCONCLUSIVE", out.getvalue())


class CountsTest(unittest.TestCase):
    """Reviewed counts of the marker-less suites, and the log rules that
    pin them."""
    D = dict(log_counts={"native-extension": 2, "literal-exclusions": 3,
                         "compiled-core": 1})

    def judge(self, name, text, declared=D):
        return t.judge_log("src/simp/src/.hol/logs/" + name, text, declared)

    def test_needs_count_is_for_marker_less_suites_only(self):
        for name in ("native-extension", "literal-exclusions",
                     "compiled-core", "fragment-contracts",
                     "traversal-contracts", "simp-selftest",
                     "src/1/.hol/logs/selftest.log", "split-lifecycle"):
            self.assertTrue(t.needs_count(name), name)
        for name in ("cond-rewr-ext", "legacy-contracts", "api-audit",
                     "check-full", "src/real/.hol/logs/tracked-recipes"):
            self.assertFalse(t.needs_count(name), name)

    def test_required_logs_include_the_ordinary_suites(self):
        for name in ("traversal-contracts", "literal-exclusions",
                     "ordinary-tactics", "compiled-core",
                     "fragment-contracts", "simp-selftest"):
            self.assertIn(name, t.LOGS_REQUIRED)

    def test_ok_lines_must_equal_the_reviewed_count(self):
        ok = "a ... OK\nb ... OK\n"
        self.assertTrue(self.judge("native-extension", ok)[0])
        for text in ("a ... OK\n", ok + "c ... OK\n"):
            passed, reasons, _ = self.judge("native-extension", text)
            self.assertFalse(passed)
            self.assertIn("reviewed 2", reasons[0])
        passed, reasons, _ = self.judge("native-extension", ok, dict(
            log_counts={}))
        self.assertIn("no reviewed ok_lines", reasons[0])

    def test_ran_blocks_and_manifest_lines_are_counted(self):
        block = "Ran 1 tests in 1s\n\nOK\n"
        self.assertTrue(self.judge("literal-exclusions", block * 3)[0])
        self.assertFalse(self.judge("literal-exclusions", block * 2)[0])
        self.assertTrue(self.judge("compiled-core", "x/manifest.json\n")[0])
        self.assertFalse(self.judge(
            "compiled-core", "x/manifest.json\ny/manifest.json\n")[0])

    def test_skipped_tests_need_a_declaration(self):
        text = "Ran 4 tests in 1s\n\nOK (skipped=2)\n"
        passed, reasons, counts = self.judge(
            "literal-exclusions", text * 3)
        self.assertFalse(passed)
        self.assertEqual(counts["skipped"], 6)
        self.assertIn("6 skipped test(s), 0 declared", reasons[0])
        declared = dict(self.D, log_skips={"literal-exclusions": 6})
        self.assertTrue(self.judge("literal-exclusions", text * 3,
                                   declared)[0])
        # other suffixes of the OK line are not a legitimate pass
        for suffix in (" (expected failures=1)",
                       " (skipped=1, expected failures=1)",
                       " (unexpected successes=1)"):
            bad = "Ran 4 tests in 1s\n\nOK" + suffix + "\n"
            self.assertFalse(self.judge("literal-exclusions", bad * 3)[0])

    def test_declaration_must_cover_exactly_the_needed_logs(self):
        def bad(change):
            declared = t.load_declared()
            change(declared)
            checks = t.Checks()
            t.check_declaration(declared, checks)
            return [c["id"] for c in checks.failed()]
        self.assertEqual(bad(lambda x: None), [])
        for name, change in (
                ("missing", lambda x: x["log_counts"].pop("replay-order")),
                ("unknown", lambda x: x["log_counts"].update(mystery=1)),
                ("not a count",
                 lambda x: x["log_counts"].update({"replay-order": 0})),
                ("not an int",
                 lambda x: x["log_counts"].update({"replay-order": "9"})),
                ("not a map", lambda x: x.update(log_counts=[1])),
                ("skips of a tprint log",
                 lambda x: x.update(log_skips={"replay-order": 1})),
                ("s2 parts without path",
                 lambda x: x["s2"]["structures"][1].update(
                     paths=["src/simp/src/Cond_rewr.sig"]))):
            with self.subTest(name):
                self.assertEqual(bad(change), ["declared.valid"])
        self.assertEqual(bad(lambda x: x.update(
            log_skips={"ordinary-tactics": 1})), [])


class DeclaredTest(unittest.TestCase):
    def test_committed_declaration_is_valid_and_matches_git(self):
        declared = t.load_declared()
        checks = t.Checks()
        t.check_declaration(declared, checks)
        self.assertEqual(checks.failed(), [])
        self.assertEqual(
            sorted(e["path"] for e in declared["l2"]),
            ["src/1/ThmAttribute.sig", "src/1/ThmAttribute.sml",
             "src/simp/src/Cond_rewr.sig"])
        for e in declared["l2"] + declared["allowlist"]:
            self.assertTrue(e.get("mechanism", "m") and e["justification"])
        self.assertEqual(
            sorted(s["structure"] for s in declared["s2"]["structures"]),
            ["Cond_rewr", "ThmAttribute"])
        # the opaque structure Cond_rewr gains the slot with its spec
        cond = {s["structure"]: s
                for s in declared["s2"]["structures"]}["Cond_rewr"]
        self.assertEqual(cond["parts"], ["struct", "sig"])
        self.assertEqual(cond["paths"], ["src/simp/src/Cond_rewr.sml",
                                         "src/simp/src/Cond_rewr.sig"])
        self.assertIn("note_rewrite", cond["mechanism"])
        ext = {x["name"]: x for x in declared["e2c"]["extension_state"]}
        self.assertIn("named-fragments", ext)
        self.assertIn("tracked-defaults-provider", ext)
        self.assertIn("trackedSimpDefaults.provider",
                      ext["tracked-defaults-provider"]["where"])
        self.assertIn("not by an explicit call",
                      ext["context-data-slots"]["created_by"])
        self.assertIn("source_serial", ext["source-serial"]["where"])
        try:
            repo = t.default_repo()
        except t.Refusal:
            self.skipTest("not inside a git tree")
        for e in declared["l2"] + declared["allowlist"]:
            for side, key in (("base", "base_blob"), ("cand", "cand_blob")):
                try:
                    found = t.blob_ids(repo, declared[side], [e["path"]])
                except t.Refusal:
                    self.skipTest("pins are not in this clone")
                self.assertEqual(found[e["path"]], e[key])

    def test_shapes_of_s2_e2c_and_allowlist_are_validated(self):
        def bad(change):
            declared = t.load_declared()
            change(declared)
            checks = t.Checks()
            t.check_declaration(declared, checks)
            return [c["id"] for c in checks.failed()]
        self.assertEqual(bad(lambda x: None), [])
        for name, change in (
                ("s2 not an object", lambda x: x.update(s2=[])),
                ("s2 no structures", lambda x: x.update(s2={})),
                ("s2 part", lambda x: x["s2"]["structures"][0].update(
                    parts=["other"])),
                ("s2 missing key", lambda x: x["s2"]["structures"][0].pop(
                    "reference")),
                ("e2c empty", lambda x: x.update(e2c={})),
                ("e2c required",
                 lambda x: x["e2c"]["extension_state"][0].update(
                     required="yes")),
                ("e2c missing",
                 lambda x: x["e2c"]["extension_state"][0].pop("source")),
                ("e2c observable flag",
                 lambda x: x["e2c"]["extension_state"][0].pop(
                     "observable")),
                ("e2c observable without names",
                 lambda x: x["e2c"]["extension_state"][0].update(
                     registers={})),
                ("e2c unknown list",
                 lambda x: x["e2c"]["extension_state"][0].update(
                     registers=dict(nothing=["a"]))),
                ("e2c duplicate name",
                 lambda x: x["e2c"]["extension_state"][0].update(
                     registers=dict(structures=["a", "a"]))),
                ("e2c unobservable required",
                 lambda x: x["e2c"]["extension_state"][-1].update(
                     required=True)),
                ("e2c unobservable with names",
                 lambda x: x["e2c"]["extension_state"][-1].update(
                     registers=dict(structures=["a"]))),
                ("probe support missing",
                 lambda x: x["e2c"].pop("probe_support")),
                ("probe support empty",
                 lambda x: x["e2c"]["probe_support"].update(registers={})),
                ("allowlist blob",
                 lambda x: x["allowlist"][0].update(cand_blob="abc")),
                ("allowlist text",
                 lambda x: x["allowlist"][0].update(justification=" ")),
                ("pin", lambda x: x.update(cand="short"))):
            with self.subTest(name):
                self.assertEqual(bad(change), ["declared.valid"])

    def test_the_total_delta_is_declared_and_its_shape_validated(self):
        declared = t.load_declared()
        deltas = declared["s2"]["total_delta"]
        self.assertIsInstance(deltas, list)
        delta = deltas[0]
        self.assertEqual(delta["value"], 754)
        self.assertEqual(delta["observed"]["cand"] -
                         delta["observed"]["base"], 754)
        self.assertIn("note_rewrite", delta["mechanism"])
        self.assertIn("attribute_fns", delta["mechanism"])

        def bad(change):
            declared = t.load_declared()
            change(declared["s2"]["total_delta"][0])
            checks = t.Checks()
            t.check_declaration(declared, checks)
            reason = " ".join(c["reason"] for c in checks.failed())
            return [c["id"] for c in checks.failed()], reason
        for name, change, why in (
                ("zero", lambda x: x.update(value=0), "positive"),
                ("negative", lambda x: x.update(value=-5), "positive"),
                ("float", lambda x: x.update(value=754.0), "positive"),
                ("unit", lambda x: x.update(unit="bytes"), "words"),
                ("not observed",
                 lambda x: x.update(value=755), "cand - base"),
                ("no observed", lambda x: x.pop("observed"), "observed"),
                ("grown part",
                 lambda x: x["observed"]["exclusive"].update(
                     simpLib=[1, 2]), "cand <= base"),
                ("missing part",
                 lambda x: x["observed"]["exclusive"].pop("Opening"),
                 "exclusive parts"),
                ("no mechanism", lambda x: x.update(mechanism=" "),
                 "mechanism"),
                ("paths", lambda x: x.update(paths=["a.sml"]), "paths"),
                ("state allowed",
                 lambda x: x.update(allowed_kinds=["code", "state"]),
                 "code only"),
                ("state not forbidden",
                 lambda x: x.update(forbidden_kinds=["per-object"]),
                 "code only"),
                ("no heap", lambda x: x.pop("heap"), "heap and kinds"),
                ("empty heap", lambda x: x.update(heap=" "),
                 "heap and kinds"),
                ("unknown kind", lambda x: x.update(kinds=["nonesuch"]),
                 "heap and kinds"),
                ("no kinds", lambda x: x.update(kinds=[]),
                 "heap and kinds"),
                ("repeated kind",
                 lambda x: x.update(kinds=["state-empty", "state-empty"]),
                 "heap and kinds"),
                ("kind not a string", lambda x: x.update(kinds=[1]),
                 "heap and kinds")):
            with self.subTest(name):
                ids, reason = bad(change)
                self.assertEqual(ids, ["declared.valid"])
                self.assertIn(why, reason)

    def problems(self, deltas):
        declared = t.load_declared()
        declared["s2"]["total_delta"] = deltas
        checks = t.Checks()
        t.check_declaration(declared, checks)
        return " ".join(c["reason"] for c in checks.failed())

    def test_the_total_delta_is_a_list_of_scoped_entries(self):
        good = t.load_declared()["s2"]["total_delta"]
        self.assertEqual(self.problems(good), "")
        for name, value in (("an object", good[0]), ("empty", []),
                            ("none", None), ("a string", "754")):
            with self.subTest(name):
                self.assertIn("non-empty list", self.problems(value))
        self.assertIn("is not an object", self.problems([good[0], 5]))
        # each (heap, kind) at most once, over the entries
        again = copy.deepcopy(good[0])
        again["kinds"] = ["first-use"]
        self.assertIn("declared twice", self.problems([good[0], again]))
        other = copy.deepcopy(good[0])
        other.update(heap="bin/hol.state0", kinds=["load-simpLib"])
        self.assertEqual(self.problems([good[0], other]), "")
        # an entry is checked on its own
        other["value"] = 3
        self.assertIn("[1]: value is not observed", self.problems(
            [good[0], other]))

    def test_the_declared_entries_cover_the_kinds_that_compute_u(self):
        # U needs all six structures: the hol.state kinds only (hol.state0
        # has no boolSimps and pureSimps loaded, measured live)
        got = {(e["heap"], k) for e in t.load_declared()["s2"][
            "total_delta"] for k in e["kinds"]}
        self.assertEqual(got, {("bin/hol.state", "state-empty"),
                               ("bin/hol.state", "first-use")})


if __name__ == "__main__":
    unittest.main()
