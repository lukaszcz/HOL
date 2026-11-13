#!/usr/bin/env python3
"""Unit tests; opt-in real paired client audit with HOL_CLIENT_REPO=<repo>.

Use a configured tree (and its historical root wrapper if required). The real
smoke builds/runs baseline then HEAD serially, audits exact paths with
run_paired.validate, and cleans both private trees. It is not timing evidence.
"""
import hashlib
import os
from pathlib import Path
import sys
import tempfile
import unittest

import client_dependencies as cd


class InstallTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="client-deps-test-")
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name) / "repo"
        self.dst = Path(self.tmp.name) / "private"
        (self.repo / "sigobj").mkdir(parents=True)
        self.dst.mkdir()

    def module(self, name, deps=(), sigdeps=(), hfs=False, theory=False,
               under_simp=False):
        directory = self.repo / "src" / ("simp" if under_simp else name)
        objects = directory / ".hol/objs"
        objects.mkdir(parents=True, exist_ok=True)
        for suffix, edges in ((".sml", deps), (".sig", sigdeps)):
            source = directory / (name + suffix)
            physical = objects / source.name if hfs else source
            physical.write_text("TheoryReader.load_thydata {}\n" if theory and
                                suffix == ".sml" else "(* source *)\n")
            product = objects / (name + (".uo" if suffix == ".sml" else ".ui"))
            lines = ["$(HOLDIR)/sigobj/" + dep for dep in edges]
            base = "$(HOLDIR)/" + str(directory.relative_to(self.repo)) + "/"
            lines += [base + name, base + source.name]
            product.write_text("\n".join(lines) + "\n")
            (self.repo / "sigobj" / product.name).symlink_to(product)
        if theory:
            dat = (objects if hfs else directory) / (name + ".dat")
            dat.write_bytes(b"theory-data")

    def fixture(self, text="open bossLib\n"):
        (self.dst / "Performance.sml").write_text(text)
        (self.dst / "simpLib.sml").write_text("(* selected source *)\n")

    def install(self):
        return cd.install(self.repo, self.dst, {"simpLib"})

    def test_recursive_reverse_slice_not_all_shared_or_all_dependents(self):
        self.module("simpLib")
        self.module("safe")
        self.module("mid", ["simpLib", "safe"])
        self.module("bossLib", ["mid", "safe"])
        self.module("unrelated", ["simpLib"])
        self.fixture()
        result = self.install()
        self.assertEqual(result["modules"], ["bossLib", "mid"])
        self.assertEqual(set(result["products"]) - {"Holmakefile"},
                         {"bossLib.sml", "bossLib.sig", "mid.sml", "mid.sig"})
        for name, info in result["products"].items():
            self.assertEqual(info["role"], "shared-dependency")
            data = (self.dst / name).read_bytes()
            self.assertEqual(info["sha256"], hashlib.sha256(data).hexdigest())
            self.assertEqual(info["bytes"], len(data))
            if name != "Holmakefile":
                self.assertIn(info["source"], result["inputs"])
        self.assertEqual((self.dst / "simpLib.sml").read_text(),
                         "(* selected source *)\n")
        # Negative graph decisions are sealed too, not just copied inputs.
        unrelated = (self.repo / "sigobj/unrelated.uo").resolve()
        self.assertIn(str(unrelated), result["inputs"])
        self.assertIn(str(self.repo / "sigobj/unrelated.uo"), result["inputs"])
        rules = (self.dst / "Holmakefile").read_text()
        self.assertRegex(rules, r"(?m)^bossLib\.uo: .*\bmid\.uo\b")
        self.assertIn("$(dprot " + str(self.repo / "sigobj/safe.uo") + ")",
                      rules)

    def test_signature_edges_hfs_theory_data_and_cycles(self):
        self.module("simpLib")
        self.module("middle", ["bossLib"], ["simpLib"], hfs=True, theory=True)
        self.module("bossLib", ["middle"])
        self.fixture()
        result = self.install()
        self.assertEqual(result["modules"], ["bossLib", "middle"])
        self.assertEqual((self.dst / "middle.dat").read_bytes(),
                         b"theory-data")
        self.assertIn("/.hol/objs/",
                      result["products"]["middle.sml"]["source"])
        self.assertEqual(result["products"]["middle.dat"]["role"],
                         "shared-dependency")

    def test_generated_simp_support_is_also_private_with_shared_data(self):
        self.module("simpLib")
        self.module("contextTheory", hfs=True, theory=True, under_simp=True)
        self.module("bossLib", ["simpLib", "contextTheory"])
        self.fixture()
        result = self.install()
        self.assertEqual(result["modules"], ["bossLib", "contextTheory"])
        dat = ".hol/objs/contextTheory.dat"
        self.assertEqual((self.dst / dat).read_bytes(), b"theory-data")
        self.assertEqual(result["products"][dat]["role"], "shared-dependency")
        self.assertFalse((self.dst / "contextTheory.sml").exists())
        loader = (self.dst / ".hol/objs/contextTheory.uo").read_text()
        self.assertIn(str(self.dst / "contextTheory.sml"), loader)
        self.assertNotIn("$(HOLDIR)/src/simp", loader)
        self.assertIn("contextTheory.uo contextTheory.ui",
                      (self.dst / "Holmakefile").read_text())

    def private_script_case(self, names):
        """A shared simp library, theory of the same name as a private script
        and an unrelated simp theory, both generated; the private sources
        are a library mentioning the theory and the script."""
        self.module("simpLib")
        self.module("markTheory", hfs=True, theory=True, under_simp=True)
        self.module("contextTheory", hfs=True, theory=True, under_simp=True)
        self.module("bossLib", ["simpLib", "markTheory", "contextTheory"])
        self.fixture()
        (self.dst / "markLib.sml").write_text("open markTheory\n")
        (self.dst / "markScript.sml").write_text("(* private script *)\n")
        return cd.install(self.repo, self.dst, names)

    def test_theory_of_a_private_script_is_private(self):
        result = self.private_script_case({"simpLib", "markLib",
                                           "markScript"})
        # Nothing of markTheory is copied or sealed as a product, though
        # the private sources name it and it is a generated simp theory.
        self.assertEqual(result["modules"], ["bossLib", "contextTheory"])
        for name in result["products"]:
            self.assertNotIn("markTheory", name)
        self.assertFalse(list(self.dst.rglob("markTheory.*")))
        self.assertNotIn("markTheory.dat",
                         (self.dst / "Holmakefile").read_text())
        # The unrelated shared simp theory is still copied as before.
        dat = ".hol/objs/contextTheory.dat"
        self.assertEqual((self.dst / dat).read_bytes(), b"theory-data")
        self.assertEqual(result["products"][dat]["role"], "shared-dependency")
        # The dependents load the private theory, not a frozen shared one.
        rules = (self.dst / "Holmakefile").read_text()
        self.assertRegex(rules, r"(?m)^bossLib\.uo: .*\bmarkTheory\.uo\b")

    def test_the_private_set_is_returned_with_the_theories(self):
        result = self.private_script_case({"simpLib", "markLib",
                                           "markScript"})
        self.assertEqual(result["private"], ["markLib", "markScript",
                                             "markTheory", "simpLib"])

    def test_a_frozen_theory_rebound_to_a_private_one_builds_it(self):
        # contextTheory is copied and frozen; its descriptor names
        # markTheory, which is private: the descriptor is rebound to the
        # private directory and the theory is built whatever else needs it.
        self.module("simpLib")
        self.module("markTheory", hfs=True, theory=True, under_simp=True)
        self.module("contextTheory", ["markTheory"], hfs=True, theory=True,
                    under_simp=True)
        self.module("bossLib", ["contextTheory"])
        self.fixture()
        (self.dst / "markScript.sml").write_text("(* private script *)\n")
        result = cd.install(self.repo, self.dst, {"simpLib", "markScript"})
        self.assertEqual(result["modules"], ["bossLib", "contextTheory"])
        loader = (self.dst / ".hol/objs/contextTheory.uo").read_text()
        self.assertIn(str(self.dst / "markTheory"), loader.splitlines())
        rules = (self.dst / "Holmakefile").read_text()
        self.assertRegex(rules, r"(?m)^paired\.exe: .*\bmarkTheory\.uo\b")
        # a private name with nothing to build it from is no prerequisite
        self.dst = Path(self.tmp.name) / "private2"
        self.dst.mkdir()
        self.fixture()
        cd.install(self.repo, self.dst, {"simpLib", "markScript"})
        self.assertNotRegex((self.dst / "Holmakefile").read_text(),
                            r"(?m)^paired\.exe: .*markTheory")

    def test_theory_of_an_unselected_script_stays_shared(self):
        # Control: without the script among the private names the theory is
        # an ordinary shared simp module, copied and frozen.
        result = self.private_script_case({"simpLib", "markLib"})
        self.assertEqual(result["modules"],
                         ["bossLib", "contextTheory", "markTheory"])
        self.assertEqual(
            (self.dst / ".hol/objs/markTheory.dat").read_bytes(),
            b"theory-data")
        self.assertIn(".hol/objs/markTheory.dat", result["products"])

    def test_missing_required_data_fails_before_copy(self):
        self.module("simpLib")
        self.module("bossLib", ["simpLib"], hfs=True, theory=True)
        (self.repo / "src/bossLib/.hol/objs/bossLib.dat").unlink()
        self.fixture()
        with self.assertRaisesRegex(cd.DependencyError, "missing theory data"):
            self.install()
        self.assertFalse((self.dst / "bossLib.sml").exists())

    def test_collisions_never_overwrite_or_partially_copy(self):
        self.module("simpLib")
        self.module("bossLib", ["simpLib"])
        self.fixture()
        (self.dst / "bossLib.sig").write_text("caller owned")
        with self.assertRaisesRegex(cd.DependencyError, "collision"):
            self.install()
        self.assertEqual((self.dst / "bossLib.sig").read_text(),
                         "caller owned")
        self.assertFalse((self.dst / "bossLib.sml").exists())

    def test_missing_recursive_metadata_fails_closed(self):
        self.module("simpLib")
        self.module("bossLib", ["missing"])
        self.fixture()
        with self.assertRaisesRegex(cd.DependencyError,
                                    "unexported dependency"):
            self.install()

    def test_no_signature_and_dotted_module_name(self):
        self.module("simpLib")
        self.module("parser.grm", ["simpLib"])
        (self.repo / "sigobj/parser.grm.ui").write_text("")
        self.module("bossLib", ["parser.grm"])
        self.fixture()
        result = self.install()
        self.assertEqual(result["modules"], ["bossLib", "parser.grm"])
        self.assertNotIn("parser.grm.sig", result["products"])

    def test_metadata_escape_rejected(self):
        self.module("simpLib")
        self.fixture()
        (self.repo / "sigobj/simpLib.uo").write_text("/outside/simpLib.sml\n")
        with self.assertRaisesRegex(cd.DependencyError, "outside shared"):
            self.install()


@unittest.skipUnless(os.environ.get("HOL_CLIENT_REPO"),
                     "set HOL_CLIENT_REPO for serial real paired client audit")
class IntegratedTests(unittest.TestCase):
    def test_exact_client_paths_on_both_selections(self):
        repo = Path(os.environ["HOL_CLIENT_REPO"]).resolve(strict=True)
        sys.path.insert(0, str(repo / "src/simp/tests/compatibility"))
        import run_paired as rp
        import performance_schema as ps
        from acceptance import serial_lock

        lock = serial_lock(repo)
        lock.__enter__()
        self.addCleanup(lock.__exit__, None, None, None)
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_",
                                    "LD_"))}
        env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
        input_seals, selections = [], []
        temporary = tempfile.TemporaryDirectory(
            prefix="client-deps-integration-")
        with temporary as tmp:
            root = Path(tmp)
            refs = (("baseline", rp.BASE), ("candidate", "HEAD"))
            for selection, ref in refs:
                dst = root / selection
                dst.mkdir()
                inventory = rp.extract(repo, ref, dst)
                rp.install_fixtures(dst, performance=True,
                                    matrix_fixture="ClientPerformance.sml")
                names = {Path(s["git_path"]).stem for s in inventory}
                selections.append(names)
                installed = cd.install(repo, dst, names)
                self.assertTrue({"bossLib", "numLib", "reduceLib"} <=
                                set(installed["modules"]))
                input_seals.append(installed["inputs"])
                hashes = {str(p): rp.fingerprint(p) for p in dst.rglob("*")
                          if p.is_file()}
                command = [str(repo / "bin/Holmake"), "--no-project",
                           "--no-cache", "--no_prereqs",
                           "--holstate=" + str(repo / "bin/hol.state0"),
                           "-C", str(dst), "-j1", "paired.exe"]
                build = rp.execute(command, root, env, 180)
                self.assertFalse(build["timed_out"], build["stdout"][-8000:])
                self.assertEqual(build["exit"], 0, build["stdout"][-8000:])
                # Audit static products too: none may retain a shared absolute
                # edge to a selected or relocated module, even if not executed.
                local = names | set(installed["modules"])
                for product in (dst / ".hol/objs").iterdir():
                    if product.suffix not in (".uo", ".ui"):
                        continue
                    for line in product.read_text().splitlines():
                        if ("$(HOLDIR)/sigobj/" in line or
                                str(repo / "sigobj") in line):
                            self.assertNotIn(Path(line).name, local,
                                             str(product) + ": " + line)
                runenv = dict(env, PAIR_SELECTION=selection,
                              PAIR_FIXTURE="performance", PAIR_CONTROL="none",
                              PAIR_PRIVATE=str(dst), PAIR_TARGET="Performance",
                              PERF_CASE="downstream_boss", PERF_SIZE="1",
                              PERF_SAMPLES="1", PERF_SECONDS="0.002")
                receipt = rp.execute(
                    [str(dst / "paired.exe")], dst, runenv, 180)
                diagnostics = "\n".join(
                    line for line in receipt["stdout"].splitlines()
                    if not line.startswith(rp.PREFIX) or
                    "\texception\t" in line)
                self.assertEqual(receipt["exit"], 0, diagnostics[-12000:])
                observations, _ = ps.validate(
                    rp.parse_events(receipt["stdout"]), 1, 0.002,
                    labels=["downstream_boss"],
                    consumed={"downstream_boss": 1},
                    storage=False)
                validation = dict(
                    selection=selection, fixture="performance",
                    control="none", private=dst, repo=repo,
                    private_names=names, flavor="baseline", signature="pass",
                    source_hashes={**installed["inputs"], **hashes},
                    expected_observations=observations)
                audit = rp.validate(receipt, **validation)
                # Replaying a leaked source in an otherwise valid real trace
                # must hit the actual path guard, not merely a runtime error.
                bad = dict(receipt, stdout=receipt["stdout"].replace(
                    str(dst / "simpLib.sml"),
                    str(repo / "src/simp/src/simpLib.sml")))
                with self.assertRaisesRegex(rp.InvalidRun,
                                            "wrong loaded simplifier path"):
                    rp.validate(bad, **validation)
                for name in ("bossLib", "numLib", "reduceLib", "simpLib"):
                    self.assertIn(str(dst / (name + ".sml")), audit["paths"])
                for path, stamp in {**installed["inputs"], **hashes}.items():
                    p = Path(path)
                    if p.suffix != ".ui" or p.is_relative_to(repo):
                        self.assertEqual(rp.fingerprint(p), stamp, path)
                print(selection, "exact-path audit PASS;",
                      len(installed["modules"]), "shared modules rebuilt;",
                      len(audit["paths"]), "loaded sources", flush=True)
            # Common shared sources and graph metadata have identical seals.
            # A module selected only by one revision may instead be a copied
            # baseline dependency on the other side.
            left, right = input_seals
            for path in left.keys() & right.keys():
                self.assertEqual(left[path], right[path], path)
            for path in left.keys() ^ right.keys():
                self.assertIn(Path(path).stem, selections[0] ^ selections[1])
            for path, stamp in {**left, **right}.items():
                self.assertEqual(rp.fingerprint(Path(path)), stamp, path)


if __name__ == "__main__":
    unittest.main()
