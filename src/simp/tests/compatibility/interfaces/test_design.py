import contextlib
import copy
import io
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import check_design as design
from run_paired import require_revisions  # noqa: E402


class DesignTests(unittest.TestCase):
    def setUp(self):
        self.graph = json.loads((design.HERE / "graph.json").read_text())
        self.table = design.TABLE.read_text()

    def test_all_275_api_decisions(self):
        self.assertEqual(design.validate_table(self.table), 275)

    def test_existing_rows_are_develop_exports(self):
        design.validate_existing()
        rows = [dict(group="C2", old_api="congLib.CONGRUENCE_EQ_SIMP_RULE",
                     kind="existing")]
        with self.assertRaisesRegex(ValueError, "not exported by develop"):
            design.validate_existing(rows)
        rows[0]["old_api"] = "noSuchLib.f"
        with self.assertRaisesRegex(ValueError, "no develop signature"):
            design.validate_existing(rows)

    def test_existing_rows_reject_non_exports(self):
        # Names that appear only in a comment, in `signature X = sig`, or
        # not at all must be rejected; a real export must be accepted.
        for api in ["congLib.y", "simpLib.BoundedRewrites", "congLib.sig"]:
            rows = [dict(group="C2", old_api=api, kind="existing")]
            with self.assertRaisesRegex(ValueError, "not exported"):
                design.validate_existing(rows)
        design.validate_existing(
            [dict(group="B1", old_api="simpLib.SF", kind="existing")])

    def test_only_existing_rows_are_checked(self):
        rows = [dict(group="T1", old_api="simpLib.BoundedRewrites",
                     kind="val")]
        design.validate_existing(rows)

    def test_shared_export_needs_row_or_justification(self):
        old, shared = design.read_old_rows(), design.read_shared()
        design.validate_completeness(old, shared)
        self.assertIn("simpLib.Cong", shared)
        # A missing row fails.
        rows = [r for r in old if r["old_api"] != "simpLib.SIMP_TAC"]
        with self.assertRaisesRegex(ValueError, "neither row"):
            design.validate_completeness(rows, shared)
        # An allowlisted name passes without a row.
        self.assertNotIn("simpLib.Cong", {r["old_api"] for r in old})
        # An allowlisted name that also has a row is stale.
        stale = dict(shared, **{"boolSimps.BOOL_ss": "x"})
        with self.assertRaisesRegex(ValueError, "has a row"):
            design.validate_completeness(old, stale)
        # An allowlisted name that is not a shared export is stale.
        for api in ["simpLib.threaded_cong_ss", "simpLib.noSuchName"]:
            with self.assertRaisesRegex(ValueError, "not a shared export"):
                design.validate_completeness(old, dict(shared, **{api: "x"}))
        # Removing a justified entry fails.
        short = {k: v for k, v in shared.items() if k != "simpLib.Cong"}
        with self.assertRaisesRegex(ValueError, "neither row"):
            design.validate_completeness(old, short)

    def test_new_extension_pairs_are_covered(self):
        old = design.read_old_rows()
        names = {r["old_api"] for r in old if r["group"] == "F1"}
        for api in ["boolSimps.bool_ss", "combinSimps.COMBIN_ss",
                    "pureSimps.PURE_ss", "intReduce.INT_REDUCE_ss",
                    "listSimps.LIST_EQ_ss", "numSimps.MOD_ss",
                    "pred_setSimps.SET_SPEC_ss", "realSimps.REAL_REDUCE_ss"]:
            self.assertIn(api, names)
        # integer_wordLib shares no name with its extension: the develop
        # and extension namespaced sets are disjoint.
        path = design.MODULES["integer_wordLib"][1]
        self.assertFalse(
            design.namespaced((design.INPUTS / "integer_wordLib.sig")
                              .read_text()) &
            design.namespaced((design.ROOT / path).read_text()))
        rows = [r for r in old if r["old_api"] != "numSimps.MOD_ss"]
        with self.assertRaisesRegex(ValueError, "neither row"):
            design.validate_completeness(rows, design.read_shared())

    def tree(self, temp, *paths):
        root = Path(temp)
        for path in paths:
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text("sig\nend\n")
        return root

    def test_extension_scan_is_git_free_and_by_name(self):
        scanned = design.scan_extension_sigs()
        self.assertEqual(
            set(scanned),
            {path for _, path in design.MODULES.values()})
        # Name-only recognition: decoys never match.
        for name in ["IntExtra", "BoolExtractShared", "ParseExtras",
                     "intExtensionLib", "Extract", "LSPExtension",
                     "GraphExtra"]:
            self.assertIsNone(design.EXT_SIG.fullmatch(name + ".sig"), name)
        for name in ["fooExt", "fooExtLib", "a_bExt"]:
            self.assertTrue(design.EXT_SIG.fullmatch(name + ".sig"), name)

    def test_every_extension_signature_is_covered(self):
        design.validate_extension_coverage()
        # The sanity floor: a scan that finds nothing is not a pass.
        with patch.object(design, "scan_extension_sigs", lambda root: []):
            with self.assertRaisesRegex(ValueError, "not found by"):
                design.validate_extension_coverage()
        with tempfile.TemporaryDirectory() as temp:
            develop = self.tree(temp + "/d", "m.sig")
            root = self.tree(temp + "/r", "src/mExt.sig")
            modules = {"m": ("mExt", "src/mExt.sig")}
            def check(**kwargs):
                design.validate_extension_coverage(
                    root, modules, kwargs.get("excluded", {}), develop)
            check()
            # Unlisted extension signatures fail.
            for path in ["src/fooExt.sig", "src/x/fooExtLib.sig"]:
                self.tree(root, path)
                with self.assertRaisesRegex(ValueError, "not covered"):
                    check()
                # An excluded entry passes, with a reason only.
                check(excluded={path: "no develop counterpart"})
                with self.assertRaisesRegex(ValueError, "without a reason"):
                    check(excluded={path: " "})
                (root / path).unlink()
            # A stale exclusion, whose file is absent, fails.
            with self.assertRaisesRegex(ValueError, "stale exclusion"):
                check(excluded={"src/gone.sig": "r"})
            # Decoys, tests directories and symlinks are ignored.
            self.tree(root, "src/IntExtra.sig", "src/BoolExtractShared.sig",
                      "src/ParseExtras.sig", "src/intExtensionLib.sig",
                      "src/Extract.sig", "src/LSPExtension.sig",
                      "src/GraphExtra.sig", "src/tests/fooExt.sig",
                      ".git/fooExt.sig", ".hol/fooExt.sig")
            (root / "src/linkExt.sig").symlink_to(root / "src/mExt.sig")
            check()
            # MODULES must exist and be pinned.
            (root / "src/mExt.sig").unlink()
            with self.assertRaisesRegex(ValueError, "missing"):
                check()
            self.tree(root, "src/mExt.sig")
            (develop / "m.sig").unlink()
            with self.assertRaisesRegex(ValueError, "no pinned develop"):
                check()

    def test_new_develop_pins_are_base_bytes(self):
        require_revisions(design.BASE)
        listing = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", design.BASE],
            cwd=design.ROOT, capture_output=True, text=True, check=True,
            stdin=subprocess.DEVNULL).stdout.splitlines()
        pins = sorted(design.INPUTS.glob("*.sig"))
        self.assertTrue({m + ".sig" for m in design.MODULES} |
                        {"ThmAttribute.sig"} <= {p.name for p in pins})
        for pin in pins:
            paths = [f for f in listing
                     if f.rsplit("/", 1)[-1] == pin.name and
                     "/tests/" not in "/" + f]
            self.assertEqual(len(paths), 1, pin.name)
            result = subprocess.run(
                ["git", "show", design.BASE + ":" + paths[0]],
                cwd=design.ROOT, capture_output=True, check=True,
                stdin=subprocess.DEVNULL)
            self.assertEqual(pin.read_bytes(), result.stdout, pin.name)

    def test_shared_exports_reject_repeats_and_empty_fields(self):
        original = design.SHARED
        head = "old_api\tjustification\n"
        try:
            with tempfile.TemporaryDirectory() as temp:
                path = Path(temp) / "shared.tsv"
                design.SHARED = path
                path.write_text(head + "a.b\tx\na.b\ty\n")
                with self.assertRaisesRegex(ValueError, "repeated"):
                    design.read_shared()
                for body in ["a.b\t\n", "a.b\t  \n", "a.b\n"]:
                    path.write_text(head + body)
                    with self.assertRaisesRegex(ValueError,
                                                "empty.*justification"):
                        design.read_shared()
                path.write_text(head + "a.b\tx\n")
                self.assertEqual(design.read_shared(), {"a.b": "x"})
        finally:
            design.SHARED = original

    def test_namespaces_are_distinguished(self):
        text = ("sig val runners : int\n type runners\n"
                "datatype t = A | B\n type u\n val u : int\nend")
        self.assertEqual(design.namespaced(text), {
            ("value", "runners"), ("type", "runners"), ("type", "t"),
            ("value", "A"), ("value", "B"), ("type", "u"),
            ("value", "u")})
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "m.sig").write_text("sig type x\nend")
            (root / "mExt.sig").write_text("sig val x : int\nend")
            with patch.object(design, "MODULES",
                              {"m": ("mExt", "mExt.sig")}):
                # A type in one and a value in the other is not shared.
                design.validate_completeness([], {}, root, root)
                (root / "mExt.sig").write_text("sig val x : int\ntype x\nend")
                with self.assertRaisesRegex(ValueError, "neither row"):
                    design.validate_completeness([], {}, root, root)

    def test_namespaced_fails_closed(self):
        for text, why in [
                ("sig structure S : sig end\nend", "structure"),
                ("sig functor F : sig end\nend", "functor"),
                ("sig type t\nsharing type t = u\nend", "sharing"),
                ("sig val a : int\nand b : int\nend", "and"),
                ("sig type t\nand u\nend", "and"),
                ("sig datatype t = A\nand u = B\nend", "and"),
                ("sig exception E\nand F\nend", "and"),
                ("sig eqtype t\nand u\nend", "and")]:
            with self.assertRaisesRegex(ValueError, "unsupported.*" + why):
                design.namespaced(text)
        with self.assertRaisesRegex(ValueError, "unresolved signature"):
            design.namespaced("sig include Nope\nend")
        # Comments hide the keywords; includes resolve through INCLUDES.
        self.assertEqual(
            design.namespaced("sig (* structure and *) val a : int end"),
            {("value", "a")})
        with patch.dict(design.INCLUDES, {"Inc": {("type", "t"),
                                                   ("value", "v")}}):
            self.assertEqual(
                design.namespaced("sig include Inc val a : int end"),
                {("type", "t"), ("value", "v"), ("value", "a")})
            self.assertEqual(
                design.declared("sig include Inc val a : int end"),
                {"t", "v", "a"})

    def test_owner_field_format(self):
        row = dict(group="F1", old_api="boolSimps.bool_ss", kind="val",
                   replacement_api="boolSimpsExt.bool_ss", owners="08,11,13")
        self.assertEqual(design.expected_rows([row])[0]["owners"],
                         "08,11,13;27")
        for owners in ["", "8", "08;27", "08,", "08 11", "x", "08,11,",
                       "13,08", "08,08", "11,08,13"]:
            with self.assertRaisesRegex(ValueError, "malformed owner"):
                design.expected_rows([dict(row, owners=owners)])

    def test_generated_check_is_in_sync(self):
        shared = design.read_shared()
        self.assertEqual(len(shared), 17)
        self.assertEqual(design.SHARED_CHECK.read_text(),
                         design.shared_check_text())
        design.validate_shared_check_file()
        # An entry added to the table makes the committed file stale.
        mutated = dict(shared, **{"simpLib.ssfrag": "x"})
        with patch.object(design, "read_shared", return_value=mutated):
            with self.assertRaisesRegex(ValueError, "stale"):
                design.validate_shared_check_file()

    def test_generated_check_text(self):
        entries = design.shared_entries()
        kinds = [e[0] for e in entries]
        self.assertEqual((kinds.count("type"), kinds.count("value")),
                         (10, 7))
        text = design.SHARED_CHECK.read_text()
        self.assertIn('same_value "simpLib.AC" simpLib.AC simpExtLib.AC',
                      text)
        self.assertIn("fn (v : Opening.congproc) => "
                      "(v : OpeningExt.congproc)", text)
        self.assertIn("fn (v : OpeningExt.congproc) => "
                      "(v : Opening.congproc)", text)
        for entry, want in [
                (("type", "M", "N", "t", "'a"),
                 "fn (v : 'a M.t) => (v : 'a N.t)"),
                (("type", "M", "N", "t", "('a,'b)"),
                 "fn (v : ('a,'b) N.t) => (v : ('a,'b) M.t)")]:
            self.assertIn(want, design.entry_check(entry))
        self.assertIn('same_value "M.x" M.x N.x',
                      design.entry_check(("value", "M", "N", "x", "")))

    def test_type_params_from_the_develop_spec(self):
        for spec, want in [("type t", ""), ("type t=int", ""),
                           ("type 'a t", "'a"), ("eqtype ''a t", "''a"),
                           ("type('a,'b)t", "('a,'b)"),
                           ("datatype 'a t=A of 'a", "'a")]:
            self.assertEqual(design.type_params(spec), want, spec)

    def entry_pair(self, shared, dev, ext):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "m.sig").write_text("sig\n" + dev + "\nend\n")
            (root / "mExt.sig").write_text("sig\n" + ext + "\nend\n")
            with patch.object(design, "MODULES",
                              {"m": ("mExt", "mExt.sig")}):
                return design.shared_entries(shared, root, root)

    def test_entry_prefilters(self):
        self.assertEqual(
            self.entry_pair({"m.x": "j", "m.t": "j"},
                            "val x : int\ntype 'a t",
                            "val x : int\ntype 'a t = 'a list"),
            [("type", "m", "mExt", "t", "'a"),
             ("value", "m", "mExt", "x", "")])
        for shared, dev, ext, why in [
                ({"m.y": "j"}, "val x : int", "val x : int", "no shared"),
                ({"m.x": "j"}, "val x : int", "val x : bool",
                 "distinct specs"),
                ({"m.E": "j"}, "exception E", "exception E", "not a val"),
                ({"m.A": "j"}, "datatype t = A", "datatype t = A",
                 "not a val"),
                ({"m.t": "j"}, "type 'a t", "type t", "arities")]:
            with self.assertRaisesRegex(ValueError, why, msg=str(shared)):
                self.entry_pair(shared, dev, ext)

    def test_live_entry_for_a_distinct_type_passes_the_prefilter(self):
        # The text pre-filter is not the authority: a distinct opaque type
        # is only refused by the compiler, which the negative controls and
        # the build exercise.  The generated text names both types.
        shared = dict(design.read_shared(), **{"simpLib.ssfrag": "x"})
        entries = design.shared_entries(shared)
        self.assertIn("fn (v : simpLib.ssfrag) => (v : simpExtLib.ssfrag)",
                      design.shared_check_text(entries=entries))

    def test_negative_controls_are_generated(self):
        texts = design.negative_shared_texts()
        self.assertEqual(set(texts), set(design.NEGATIVE_SHARED_EXPECT))
        self.assertIn("(v : simpExtLib.ssfrag)",
                      texts["sharedExportsNegType"])
        self.assertIn('same_value "boolSimps.SimpL" boolSimps.SimpL '
                      "boolSimpsExt.SimpL", texts["sharedExportsNegValue"])
        for text in texts.values():
            self.assertTrue(text.startswith(design.CHECK_HEAD))
            self.assertEqual(text.count("SHARED_EXPORTS_CHECK_OK"), 1)

    def test_output_validation(self):
        entries = design.shared_entries()
        ok = "".join("shared export ok: %s%s.%s\n" % (
            "type " if e[0] == "type" else "", e[1], e[3])
            for e in entries) + "SHARED_EXPORTS_CHECK_OK entries=17\n"
        design.validate_shared_output(ok, entries)
        for bad in [ok.replace("SHARED_EXPORTS_CHECK_OK", "x"),
                    ok.replace("entries=17", "entries=16"),
                    ok.replace("shared export ok: simpLib.AC\n", ""),
                    ok + "SHARED_EXPORT_FAILED: x\n"]:
            with self.assertRaises(ValueError):
                design.validate_shared_output(bad, entries)

    def test_build_wiring_lists_every_checked_module(self):
        text = (design.ROOT / "src/simp/src/Holmakefile").read_text()
        start = text.index("\ninterfaces-design-check:")
        recipe = text[start:text.index("\n\t", start)]
        modules = {m for e in design.shared_entries() for m in e[1:3]}
        modules |= {"boolSimps", "boolSimpsExt"}
        for module in modules:
            self.assertRegex(recipe, rf"\b{module}\.uo\b")
        make = (design.HERE / "Holmakefile").read_text()
        self.assertIn("./sharedExportsCheck.exe", make)

    def test_validate_table_runs_every_validator(self):
        design.validate_table(self.table)
        for name in ["validate_existing", "validate_extension_coverage",
                     "validate_completeness", "validate_entries",
                     "validate_shared_check_file"]:
            with patch.object(design, name,
                              side_effect=ValueError("x-" + name)):
                with self.assertRaisesRegex(ValueError, "x-" + name):
                    design.validate_table(self.table)

    def test_main_reaches_validate_table(self):
        out = io.StringIO()
        with patch.object(design, "validate_table",
                          return_value=275) as table, \
                patch.object(sys, "argv", ["check_design.py"]), \
                contextlib.redirect_stdout(out):
            design.main()
        table.assert_called_once()
        self.assertEqual(json.loads(out.getvalue())["api_decisions"], 275)
        with patch.object(design, "validate_table",
                          side_effect=ValueError("x-table")), \
                patch.object(sys, "argv", ["check_design.py"]):
            with self.assertRaisesRegex(ValueError, "x-table"):
                design.main()

    def test_excluded_entry_in_modules_fails(self):
        path = design.MODULES["Traverse"][1]
        with self.assertRaisesRegex(ValueError, "is in MODULES"):
            design.validate_extension_coverage(
                excluded={path: "no develop counterpart"})

    def test_scan_ignores_dot_dirs_sigobj_and_tests(self):
        path = design.MODULES["Traverse"][1]
        source = design.ROOT / path
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for where in [".agent-files/x", ".hol/x", ".other/x",
                          "src/sigobj", "sigobj", "a/tests", "tests",
                          "src/.hidden"]:
                (root / where).mkdir(parents=True)
                shutil.copyfile(source, root / where / "TraverseExt.sig")
            self.assertEqual(design.scan_extension_sigs(root), [])
            (root / "src").mkdir(exist_ok=True)
            shutil.copyfile(source, root / "src/TraverseExt.sig")
            self.assertEqual(design.scan_extension_sigs(root),
                             ["src/TraverseExt.sig"])

    def test_spec_normalisation(self):
        norm = design.normalise
        self.assertEqual(norm("val  x : a ->  b ;"), norm("val x:a->b"))
        self.assertEqual(norm("type t = { a : int , b : bool }"),
                         norm("type t={a:int,b:bool}"))
        self.assertEqual(norm("val f : (a * b) -> c"),
                         norm("val f:(a*b)->c"))
        self.assertNotEqual(norm("val f : a -> b"), norm("val f : b -> a"))
        old = "sig val x : int * bool ->\n int ; val y : int end"
        new = "sig val x:int*bool->int val y : int end"
        self.assertEqual(design.parse_specs(old)[0][1],
                         design.parse_specs(new)[0][1])

    def test_parser_gaps(self):
        self.assertEqual(
            design.parse_specs("sig type ''a t = ''a list end"),
            ((("type", "t"), "type ''a t=''a list"),))
        self.assertEqual(
            design.parse_specs("sig type ''a t end")[0][0], ("type", "t"))
        for text, why in [
                ("sig type t\nwithtype u = int\nend", "withtype"),
                ("sig include A where type t = int\nend", "where"),
                ("sig abstype t = A with end\nend", "abstype")]:
            with self.assertRaisesRegex(ValueError, "unsupported.*" + why):
                design.parse_specs(text)
        with patch.dict(design.INCLUDES, {"A": {("type", "a")},
                                          "B": {("type", "b")}}):
            self.assertEqual(
                design.namespaced("sig include A B val v : int end"),
                {("type", "a"), ("type", "b"), ("value", "v")})
            self.assertEqual(
                design.namespaced("sig include A\n B\nend"),
                {("type", "a"), ("type", "b")})
            with self.assertRaisesRegex(ValueError, "unresolved.*C"):
                design.namespaced("sig include A C val v : int end")
        # The live signatures still parse.
        design.validate_extension_coverage()
        for module, (_, path) in design.MODULES.items():
            design.parse_specs((design.ROOT / path).read_text())
            design.parse_specs(
                (design.INPUTS / (module + ".sig")).read_text())

    def test_receipt_hashes_the_verdict_inputs(self):
        paths = design.source_paths()
        names = {p.name for p in paths}
        for _, path in design.MODULES.values():
            self.assertIn(design.ROOT / path, paths)
        for name in ["boolSimpsExt.sig", "realSimpsExt.sig",
                     "boolSimpsExt.sml", "ThmAttribute.sig",
                     "simpMarkerLib.sig", "splitLib.sig", "SplitData.sig",
                     "shared-exports.tsv", "apis.tsv", "final-apis.tsv",
                     "check_task27_docs.py", "check_design.py",
                     "Cond_rewr.sig", "boolSimps.sig", "realSimps.sig"]:
            self.assertIn(name, names)
        self.assertIn(design.SHARED_CHECK, paths)
        self.assertFalse((design.INPUTS / "simpLib.sml").exists())
        self.assertNotIn("prior-streams.json.gz", names)

    def test_missing_api_is_not_a_pass(self):
        lines = self.table.splitlines(keepends=True)
        with self.assertRaisesRegex(ValueError, "missing/stale"):
            design.validate_table("".join(lines[:-1]))

    def test_changed_construction_is_not_a_pass(self):
        rows = design.expected_rows()
        rows[0]["construction"] = ""
        with self.assertRaisesRegex(ValueError, "missing/stale"):
            design.validate_table(design.table_text(rows))

    def test_export_must_belong_to_its_prototype_module(self):
        original = Path.read_text
        def missing(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if path.name == "Task08API.sml":
                text = text.replace(
                    "    val dproc_ss : T.reducer -> ssfrag\n", "")
                text += "\n(* val dproc_ss exists only outside S *)\n"
            return text
        with patch.object(Path, "read_text", missing):
            with self.assertRaisesRegex(ValueError, "missing scoped"):
                design.validate_table(self.table)

    def test_external_rows_require_typed_provider_not_fake_exports(self):
        original = Path.read_text
        def missing(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            return text.replace("    type provider\n", "")
        with patch.object(Path, "read_text", missing):
            with self.assertRaisesRegex(ValueError, "typed external provider"):
                design.validate_table(self.table)

    def test_final_graph_and_all_cutovers(self):
        order = design.validate_graph(self.graph)
        self.assertEqual(len(order), len(self.graph["nodes"]))
        self.assertLess(order.index("Cond_rewr"),
                        order.index("Cond_rewrExt"))
        self.assertLess(order.index("simpExtLib"), order.index("boolSimpsExt"))

    def test_recipe_cycle_is_rejected(self):
        self.graph["nodes"]["simpExtLib"]["imports"].append("boolSimpsExt")
        with self.assertRaisesRegex(ValueError, "cycle"):
            design.validate_graph(self.graph)

    def test_indirect_ordinary_extension_import_rejected(self):
        self.graph["nodes"]["Trace"]["imports"].append("simpMarkerTheory")
        with self.assertRaisesRegex(ValueError, "reaches extension"):
            design.validate_graph(self.graph)

    def test_unbounded_transition_is_rejected(self):
        for edge in self.graph["transitional_edges"]:
            graph = copy.deepcopy(self.graph)
            graph["transitional_edges"][0]["remove"] = 27
            with self.assertRaisesRegex(ValueError, "unbounded"):
                design.validate_graph(graph)
            self.assertIn(edge["remove"], {12, 13, 16})

    def test_missing_module_availability_is_rejected(self):
        self.graph["introduced_nodes"].pop("Cond_rewrExt")
        with self.assertRaisesRegex(ValueError, "module-availability"):
            design.validate_graph(self.graph)

    def test_missing_transition_is_rejected(self):
        self.graph["transitional_edges"].pop()
        with self.assertRaisesRegex(ValueError, "missing transitional"):
            design.validate_graph(self.graph)

    def test_missing_cutover_is_rejected(self):
        self.graph["cutovers"].remove(14)
        with self.assertRaisesRegex(ValueError, "missing structural"):
            design.validate_graph(self.graph)

    def good_output(self):
        return "\n".join(
            ["TASK08_COMPLETE checks=29"] +
            ["static rejection: " + n + " ..." for n in design.NEGATIVES] +
            ["TASK08_LOADED " + str(design.HERE / n) for n in
             ["Task08API", "Task08TraverseExt", "Task08ReducerTypes",
              "Task08Clients", "Task08Cutovers", "Task08Controls",
              "Task08Reducers"]])

    def test_complete_output_only(self):
        design.validate_output(0, self.good_output())
        for code, output in [(1, self.good_output()), (0, ""),
                             (0, self.good_output() * 2)]:
            with self.assertRaisesRegex(ValueError, "incomplete/failed"):
                design.validate_output(code, output)

    def test_missing_static_case_is_rejected(self):
        text = self.good_output().replace(
            "static rejection: set-to-legacy", "oops")
        with self.assertRaisesRegex(ValueError, "missing static"):
            design.validate_output(0, text)

    def test_stale_module_path_is_rejected(self):
        text = self.good_output().replace(str(design.HERE), "/stale")
        with self.assertRaisesRegex(ValueError, "private module"):
            design.validate_output(0, text)


if __name__ == "__main__":
    unittest.main()
