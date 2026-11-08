"""Unit/mutation tests for the documentation gate; no HOL process started.

  python3 -B -m unittest discover -s src/simp/tests/compatibility \
      -p test_task27_docs.py
"""

from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock

import check_task27_docs as gate


class SignatureTests(unittest.TestCase):
    def test_nested_comments_strings_and_type_parameters(self):
        text = '''signature Example = sig
          (* val fake : unit (* type hidden *) *)
          type 'a box
          eqtype ('a, 'b) pair
          datatype reducer = LIFTED of Ordinary.reducer
                           | CONFIG of {apply : unit -> unit}
          val ++ : int * int -> int
          exception Abort of string
        end'''
        self.assertEqual(gate.signature_symbols(text),
                         {"box", "pair", "reducer", "LIFTED", "CONFIG",
                          "++", "Abort"})
        masked = gate.strip_sml_comments(
            'val x : string (* " *)\nval y : unit\n"(*not comment*)"')
        self.assertIn("val y", masked)
        self.assertNotIn("not comment", masked)
        self.assertEqual(masked.count("\n"), 2)

    def test_unclosed_comment_fails(self):
        with self.assertRaises(ValueError):
            gate.signature_symbols("(* broken")

    def test_include_is_explicit(self):
        self.assertEqual(gate.signature_symbols(
            "sig include Abbrev type fresh end", {"Abbrev": {"term"}}),
            {"term", "fresh"})
        with self.assertRaises(ValueError):
            gate.signature_symbols("sig include Unknown end")

    def test_actual_constructor_and_type_exports(self):
        symbols = gate.signature_symbols(
            (gate.ROOT / gate.SIGNATURES["TraverseExt"]).read_text(),
            {"Abbrev": {"conv"}})
        self.assertTrue({"CONFIG_REDUCER", "CONTEXT_REDUCER", "LIFTED",
                         "ParentFirst", "ChildFirst", "reducer",
                         "simp_prover_ctxt", "xtraverse_data"} <= symbols)
        self.assertNotIn("REDUCER", symbols)
        self.assertNotIn("apply", symbols)  # record field, not qualified API


class ReferenceTests(unittest.TestCase):
    def setUp(self):
        self.symbols = {m: set() for m in gate.SIGNATURES}
        self.symbols["simpLib"] = {"simpset", "SSFRAG", "++"}
        self.symbols["TraverseExt"] = {"CONFIG_REDUCER", "xtraverse_data"}

    def scan(self, text, path="help/Docfiles/example.smd"):
        return gate.scan_references(text, self.symbols, path)

    def test_values_types_constructors_and_unknowns(self):
        valid, unknown, _ = self.scan(
            "simpLib.SSFRAG simpLib.simpset TraverseExt.CONFIG_REDUCER "
            "TraverseExt.xtraverse_data simpLib.no_such_api")
        self.assertEqual(len(valid), 4)
        self.assertEqual([r["reference"] for r in unknown],
                         ["simpLib.no_such_api"])

    def test_doc_declarations_do_not_define_exports(self):
        _, unknown, _ = self.scan(
            "simpLib.fake : simpLib.missing_type\n"
            "val simpLib.fake = fn x => x")
        self.assertEqual(len(unknown), 3)

    def test_operator_markdown_and_encoded_link(self):
        valid, unknown, _ = self.scan(
            "`simpLib.++` [plus](#simpLib..KAL)")
        self.assertEqual(len(valid), 2)
        self.assertFalse(unknown)
        self.assertEqual({r["reference"] for r in valid}, {"simpLib.++"})

    def test_file_mentions_and_private_names_not_apis(self):
        valid, unknown, excluded = self.scan(
            "simpLib.sml simpLib.sig simpLib.*.smd "
            "`splitLib.persistent.rules.v1` simpLib.ssfragDB")
        self.assertFalse(valid)
        self.assertFalse(unknown)
        self.assertEqual(len(excluded), 2)
        # Prefix exceptions must not hide genuine unknown references.
        _, unknown, _ = self.scan("splitLib.persistent.rules.v1.fake")
        self.assertEqual(unknown[0]["reference"], "splitLib.persistent")

    def test_only_old_table_column_is_historical(self):
        text = ("| Earlier branch use | Final module/type/construction |\n"
                "| `simpLib.removed` | `TraverseExt.CONFIG_REDUCER` |\n"
                "| `simpLib.removed` | `simpLib.new_fake` |\n")
        valid, unknown, excluded = self.scan(text, "src/simp/src/notes.md")
        self.assertEqual(len(valid), 1)
        self.assertEqual([r["reference"] for r in unknown],
                         ["simpLib.new_fake"])
        self.assertEqual(len(excluded), 2)
        _, unknown, _ = self.scan(text)
        self.assertEqual(len(unknown), 3)  # no blanket historical exemption

    def test_title_comes_from_signature_not_docfile(self):
        self.assertTrue(gate.docfile_title_errors(
            "simpLib.fake.smd", "## `fake`\nsimpLib.fake : unit",
            self.symbols))
        self.assertFalse(gate.docfile_title_errors(
            "simpLib..KAL.smd", "title: simpLib.++\n## `++`\n",
            self.symbols))
        self.assertTrue(gate.docfile_title_errors(
            "simpLib.SSFRAG.smd", "title: simpLib.simpset\n## `simpset`",
            self.symbols))


class CurrentDocsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = gate.check_docs()

    def test_actual_final_documents(self):
        self.assertEqual(self.report["errors"], [])
        self.assertEqual(self.report["unknown_references"], [])
        self.assertGreater(self.report["signature_references"], 750)
        self.assertGreater(len(self.report["doc_sha256"]), 70)
        self.assertTrue(set(gate.CURRENT_DOCS) <=
                        self.report["doc_sha256"].keys())
        self.assertTrue(all("compatibility/migration" not in p for p in
                            self.report["doc_sha256"]))

    def fixture(self):
        temporary = tempfile.TemporaryDirectory(prefix="task27-docs-test-")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        for name in (set(self.report["signature_sha256"]) |
                     set(self.report["doc_sha256"])):
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(gate.ROOT / name, target)
        return root

    def test_unknown_declaration_and_title_mutations(self):
        root = self.fixture()
        fake = root / "help/Docfiles/simpLib.transparent_promote.smd"
        fake.write_text("## `transparent_promote`\n"
                        "simpLib.transparent_promote : simpLib.simpset")
        report = gate.check_docs(root)
        self.assertTrue(any("unknown docfile title" in e
                            for e in report["errors"]))
        self.assertTrue(any(r["reference"] == "simpLib.transparent_promote"
                            for r in report["unknown_references"]))

    def test_stale_removed_docfile_mutation(self):
        root = self.fixture()
        for name in gate.REMOVED_DOCS:
            (root / name).write_text("## `removed`\n")
        errors = gate.check_docs(root)["errors"]
        self.assertEqual(sum("removed docfile still exists" in e
                             for e in errors), 3)

    def test_signature_removal_is_detected(self):
        root = self.fixture()
        path = root / gate.SIGNATURES["TraverseExt"]
        path.write_text(path.read_text().replace("CONFIG_REDUCER", "REMOVED"))
        report = gate.check_docs(root)
        self.assertTrue(any(r["reference"] == "TraverseExt.CONFIG_REDUCER"
                            for r in report["unknown_references"]))

    def test_transparent_promotion_and_dispatch_claim_mutations(self):
        root = self.fixture()
        for name, claims in gate.SENTINELS.items():
            path = root / name
            # Normalize whitespace, then remove precisely each reviewed claim.
            text = " ".join(path.read_text().split())
            for claim in claims:
                self.assertIn(claim, text)
                text = text.replace(claim, "ordinary tactics promote/dispatch")
            path.write_text(text)
        errors = gate.check_docs(root)["errors"]
        self.assertEqual(sum("missing reviewed sentinel" in e for e in errors),
                         sum(map(len, gate.SENTINELS.values())))

    def test_historical_ledger_is_not_an_input(self):
        root = self.fixture()
        ledger = root / "src/simp/tests/compatibility/migration/TASK07.md"
        ledger.parent.mkdir(parents=True)
        ledger.write_text("simpLib.removed Traverse.CONFIG_REDUCER")
        self.assertFalse(gate.check_docs(root)["unknown_references"])


class ExecutionTests(unittest.TestCase):
    def test_prior_selection_and_independent_counts(self):
        self.assertEqual(len(gate.SELECTED_DOCS), 48)
        self.assertEqual(len(set(gate.SELECTED_DOCS)), 48)
        self.assertEqual(len(gate.INDEPENDENT_DOCS), 30)
        self.assertTrue(set(gate.INDEPENDENT_DOCS) <=
                        set(gate.SELECTED_DOCS))
        for name in gate.SELECTED_DOCS:
            self.assertTrue((gate.ROOT / "help/Docfiles" / name).is_file())
        self.assertIn('load "listTheory"', gate.PRELUDE)

    def test_swallowed_static_failure_is_not_success(self):
        for text in ("Exception- Fail \"Static Errors\" raised",
                     "error: Value foo has not been declared"):
            self.assertTrue(gate.processed_errors(text))
        self.assertFalse(gate.processed_errors("Exception- HOL_ERR raised"))

    def test_recipe_runs_48_together_and_30_independently(self):
        def fake_process(command, **kwargs):
            if "buildheap" in command:
                Path(command[command.index("-o") + 1]).touch()
            else:
                source, dest = map(Path, command[-2:])
                dest.mkdir()
                for path in source.glob("*.smd"):
                    (dest / path.name).write_text("processed successfully\n")
                kwargs["stdout"].write("...polyscripter pass done\n")
            return mock.Mock(returncode=0)

        with tempfile.TemporaryDirectory(prefix="task27-docs-output-") as tmp:
            with mock.patch.object(gate.subprocess, "run", fake_process):
                report = gate.execute_examples(gate.ROOT, Path(tmp) / "result")
            self.assertTrue(report["ok"])
            self.assertEqual(report["combined"]["processed_count"], 48)
            self.assertEqual(len(report["runs"]), 30)
            self.assertTrue(all(receipt["sha256"]
                                for receipt in report["runs"]))
            self.assertTrue((Path(tmp) / "result" /
                             "processed-receipts.tar.gz").is_file())

    def test_failed_build_keeps_recipe_and_cleans_scratch(self):
        with tempfile.TemporaryDirectory(prefix="task27-docs-output-") as tmp:
            output = Path(tmp) / "result"
            # This test exercises recipe/evidence/cleanup, not a HOL build.
            with mock.patch.object(gate.subprocess, "run") as run:
                run.return_value.returncode = 1
                report = gate.execute_examples(gate.ROOT, output)
            self.assertFalse(report["ok"])
            self.assertEqual((output / "prelude.sml").read_text(),
                             gate.PRELUDE)
            self.assertTrue((output / "execution.json").is_file())
            self.assertIn("buildheap", report["build"]["command"])
            self.assertIn("<scratch>/prelude.sml", report["build"]["command"])
            self.assertEqual(report["runtime_options"], [])
            command = run.call_args.args[0]
            prelude = next(Path(p) for p in command
                           if p.endswith("/prelude.sml"))
            self.assertFalse(prelude.parent.exists())
            self.assertIsNone(run.call_args.kwargs.get("input"))



class ExportClaimTests(unittest.TestCase):
    """Develop's Cond_rewr.sig does not export is_var_perm (TASK_31 keeps
    the pure copy in Cond_rewrExt), so no live document may say it does.
    Sealed history (migration/TASK*.md, EXTERNAL.md, handoffs, evidence,
    references.tsv) records what was true when written and is not input."""

    LIVE = (
        "src/simp/src/notes.md", "src/simp/src/MANIFEST", "src/simp/README",
        "src/simp/tests/compatibility/README.md",
        "src/simp/tests/compatibility/interfaces/DESIGN.md",
        "src/simp/tests/compatibility/interfaces/CUTOVERS.md",
        "src/simp/tests/compatibility/migration/MIGRATION.md",
        "src/simp/tests/compatibility/migration/IDENTITIES.md",
        "src/simp/tests/compatibility/migration/final-apis.tsv",
        "src/simp/tests/cond-rewr-ext/README.md",
        "src/simp/tests/fragments/README.md")
    # Phrases that deny the export, and the one mapping row of
    # final-apis.tsv that names the old symbol beside its replacement.
    DENIAL = ("no longer exported", "not exported", "unexported",
              "does not export", "absent from pinned",
              "R1\tCond_rewr.is_var_perm\tCond_rewrExt.is_var_perm\t")
    CLAIM = "Cond_rewr.is_var_perm"

    def test_signature_does_not_export_it(self):
        symbols = gate.signature_symbols(
            (gate.ROOT / gate.SIGNATURES["Cond_rewr"]).read_text(),
            {"Abbrev": set()})
        self.assertNotIn("is_var_perm", symbols)
        self.assertIn("note_rewrite", symbols)

    def test_no_live_document_claims_the_export(self):
        for name in self.LIVE:
            with self.subTest(document=name):
                text = (gate.ROOT / name).read_text()
                self.assertTrue(self.claims(text) == [], self.claims(text))

    def claims(self, text):
        return [line for line in text.splitlines()
                if self.CLAIM in line and
                not any(d in line for d in self.DENIAL)]

    def test_detector_catches_a_claim(self):
        self.assertEqual(self.claims(
            "is_var_perm remains exported: Cond_rewr.is_var_perm\n"
            "Cond_rewr.is_var_perm is no longer exported\n"), [
            "is_var_perm remains exported: Cond_rewr.is_var_perm"])


if __name__ == "__main__":
    unittest.main()
