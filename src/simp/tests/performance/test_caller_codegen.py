"""Caller-codegen guards; synthetic listings are not measurement evidence."""
import gzip
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

import caller_codegen as c
from performance_schema import suite_options


BODY = ("fn() (* \"Fixture.run(1)\" *) => Constant 7\n"
        "Fixture.run(1)\n"
        "BEGINFUNCTION 0\n"
        "Fixture.run(1):\n"
        "000000  D100237B  sub x27,x27,#8\n"
        "000004  D65F03C0  ret\n")


def listing(names=c.TARGETS):
    lines, event = [], 0
    for name in names:
        path = "/private/" + name
        lines += [f"@@PAIR\t{event}\tuse\t{path}\n",
                  f"{c.MARKER}begin\t{path}\n", BODY,
                  f"{c.MARKER}end\t{path}\n",
                  f"@@PAIR\t{event+1}\tused\t{path}\n"]
        event += 2
    return "".join(lines)


class CallerCodegenTests(unittest.TestCase):
    def test_exact_private_loader_transform(self):
        original = (c.COMPAT / "paired/runner.sml").read_text()
        helper = (c.HERE / "CallerCodegen.sml").read_text()
        result = c.instrument_runner(original, helper)
        self.assertEqual(result.replace("open Paired\n" + helper + "\n",
            "open Paired\n").replace("    codegenUse path;\n",
            "    Meta.qquse path;\n"), original)
        for old in (original.replace("Meta.qquse path", "other path"),
                    original + "    Meta.qquse path;\n",
                    original.replace("open Paired\n", "")):
            with self.assertRaises(ValueError):
                c.instrument_runner(old, helper)

    def test_extents_and_every_repeated_pass(self):
        text = listing()
        spans = c.extents(text, Path("/private"), [])
        self.assertEqual(set(spans), set(c.TARGETS))
        span = spans["MatrixSupport.sml"]
        lines = text.splitlines(keepends=True)
        self.assertEqual("".join(lines[span["stdout_start_line"]-1:
                                            span["stdout_end_line"]]), BODY)
        span["text"] *= 2
        rows = c.records(span)
        self.assertEqual([r["kind"] for r in rows],
                         ["optimized-tree", "icode", "assembly"] * 2)
        self.assertEqual([r["occurrence"] for r in rows], [1, 1, 1, 2, 2, 2])
        self.assertEqual(rows[2]["static"]["allocation_reservations"],
                         ["sub x27,x27,#8"])
        self.assertEqual(rows[2]["body"], BODY[BODY.index("Fixture.run(1):"):])

    def test_optional_source_bound_to_actual_inventory(self):
        names = c.TARGETS + c.OPTIONAL
        c.extents(listing(names), Path("/private"), c.OPTIONAL)
        with self.assertRaisesRegex(ValueError, "inventory"):
            c.extents(listing(names), Path("/private"), [])
        with self.assertRaisesRegex(ValueError, "inventory"):
            c.extents(listing(), Path("/private"), c.OPTIONAL)

    def test_loss_duplicate_nesting_nonprivate_abort_and_trace_faults(self):
        text = listing()
        marker = c.MARKER
        mutations = [
            text.replace(marker + "begin", marker + "aborted", 1),
            text.replace(marker + "end", marker + "aborted", 1),
            text.replace(marker + "end", marker + "begin", 1),
            text.replace(marker + "begin\t/private/Cond_rewr.sml\n", "", 1),
            text.replace(marker + "end\t/private/Cond_rewr.sml\n", "", 1),
            text.replace("/private/Cond_rewr.sml", "/shared/Cond_rewr.sml"),
            text.replace("/private/Cond_rewr.sml", "/private/Unknown.sml"),
            text.replace("\tuse\t", "\tused\t", 1),
            text.replace("\tused\t", "\tuse\t", 1),
            text.replace(marker, "x" + marker, 1),
            text.replace(BODY, "", 1),
            text[:-1],
            listing(c.TARGETS[:-1]),
        ]
        for mutant in mutations:
            with self.subTest(mutant=mutant[:80]):
                with self.assertRaises(ValueError):
                    c.extents(mutant, Path("/private"), [])
        # Duplicate spans with fresh event numbers, not just bad numbering.
        duplicate = text + listing(("Cond_rewr.sml",)).replace(
            "@@PAIR\t0", "@@PAIR\t10").replace("@@PAIR\t1\t", "@@PAIR\t11\t")
        with self.assertRaisesRegex(ValueError, "uniquely|duplicate"):
            c.extents(duplicate, Path("/private"), [])

    def test_optional_optimizer_absence_is_not_fabricated(self):
        text = BODY[BODY.index("Fixture.run(1)\n"):]
        span = dict(text=text, stdout_start_line=1)
        with self.assertRaisesRegex(ValueError, "representation"):
            c.records(span)
        rows = c.records(span, require_optimized=False)
        self.assertEqual([r["kind"] for r in rows], ["icode", "assembly"])

    def test_missing_representation_and_bad_native_encoding(self):
        for text in (BODY.split("Fixture.run(1):")[0],
                     BODY[BODY.index("Fixture.run(1):"):],
                     BODY.replace("000004", "000008"),
                     BODY.replace("D65F03C0", "BADWORD!")):
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    c.records(dict(text=text, stdout_start_line=1))

    def test_no_literal_or_inventory_parity_shortcut(self):
        def rec(text):
            return c.records(dict(text=text, stdout_start_line=1))
        aa = rec(BODY)
        bb = rec(BODY.replace("Constant 7", "Constant 8"))
        rows = c.compare(aa, bb)
        self.assertFalse(rows[0]["exact_printed_text_equal"])
        self.assertTrue(rows[-1]["exact_printed_text_equal"])
        self.assertTrue(all(not r["exact_printed_text_equal"]
                            for r in c.compare(aa, [])))
        native = BODY.replace("sub x27,x27,#8", "sub x27,x27,#16")
        self.assertFalse(c.compare(aa, rec(native))[-1][
            "instruction_text_equal_after_pool_relocation"])

    def test_raw_output_kept_before_rejected_parser_and_hooks_restored(self):
        install, compact = c.paired.install_fixtures, c.paired.compact
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            report = {"stdout": {}}
            text = listing().replace("\tend\t", "\taborted\t", 1)
            receipt = dict(fixture="performance", stdout=text, accepted=True,
                selection="baseline", environment={"PAIR_PRIVATE": "/private"})
            with self.assertRaises(ValueError):
                with c.diagnostic_loader(output, report):
                    c.paired.compact(receipt, output, "failed")
            self.assertIs(c.paired.compact, compact)
            self.assertIs(c.paired.install_fixtures, install)
            path = output / "failed.stdout.txt.gz"
            self.assertEqual(gzip.decompress(path.read_bytes()).decode(), text)
            self.assertEqual(report["stdout"]["failed"]["uncompressed_sha256"],
                             c.paired.digest(text.encode()))
            with self.assertRaises(ValueError):
                c.archive_stdout(output, "failed", text)

    def test_duplicate_compiler_dump_removed_without_losing_raw_output(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            text = listing() + "@@MATRIX_RUNTIME\t{}\n"
            report = {"stdout": {}}
            receipt = dict(fixture="performance", stdout=text, accepted=True,
                selection="baseline", environment={"PAIR_PRIVATE": "/private"},
                stdout_sha256=c.paired.digest(text.encode()),
                stdout_bytes=len(text.encode()))
            with c.diagnostic_loader(output, report):
                c.paired.compact(receipt, output, "pair-00-baseline")
            raw = json.loads(gzip.decompress(
                (output / "pair-00-baseline.json.gz").read_bytes()))
            self.assertEqual(raw["diagnostics"], ["@@MATRIX_RUNTIME\t{}"])
            info = raw["compiler_stdout"]
            self.assertNotIn("diagnostic_accepted", info)
            self.assertEqual(gzip.decompress(
                (output / info["file"]).read_bytes()).decode(), text)
            self.assertEqual(raw["stdout_sha256"], info["uncompressed_sha256"])
            self.assertEqual(raw["stdout_bytes"], info["uncompressed_bytes"])

    def test_diagnostic_cannot_enter_timing_acceptance(self):
        with self.assertRaisesRegex(ValueError, "unknown performance suite"):
            suite_options({"suite": "caller-codegen-diagnostic"})

    @unittest.skipUnless(os.environ.get("CALLER_CODEGEN_EVIDENCE"),
                         "requires real diagnostic archive")
    def test_real_archive_replay_and_mutations(self):
        root = Path(os.environ["CALLER_CODEGEN_EVIDENCE"])
        source = root / "baseline-candidate"
        repo = c.HERE.parents[3]
        summary = c.replay_report(source, repo)
        self.assertEqual(summary["MatrixSupport.sml"]["native_bodies"], 885)
        with tempfile.TemporaryDirectory() as temp:
            dst = Path(temp) / "archive"
            for mutation, reason in (
                    ("comparison", "comparison changed"),
                    ("source", "selected source differs from Git"),
                    ("loader", "wrong diagnostic loader"),
                    ("fixture", "private source/hash mismatch"),
                    ("trace", "proof trace mismatch"),
                    ("marker", "compiler extent"),
                    ("inventory", "process inventory")):
                with self.subTest(mutation=mutation):
                    shutil.copytree(source, dst)
                    try:
                        rp = dst / "report.json.gz"
                        report = json.loads(gzip.decompress(rp.read_bytes()))
                        mp = dst / "paired/manifest.json"
                        manifest = json.loads(mp.read_text())
                        selected = manifest["selections"]["candidate"]
                        if mutation == "comparison":
                            row = report["comparison"]["MatrixSupport.sml"][0]
                            row["exact_printed_text_equal"] = not row[
                                "exact_printed_text_equal"]
                        elif mutation == "source":
                            selected["sources"][0]["sha256"] = "0" * 64
                        elif mutation in ("loader", "fixture"):
                            name = ("runner.sml" if mutation == "loader"
                                    else "MatrixSupport.sml")
                            selected["fixture_products"][name]["sha256"] = (
                                "0" * 64)
                        elif mutation == "trace":
                            path = dst / "paired/pair-00-candidate.json.gz"
                            raw = json.loads(gzip.decompress(path.read_bytes()))
                            raw["result"]["events"].pop()
                            path.write_bytes(gzip.compress(
                                json.dumps(raw).encode(), mtime=0))
                        elif mutation == "marker":
                            info = report["stdout"]["pair-00-candidate"]
                            path = dst / info["file"]
                            raw = gzip.decompress(path.read_bytes()).replace(
                                b"@@CALLER_CODEGEN\tend\t",
                                b"@@CALLER_CODEGEN\taborted\t", 1)
                            path.write_bytes(gzip.compress(raw, mtime=0))
                            info.update(c.paired.fingerprint(path),
                                uncompressed_sha256=c.paired.digest(raw),
                                uncompressed_bytes=len(raw))
                            path = dst / "paired/pair-00-candidate.json.gz"
                            receipt = json.loads(gzip.decompress(
                                path.read_bytes()))
                            receipt["stdout_sha256"] = c.paired.digest(raw)
                            receipt["stdout_bytes"] = len(raw)
                            receipt["compiler_stdout"] = {k: v for k, v in
                                info.items() if k not in ("extents",
                                    "process_accepted", "diagnostic_accepted")}
                            path.write_bytes(gzip.compress(
                                json.dumps(receipt).encode(), mtime=0))
                        else:
                            report["stdout"].pop("pair-00-candidate")
                        mp.write_text(json.dumps(manifest) + "\n")
                        report["paired_manifest"] = c.paired.fingerprint(mp)
                        rp.write_bytes(gzip.compress(
                            json.dumps(report).encode(), mtime=0))
                        with self.assertRaisesRegex(ValueError, reason):
                            c.replay_report(dst, repo)
                    finally:
                        shutil.rmtree(dst)

    def test_authorization_before_creating_output(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "no-output"
            with self.assertRaisesRegex(ValueError, "authorization"):
                c.main(["--output", str(output)])
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
