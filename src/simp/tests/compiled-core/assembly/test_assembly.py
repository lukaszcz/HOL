"""TASK16 parser/diff sensitivity controls; no compiler or timing runs."""
import gzip
import json
from pathlib import Path
import unittest
import run_assembly as core


def body(*rows):
    return "simpLib.appconv(1):\n" + "".join(
        f"{i * 4:06X}  00000001        {asm}\n"
        for i, asm in enumerate(rows))


class AssemblyTests(unittest.TestCase):
    def test_real_differences_survive(self):
        for x, y in (("ldr x0,[x8,#16]", "ldr x0,[x8,#24]"),
                     ("sub x9,x27,#72", "sub x9,x27,#80"),
                     ("blr x16", "blr x17"),
                     ("b.cs 0x20", "b.cs 0x24")):
            self.assertNotEqual(core.audit.normalized(body(x)),
                                core.audit.normalized(body(y)))
        self.assertNotEqual(core.audit.normalized(body("ret x30")),
            core.audit.normalized(body("blr x16", "ret x30")))

    def test_pool_only(self):
        a = body("adrp x9,0x0", "ldr x0,[x9,#832]", "ret x30")
        b = body("adrp x9,0x1000", "ldr x0,[x9,#904]", "ret x30")
        self.assertEqual(core.audit.normalized(a), core.audit.normalized(b))
        with self.assertRaises(core.paired.InvalidRun):
            core.audit.normalized(body("adrp x9,0x0"))

    def test_counts_not_allocation_measurements(self):
        counts = core.audit.counts(body("sub x9,x27,#72", "blr x16",
                                       "[x0, x1]", "ret x30", "?"))
        self.assertEqual((counts["instructions"], counts["calls"],
                          counts["gc_maps"], counts["padding"]), (3, 1, 1, 1))
        self.assertEqual(counts["allocation_reservations"],
                         ["sub x9,x27,#72"])

    def test_source_extent_and_duplicates(self):
        code = body("ret x30")
        text = (code + "@@PAIR\t0\tuse\t/private/simpLib.sml\n" +
                code + code + "@@PAIR\t1\tused\t/private/simpLib.sml\n")
        old = core.audit.ROOTS
        try:
            core.audit.ROOTS = core.ROOTS
            selected = core.audit.extract(text, Path("/private"))
            self.assertEqual(list(selected), ["simpLib.appconv(1)",
                                              "simpLib.appconv(1)@2"])
        finally:
            core.audit.ROOTS = old
        with self.assertRaises(core.paired.InvalidRun):
            core.audit.simp_extent(text.replace("\tused\t", "\tuse\t"),
                                   Path("/private"))

    def test_exact_trees_nested_lambdas_library_and_ranges(self):
        chunks = []
        for name in core.ROOTS:
            if name == "appconv":
                continue
            raw = 'fn( Arg0 ) (* "simpLib.' + name + '(1)" *)\n'
            if name == "mk_rewr_convdata":
                raw += '  fn( Arg0 ) (* "simpLib.appconv(2)(1)" *)\n'
            chunks.append(raw + '  Arg0\n')
        fold = ('fn( Arg0 ) (* "List.foldr(3)()" *)\n'
                '  FUN "simpLib.USER_CONV(4)" (Arg0)\n'
                'List.foldr(3)()\n'
                '  FunctionCall CODE "simpLib.USER_CONV(4)"\n'
                'List.foldr(3)():\n000000  00000001 ret x30\n')
        text = ('@@PAIR\t0\tuse\t/private/simpLib.sml\n' +
                ''.join(chunks) + fold +
                '@@PAIR\t1\tused\t/private/simpLib.sml\n')
        rows = core.compiler_records(text, Path('/private'))
        self.assertEqual([r['kind'] for r in rows][-3:],
                         ['optimized-tree', 'icode', 'assembly'])
        for r in rows:
            self.assertEqual(''.join(text.splitlines(keepends=True)[
                r['stdout_start_line'] - 1:r['stdout_end_line']]), r['text'])
        with self.assertRaises(core.paired.InvalidRun):
            core.compiler_records(text.replace('simpLib.appconv(',
                                  'unrelated('), Path('/private'))

    def test_repeated_tree_passes_and_missing_not_equal(self):
        a = dict(kind="icode", name="simpLib.appconv(1)",
                 text="Load 16\nFunctionCall x16\n")
        b = dict(a, text="Load 24\nFunctionCall x17\n")
        result = core.tree_comparison([a, a], [a, b])
        self.assertEqual(len(result), 2)
        self.assertTrue(result["icode:simpLib.appconv(1)@1"]["identical"])
        self.assertFalse(result["icode:simpLib.appconv(1)@2"]["identical"])
        missing = core.tree_comparison([a], [])
        self.assertFalse(next(iter(missing.values()))["identical"])

    def test_only_final_equality_failure_can_be_accepted(self):
        failure = ("strict equality rejected: nonrelocation code or "
                   "emission-inventory differences (see comparison)")
        self.assertTrue(core.collection_accepted(dict(success=False,
            collection_validated=True, failure=failure)))
        for validated, why in ((False, failure), (True, "fixture failure"),
                               (True, "source drift")):
            self.assertFalse(core.collection_accepted(dict(success=False,
                collection_validated=validated, failure=why)))

    def test_native_duplicates_retained(self):
        row = dict(kind="assembly", name="simpLib.appconv(1)",
                   text=body("ret x30"))
        result = core.native_records([row, row])
        self.assertEqual(list(result), ["simpLib.appconv(1)",
                                        "simpLib.appconv(1)@2"])

    def test_selected_names(self):
        for n in core.ROOTS + core.HELPERS:
            self.assertTrue(core.selected("simpLib." + n + "(1)(2)"))
        self.assertFalse(core.selected("simpLib.appconv_other(1)"))
        self.assertFalse(core.selected("Cond_rewr.appconv(1)"))

    def test_archived_evidence(self):
        for directory in (core.HERE / "evidence").glob("*"):
            with self.subTest(evidence=directory.name):
                m = json.loads((directory / "manifest.json").read_text())
                self.assertTrue(m["success"])
                self.assertTrue(m["inspection_complete"])
                self.assertTrue(m["collection_validated"])
                self.assertTrue(m["compiler_source_matches_pinned"])
                for name, seal in m["artifacts"].items():
                    self.assertEqual(core.paired.fingerprint(directory / name),
                                     seal)
                for name, seal in m["extra_artifacts"].items():
                    path = directory / name
                    raw = gzip.decompress(path.read_bytes())
                    self.assertEqual(core.paired.digest(raw),
                                     seal["uncompressed_sha256"])
                for side in ("baseline", "candidate"):
                    source = gzip.decompress((directory /
                        (side + '.source.simpLib.sml.gz')).read_bytes())
                    lines = source.decode().splitlines(keepends=True)
                    for span in m['source_spans'].values():
                        self.assertEqual(''.join(lines[
                            span['start_line'] - 1:span['end_line']]),
                            span['text'])
                    full = gzip.decompress((directory /
                        (side + '.compiler-extent.txt.gz')).read_bytes())
                    offset = m['extra_artifacts'][side +
                        '.compiler-extent.txt.gz']['stdout_start_line']
                    full_lines = full.decode().splitlines(keepends=True)
                    trees = json.loads(gzip.decompress((directory /
                        (side + ".optimized-tree.json.gz")).read_bytes()))
                    for r in trees:
                        self.assertEqual(core.paired.digest(r["text"].encode()),
                                         r["sha256"])
                        self.assertEqual(''.join(full_lines[
                            r['stdout_start_line'] - offset:
                            r['stdout_end_line'] - offset + 1]), r['text'])
                self.assertTrue(all(row["identical_after_pool_relocation"]
                    for row in m["extended_native_comparison"].values()))
                if m["baseline_control"]:
                    self.assertTrue(m["strict_equality_accepted"])
                    self.assertTrue(all(row["identical"] for key, row in
                        m["compiler_comparison"].items()
                        if not key.startswith("assembly:")))


if __name__ == "__main__":
    unittest.main()
