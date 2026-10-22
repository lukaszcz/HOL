"""Fail-closed assembly parsing/normalization controls (no compiler runs)."""
from pathlib import Path
import unittest
import run_assembly as audit


def body(*rows):
    return "simpLib.ac_ss(1):\n" + "".join(
        f"{i * 4:06X}  00000001        {asm}\n"
        for i, asm in enumerate(rows))


class AssemblyTests(unittest.TestCase):
    def test_pool_relocation_only(self):
        a = body("adrp x9,0x0", "ldr x0,[x9,#832]", "ret x30", "?")
        b = body("adrp x9,0x1000", "ldr x0,[x9,#904]", "ret x30", "?")
        self.assertEqual(audit.normalized(a), audit.normalized(b))

    def test_real_operands_not_normalized(self):
        for a, b in (("ldr x0,[x8,#16]", "ldr x0,[x8,#24]"),
                     ("b.cs 0x20", "b.cs 0x24"),
                     ("sub x9,x27,#72", "sub x9,x27,#80"),
                     ("blr x16", "blr x17")):
            self.assertNotEqual(audit.normalized(body(a)),
                                audit.normalized(body(b)))

    def test_extra_instructions_preserved(self):
        self.assertNotEqual(audit.normalized(body("ret x30")),
                            audit.normalized(body("blr x16", "ret x30")))

    def test_unknown_adrp_rejected(self):
        with self.assertRaises(audit.paired.InvalidRun):
            audit.normalized(body("adrp x9,0x0", "ldr x0,[x8,#832]"))

    def test_truncated_pool_pair_rejected(self):
        with self.assertRaises(audit.paired.InvalidRun):
            audit.normalized(body("adrp x9,0x0"))

    def test_count_maps_and_padding_separately(self):
        c = audit.counts(body("sub x9,x27,#72", "blr x16", "[x0, x1]",
                              "ret x30", "?"))
        self.assertEqual((c["instructions"], c["gc_maps"], c["padding"],
                          c["calls"]), (3, 1, 1, 1))
        self.assertEqual(c["allocation_reservations"], ["sub x9,x27,#72"])

    def test_extent_and_exact_body(self):
        private = Path("/private")
        code = body("ret x30")
        text = ("simpLib.fake(1):\n000000  00000001 ret x30\n"
                "@@PAIR\t0\tuse\t/private/simpLib.sml\n" + code +
                "@@PAIR\t1\tused\t/private/simpLib.sml\n")
        self.assertEqual(audit.extract(text, private),
                         {"simpLib.ac_ss(1)": code})
        with self.assertRaises(audit.paired.InvalidRun):
            audit.extract(text.replace("\tused\t", "\tuse\t"), private)

    def test_duplicate_specializations_retained(self):
        code = body("ret x30")
        text = ("@@PAIR\t0\tuse\t/private/simpLib.sml\n" + code + code +
                "@@PAIR\t1\tused\t/private/simpLib.sml\n")
        selected = audit.extract(text, Path("/private"))
        self.assertEqual(list(selected), ["simpLib.ac_ss(1)",
                                          "simpLib.ac_ss(1)@2"])
        self.assertEqual(list(selected.values()), [code, code])

    def test_unpaired_optional_not_silently_accepted(self):
        selected = {"simpLib." + root + "(1)": body("ret x30")
                    for root in audit.ROOTS}
        optional = dict(selected)
        optional["simpLib.merge_names(1)"] = body("ret x30")
        c = audit.compare(optional, selected)["simpLib.merge_names(1)"]
        self.assertFalse(c["identical_after_pool_relocation"])
        self.assertIsNone(c["candidate"])
        self.assertIn("not emitted by candidate", c["support"])

    def test_optimized_tree_optional_cli(self):
        self.assertFalse(audit.parse_args(["--output", "/tmp/unused"])
                         .optimized_tree)
        self.assertTrue(audit.parse_args(["--output", "/tmp/unused",
                                          "--optimized-tree"]).optimized_tree)

    def test_optimized_tree_selected_exact_passes_and_extent(self):
        tree = ('fn( Arg0 ) (* "simpLib.merge_ss(1)" 2 locals *)\n'
                '  C<callee> (Arg0, 0)\n')
        icode = ("simpLib.merge_ss(1)                            \n"
                 '        FunctionCall        CODE "callee" (X0=X0 )\n')
        other = ('fn( Arg0 ) (* "simpLib.other(1)" 0 locals *)\n'
                 '  Arg0\n')
        text = (tree + "@@PAIR\t0\tuse\t/private/simpLib.sml\n" +
                other + "simpLib.other(1):\n000000  00000001 ret x30\n" +
                tree + 'LAMBDA(\n  ignored backend tree\n)\n' +
                icode + icode +
                "List.map(2)()   \n  ignored helper pass\n" +
                "simpLib.merge_ss(1):\n000000  00000001 ret x30\n" +
                "@@PAIR\t1\tused\t/private/simpLib.sml\n" + tree)
        records = audit.extract_compiler(text, Path("/private"))
        self.assertEqual([r["text"] for r in records], [tree, icode, icode])
        self.assertEqual([r["kind"] for r in records],
                         ["optimized-tree", "icode", "icode"])
        for r in records:
            self.assertEqual(r["sha256"],
                             audit.paired.digest(r["text"].encode()))
            self.assertEqual("".join(text.splitlines(keepends=True)[
                r["stdout_start_line"] - 1:r["stdout_end_line"]]), r["text"])

    def test_specialized_fold_helper_retained_not_unrelated_fold(self):
        caller = ('fn( Arg0 ) (* "simpLib.merge_ss(1)" *)\n  Arg0\n'
                  'simpLib.merge_ss(1)\n  FunctionCall CODE "helper"\n')
        fold = ('fn( Arg0, Arg1 ) (* "List.foldr(3)()" *)\n'
                '  FUN "simpLib.merge_names(1)(1)" (Arg0)\n')
        icode = ('List.foldr(3)()   \n'
                 '  FunctionCall CODE "simpLib.merge_names(1)(1)"\n')
        native = 'List.foldr(3)():  \n000000  00000001 ret x30\n'
        unrelated = ('List.foldr(3)()\n  FunctionCall CODE "other"\n' +
                     native)
        text = ('@@PAIR\t0\tuse\t/private/simpLib.sml\n' + caller +
                fold + icode + native + unrelated +
                '@@PAIR\t1\tused\t/private/simpLib.sml\n')
        records = audit.extract_compiler(text, Path('/private'))
        self.assertEqual([r['text'] for r in records][2:],
                         [fold, icode, native])
        self.assertEqual(records[-1]['kind'], 'assembly')

    def test_missing_optimized_tree_or_calls_rejected(self):
        tree = 'fn( Arg0 ) (* "simpLib.merge_ss(1)" *)\n  Arg0\n'
        icode = "simpLib.merge_ss(1)\n  FunctionCall ConstantCode callee\n"
        no_calls = tree + icode.replace("FunctionCall", "move")
        for data in (tree, icode, no_calls):
            text = ("@@PAIR\t0\tuse\t/private/simpLib.sml\n" + data +
                    "@@PAIR\t1\tused\t/private/simpLib.sml\n")
            with self.assertRaises(audit.paired.InvalidRun):
                audit.extract_compiler(text, Path("/private"))

    def test_compiler_switches_private_and_exception_safe(self):
        runner = (audit.HERE / "runner.sml").read_text()
        self.assertIn('PAIR_OPTIMIZED_TREE', runner)
        self.assertIn('if path = OS.Path.concat (Paired.env "PAIR_PRIVATE", '
                      '"simpLib.sml")', runner)
        self.assertIn('handle e => (switches false; raise e));'
                      '\n        switches false', runner)
        self.assertIn('PolyML.Compiler.codetreeAfterOpt := '
                      '(enabled andalso optimizedTree)', runner)
        self.assertIn('PolyML.Compiler.icode := (enabled andalso optimizedTree)',
                      runner)

    def test_required_inventory_and_changes_rejected(self):
        selected = {"simpLib." + root + "(1)": body("ret x30")
                    for root in audit.ROOTS}
        self.assertTrue(all(c["identical_after_pool_relocation"] for c in
                            audit.compare(selected, selected).values()))
        missing = dict(selected)
        missing.pop("simpLib.ac_ss(1)")
        with self.assertRaises(audit.paired.InvalidRun):
            audit.compare(missing, missing)
        changed = dict(selected)
        changed["simpLib.ac_ss(1)"] = body("blr x16", "ret x30")
        self.assertFalse(audit.compare(selected, changed)["simpLib.ac_ss(1)"]
                         ["identical_after_pool_relocation"])
        with self.assertRaises(audit.paired.InvalidRun):
            audit.compare(selected, missing)


if __name__ == "__main__":
    unittest.main()
