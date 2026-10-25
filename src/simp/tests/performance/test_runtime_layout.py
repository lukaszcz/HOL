"""Runtime graph guards. Synthetic dumps are not runtime evidence."""
import gzip
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

import runtime_layout as r
from performance_schema import suite_options


def dump(base=0x1000, *, literal="0100000000000000", capture=3):
    # Tuple -> four aliases of a closure -> inline code/name/profile/string.
    addr = lambda n: hex(base + n * 0x100)
    data = ' '.join(literal[i:i+2] for i in range(0, 16, 2))
    return (f"{r.MARKER}begin\tArm64\t{','.join(r.ROOTS)}\n\n"
        f"WORDS:{addr(0)}:4\n{addr(1)} {addr(1)} {addr(1)} {addr(1)}\n"
        f"CLOSURE:{addr(1)}:2\n{addr(2)} {capture:08d}\n"
        f"CODE:{addr(2)}:6 Fixture.run\n"
        f"0xd65f03c0 0x3 {addr(3)} {addr(4)} 0x0 0xffffffffffffffe0\n"
        f"BYTES:{addr(3)}:8\n{data}\n"
        f"MUTABLE BYTES:{addr(4)}:8\n00 00 00 00 00 00 00 00\n"
        f"{r.MARKER}end\t19\n")


class RuntimeLayoutTests(unittest.TestCase):
    def test_postlude_after_unmodified_workload_return(self):
        path = r.HERE.parent / "compatibility/paired/runner.sml"
        original = path.read_text()
        result = r.instrument_runner(original)
        prefix, suffix = original.split("val _ = files ()\n")
        self.assertTrue(result.startswith(prefix))
        self.assertTrue(result.endswith("val _ = files ()\n" + suffix))
        self.assertGreater(result.index('"RuntimeLayout.sml"'),
                           result.index('"PAIR_TARGET"'))
        self.assertNotIn("unsafeCast",
                         (r.HERE / "RuntimeLayout.sml").read_text())
        for text in (original.replace("val _ = files ()\n", ""),
                     original + "val _ = files ()\n"):
            with self.assertRaisesRegex(ValueError, "footer"):
                r.instrument_runner(text)

    def test_actual_pools_not_instruction_pointer_guessing(self):
        graph = r.parse(dump())
        code = graph["nodes"][2]
        self.assertEqual(code["fields"], [0x1300, 0x1400, 0])
        self.assertEqual(code["native_words"], [0xd65f03c0])
        inv = r.inventory(graph)
        self.assertEqual(inv["unresolved_slots"], 0)
        self.assertEqual(inv["roots"]["run"]["fields"][0]["name"],
                         "Fixture.run")
        self.assertEqual(inv["roots"]["run"]["fields"][1], {"immediate": 3})
        self.assertEqual(inv["code"][0]["pool"][0]["kind"], "BYTES")
        # An instruction word that happens to equal a known object address
        # MUST NOT be added to the pool or traversed as an edge.
        graph = r.parse(dump().replace("0xd65f03c0", "0x1300"))
        self.assertEqual(graph["nodes"][2]["fields"], code["fields"])

    def test_root_correspondence_not_address_or_name_equality(self):
        a, b = r.parse(dump()), r.parse(dump(0x8000))
        result = r.compare(a, b)
        self.assertEqual(result["matched_objects"], 5)
        self.assertFalse(result["differences"])
        changed = r.parse(dump(0x8000, literal="0300000000000000"))
        self.assertTrue(any(d.get("field") == "bytes" for d in
                            r.compare(a, changed)["differences"]))
        changed = r.parse(dump(0x8000, capture=5))
        self.assertTrue(any(d.get("slot") == 1 for d in
                            r.compare(a, changed)["differences"]))
        changed = r.parse(dump(0x8000).replace("0xd65f03c0", "0xd503201f"))
        self.assertEqual(len(r.compare(a, changed)["native_word_differences"]),
                         1)

    def test_full64_pool_address_decoding_and_register_guards(self):
        text = dump().replace("0xd65f03c0", "0xf941080190000000")
        graph = r.parse(text)
        nodes = {n["address"]: n for n in graph["nodes"]}
        decoded = r.code_references(graph["nodes"][2], nodes)
        self.assertEqual(decoded["references"][0]["load_address"], 0x1210)
        self.assertEqual(decoded["references"][0]["pool_slot"], 0)
        self.assertEqual(decoded["references"][0]["target"]["address"], 0x1300)
        self.assertEqual(decoded["normalized_instructions"],
                         [0x90000000, 0xf9400001])
        # Negative ADRP page displacement must be sign-extended.
        graph = r.parse(dump(0x2000).replace("0xd65f03c0",
                                           "0xf9490801f0ffffe0"))
        decoded = r.code_references(graph["nodes"][2],
                                   {n["address"]: n for n in graph["nodes"]})
        self.assertEqual(decoded["references"][0]["load_address"], 0x2210)
        self.assertEqual(decoded["references"][0]["pool_slot"], 0)
        # Different base register, non-LDR instruction, and out-of-pool
        # address cannot be normalized into a supposedly resolved reference.
        for word in ("0xf941082190000000", "0xd65f03c090000000",
                     "0xf940000190000000"):
            graph = r.parse(dump().replace("0xd65f03c0", word))
            decoded = r.code_references(graph["nodes"][2], nodes)
            self.assertEqual(decoded["unresolved_references"], 1)

    def test_zero_length_data_objects_are_valid(self):
        for kind in ("WORDS", "BYTES"):
            text = dump().replace(r.MARKER + "end\t19",
                f"{kind}:0x1800:0\n{r.MARKER}end\t20")
            graph = r.parse(text)
            self.assertEqual(graph["nodes"][-1]["words"], 0)

    def test_bound_to_post_workload_traced_source(self):
        use = "@@PAIR\t0\tused\t/private/Performance.sml\n"
        begin = "@@PAIR\t1\tuse\t/private/RuntimeLayout.sml\n"
        end = "@@PAIR\t2\tused\t/private/RuntimeLayout.sml\n"
        r.bind_extent(use + begin + dump() + end, Path("/private"))
        for text in (begin + dump() + end + use,
                     use + dump() + begin + end,
                     use + begin + end + dump(),
                     use + begin + dump() + end + end):
            with self.assertRaises(ValueError):
                r.bind_extent(text, Path("/private"))

    def test_aliasing_is_not_erased(self):
        a = r.parse(dump())
        b = r.parse(dump(0x8000))
        extra = dict(b["nodes"][1], address=0xf000)
        b["nodes"].append(extra)
        b["nodes"][0]["fields"][1] = extra["address"]
        result = r.compare(a, b)
        self.assertTrue(any(d.get("reason") == "alias correspondence differs"
                            for d in result["differences"]))

    def test_unresolved_slots_never_compare_equal(self):
        text = dump().replace("00000003", "0x9000")
        graph = r.parse(text)
        self.assertEqual(r.inventory(graph)["unresolved_slots"], 1)
        self.assertTrue(r.compare(graph, graph)["differences"])
        # Runtime IO pointers can be outside the traversable heap; retain
        # the original runtime warning rather than pretending to bind them.
        text = text.replace(r.MARKER + "end", "Bad address 0x0x9000 found\n" +
                            r.MARKER + "end")
        self.assertEqual(len(r.parse(text)["bad_addresses"]), 1)

    def test_split_pool_explicitly_unavailable(self):
        text = dump().replace("0xffffffffffffffe0", "0xf940000090000000")
        graph = r.parse(text)
        self.assertEqual(graph["nodes"][2]["fields"], [])
        self.assertEqual(r.inventory(graph)["split_pools"], 1)
        self.assertEqual(r.inventory(graph)["code"][0]["pool_status"],
                         "split; slots unavailable")

    def test_incomplete_unknown_or_malformed_graphs_reject(self):
        text = dump()
        mutations = [text.replace("Arm64", "Arm64_32"),
            text + text, text.replace(r.MARKER + "end\t19", ""),
            text.replace("end\t19", "end\t20"),
            text.replace("0xffffffffffffffe0", "0xffffffffffffffff"),
            text.replace("0xffffffffffffffe0", "0xfffffffffffffff0"),
            text.replace("0xffffffffffffffe0", "0x0"),
            text.replace("0x3 0x1300", "0x4 0x1300"),
            text.replace("CLOSURE:0x1100:2", "CLOSURE:0x1100:3"),
            text.replace("BYTES:0x1300:8", "BYTES:0x1300:9"),
            text.replace("0x1100 0x1100", "0x9900 0x1100", 1),
            text.replace("BYTES:0x1300", "BYTES:0x1400"),
            text.replace("0xd65f03c0", "not-a-word"),
            text.replace("00000003", "18446744073709551616"),
            text.replace(r.MARKER + "end", r.MARKER + "unknown\n" +
                         r.MARKER + "end"),
            text.replace("0xd65f03c0",
                         "Bad address garbage found\n0xd65f03c0")]
        for mutant in mutations:
            with self.subTest(mutant=mutant[:80]):
                with self.assertRaises(ValueError):
                    r.parse(mutant)

    def test_raw_retained_on_parser_failure_and_hooks_restored(self):
        install, compact = r.paired.install_fixtures, r.paired.compact
        with tempfile.TemporaryDirectory() as tmp:
            output, report = Path(tmp), {"stdout": {}}
            receipt = dict(fixture="performance", accepted=True,
                           selection="baseline", stdout="bad graph\n",
                           environment={"PAIR_PRIVATE": "/private"})
            with self.assertRaises(ValueError):
                with r.diagnostic_loader(output, report):
                    r.paired.compact(receipt, output, "failed")
            self.assertIs(r.paired.install_fixtures, install)
            self.assertIs(r.paired.compact, compact)
            self.assertEqual(gzip.decompress(
                (output / "failed.stdout.txt.gz").read_bytes()),
                b"bad graph\n")
            self.assertFalse(report["stdout"]["failed"]["diagnostic_accepted"])

    def test_explicit_nontiming_suite_and_authorization(self):
        with self.assertRaisesRegex(ValueError, "unknown performance suite"):
            suite_options({"suite": r.SUITE})
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "not-created"
            with self.assertRaisesRegex(ValueError, "authorization"):
                r.main(["--output", str(path)])
            self.assertFalse(path.exists())

    @unittest.skipUnless(os.environ.get("RUNTIME_LAYOUT_EVIDENCE"),
                         "requires real runtime graph archive")
    def test_real_replay_and_coherent_mutations(self):
        root = Path(os.environ["RUNTIME_LAYOUT_EVIDENCE"])
        source = root / "baseline-candidate"
        result = r.replay(source, r.HERE.parents[3])
        with self.assertRaisesRegex(ValueError, "control/source role"):
            r.replay(source, r.HERE.parents[3], control=True)
        self.assertGreater(result["matched_objects"], 10)
        with tempfile.TemporaryDirectory() as tmp:
            dst = Path(tmp) / "archive"
            for mutation, reason in (("comparison", "comparison changed"),
                    ("source", "source differs from Git"),
                    ("loader", "post-workload loader"),
                    ("postlude", "layout postlude"),
                    ("inventory", "process inventory"),
                    ("trace", "proof trace mismatch")):
                with self.subTest(mutation=mutation):
                    shutil.copytree(source, dst)
                    try:
                        rp = dst / "report.json.gz"
                        report = r.load(rp)
                        mp = dst / "paired/manifest.json"
                        manifest = json.loads(mp.read_text())
                        selected = manifest["selections"]["candidate"]
                        if mutation == "comparison":
                            report["comparison"]["matched_objects"] += 1
                        elif mutation == "source":
                            selected["sources"][0]["sha256"] = "0" * 64
                        elif mutation in ("loader", "postlude"):
                            name = ("runner.sml" if mutation == "loader"
                                    else "RuntimeLayout.sml")
                            selected["fixture_products"][name]["sha256"] = (
                                "0" * 64)
                        elif mutation == "inventory":
                            report["stdout"].pop("pair-00-candidate")
                        else:
                            path = dst / "paired/pair-00-candidate.json.gz"
                            receipt = r.load(path)
                            receipt["result"]["events"].pop()
                            path.unlink()
                            r.save(path, receipt)
                        mp.write_text(json.dumps(manifest) + "\n")
                        report["paired_manifest"] = r.seal(mp)
                        rp.unlink()
                        r.save(rp, report)
                        with self.assertRaisesRegex(ValueError, reason):
                            r.replay(dst, r.HERE.parents[3])
                    finally:
                        shutil.rmtree(dst)


if __name__ == "__main__":
    unittest.main()
