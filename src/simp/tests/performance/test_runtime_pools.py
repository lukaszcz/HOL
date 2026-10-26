"""Pool capture guards. Synthetic dumps are not runtime evidence."""
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import runtime_pools as p
from test_runtime_layout import dump
from performance_schema import suite_options


def pair(pc, address, reg=0):
    pages = ((address & ~4095) - (pc & ~4095)) // 4096
    imm = pages & ((1 << 21) - 1)
    adrp = 0x90000000 | (imm & 3) << 29 | (imm >> 2) << 5
    ldr = 0xf9400000 | (address & 4095) // 8 << 10 | reg
    return ldr << 32 | adrp


def record(owner, address, slots, kind):
    words = "".join(" ".join(f"0x{w:016x}" for w in slots[i:i+4]) + "\n"
                    for i in range(0, len(slots), 4))
    return (f"{p.POOL}begin\t{owner:#x}\t{address:#x}\t{len(slots)}\t"
            f"{kind}\n{words}{p.POOL}end\t{owner:#x}\n")


def capture(*, split=False, address=0x3000):
    text = dump()
    if split:
        native, trailer = pair(0x1200, address, 1), pair(0x1208, address)
        text = text.replace("CODE:0x1200:6", "CODE:0x1200:2").replace(
            "0xd65f03c0 0x3 0x1300 0x1400 0x0 0xffffffffffffffe0",
            f"{native:#x} {trailer:#x}").replace("end\t19", "end\t15")
    block = p.HANDSHAKE + "\n" + record(0x1200,
        address if split else 0x1210, [0x1300, 0x1400, 0],
        "split" if split else "inline")
    return text.replace("BYTES:0x1300", block + "BYTES:0x1300")


class RuntimePoolTests(unittest.TestCase):
    def test_preserves_legacy_inline_and_totals(self):
        original = p.old.parse(dump())
        graph = p.parse(capture())
        self.assertEqual(graph["total_words"], original["total_words"])
        for before, after in zip(original["nodes"], graph["nodes"]):
            self.assertEqual(before, {k: v for k, v in after.items()
                                      if k != "pool_address"})
        inv = p.inventory(graph)
        self.assertEqual(inv["omitted_pools"], 0)
        self.assertEqual(inv["pool_records"], 1)
        self.assertEqual(inv["unique_split_pools"], 0)

    def test_actual_split_slots_and_nonexecuted_trailer(self):
        graph = p.parse(capture(split=True))
        code = graph["nodes"][2]
        self.assertEqual(code["fields"], [0x1300, 0x1400, 0])
        self.assertEqual(code["native_words"], [pair(0x1200, 0x3000, 1)])
        inv = p.inventory(graph)
        self.assertEqual(inv["total_words"], 15)
        self.assertEqual(inv["split_pool_words_with_headers"], 4)
        self.assertEqual(inv["split_pool_words_already_in_showSize"], 0)
        refs = inv["code"][0]["code_references"]["references"]
        self.assertEqual(len(refs), 1)  # Dummy trailer is NOT a reference.
        self.assertEqual(refs[0]["status"], "resolved split pool load")
        self.assertEqual(refs[0]["target"]["address"], 0x1300)

    def test_signed_pages_boundaries_and_alignment(self):
        for pc, address in ((0x1000, 0x3000), (0x3000, 0x1000),
                            (0x1ff8, 0x2000), (0x2000, 0x1ff8)):
            with self.subTest(pc=pc, address=address):
                self.assertEqual(p.decode_pair(pair(pc, address), pc), address)
        for address in (0x800, 0x3000, 0x3ff8):
            graph = p.parse(capture(split=True, address=address))
            refs = p.inventory(graph)["code"][0]["code_references"]
            self.assertEqual(refs["unresolved_references"], 0)
        with self.assertRaises(ValueError):
            p.decode_pair(pair(0x1200, 0x3000, 1), 0x1200)

    def test_shared_pools_and_present_storage_not_double_counted(self):
        text = capture(split=True)
        # One extra same-named CODE owner; do not collapse it by name.
        extra = (f"CODE:0x1800:2 Fixture.run\n"
                 f"{pair(0x1800, 0x3000, 1):#x} "
                 f"{pair(0x1808, 0x3000):#x}\n" +
                 record(0x1800, 0x3000, [0x1300, 0x1400, 0], "split"))
        text = text.replace(p.old.MARKER + "end\t15", extra +
            "WORDS:0x3000:3\n0x1300 0x1400 0x0\n" +
            p.old.MARKER + "end\t22")
        graph = p.parse(text)
        inv = p.inventory(graph)
        self.assertEqual(inv["pool_records"], 2)
        self.assertEqual(inv["unique_split_pools"], 1)
        self.assertEqual(inv["split_pool_words_with_headers"], 4)
        self.assertEqual(inv["split_pool_words_already_in_showSize"], 4)
        self.assertEqual(list(inv["split_pool_owners"].values()), [2])
        for changed in (text.replace(record(0x1800, 0x3000,
                [0x1300, 0x1400, 0], "split"),
                record(0x1800, 0x3000, [0x1300, 0x1400, 1], "split")),
                text.replace("WORDS:0x3000:3\n0x1300",
                             "WORDS:0x3000:3\n0x1400")):
            with self.assertRaises(ValueError):
                p.parse(changed)

    def test_pool_alias_correspondence_and_root_paths(self):
        left = p.parse(capture(split=True))
        right = p.parse(capture(split=True))
        for graph in (left, right):
            extra = dict(graph["nodes"][2], address=0x1800)
            graph["nodes"].append(extra)
            graph["nodes"][1]["fields"][1] = 0x1800
        right["nodes"][-1]["pool_address"] = 0x4000
        result = p.compare(left, right)
        faults = [d for d in result["differences"]
                  if d.get("reason") == "pool alias correspondence differs"]
        self.assertEqual(len(faults), 1)
        self.assertTrue(faults[0]["path"].startswith("roots.run"))
        self.assertTrue(any("path" in d for d in result["differences"]))

    def test_xzr_is_not_an_sp_address_producer(self):
        graph = p.parse(capture(split=True))
        node = graph["nodes"][2]
        word = pair(0x1200, 0x3000, 1) | 31 | (31 << 37)
        node["native_words"] = [word]
        result = p.code_references(node, {})
        self.assertEqual(result["unresolved_references"], 1)
        self.assertNotIn("target", result["references"][0])
        self.assertEqual(result["normalized_instructions"],
                         [word & 0xffffffff, word >> 32])

    def test_early_pool_record_and_empty_split_reject(self):
        text = capture()
        block = p.HANDSHAKE + "\n" + record(0x1200, 0x1210,
                                             [0x1300, 0x1400, 0], "inline")
        early = text.replace(block, "").replace("CODE:0x1200:6 Fixture.run\n",
            "CODE:0x1200:6 Fixture.run\n" + block)
        with self.assertRaisesRegex(ValueError, "early"):
            p.parse(early)
        text = capture(split=True).replace(record(0x1200, 0x3000,
            [0x1300, 0x1400, 0], "split"), record(0x1200, 0x3000, [], "split"))
        with self.assertRaisesRegex(ValueError, "address/count"):
            p.parse(text)

    def test_unknown_slots_preserved_not_parity(self):
        text = capture(split=True).replace("0x0000000000001300",
                                          "0x0000000000009000")
        graph = p.parse(text)
        self.assertEqual(p.inventory(graph)["unresolved_slots"], 1)
        self.assertTrue(p.compare(graph, graph)["differences"])

    def test_inline_disagreement_truncation_wrong_owner_and_handshake(self):
        text = capture()
        block = record(0x1200, 0x1210, [0x1300, 0x1400, 0], "inline")
        mutations = [dump(), text.replace(p.HANDSHAKE + "\n", ""),
            text + p.HANDSHAKE + "\n",
            text.replace(p.HANDSHAKE, p.HANDSHAKE + "\n" + p.HANDSHAKE),
            text.replace(block, ""), text.replace(block, block + block),
            text.replace("begin\t0x1200", "begin\t0x1100"),
            text.replace("end\t0x1200", "end\t0x1300"),
            text.replace("\t0x1210\t3\t", "\t0x1218\t3\t"),
            text.replace("\t0x1210\t3\t", "\t0x1210\t2\t"),
            text.replace("\t0x1210\t3\t", "\t0x1210\t4\t"),
            text.replace("0000000000001300", "0000000000001400"),
            text.replace("0x0000000000001300", "0x1300"),
            text.replace("\tinline\n", "\tsplit\n"),
            text.replace(p.POOL + "end\t0x1200\n", ""),
            text + p.POOL + "unknown\n"]
        for i, changed in enumerate(mutations):
            with self.subTest(mutation=i):
                with self.assertRaises(ValueError):
                    p.parse(changed)
        text = capture(split=True)
        for changed in (text.replace("\t0x3000\t3\t", "\t0x3010\t3\t"),
                        text.replace("\t0x3000\t3\t", "\t0x3001\t3\t"),
                        text.replace("\tsplit\n", "\tinline\n")):
            with self.assertRaises(ValueError):
                p.parse(changed)

    def test_new_postlude_bound_after_unchanged_target(self):
        path = p.HERE.parent / "compatibility/paired/runner.sml"
        original = path.read_text()
        instrumented = p.instrument_runner(original)
        self.assertTrue(instrumented.startswith(
            original.split("val _ = files ()\n")[0]))
        self.assertIn('"RuntimePools.sml"', instrumented)
        self.assertNotIn('"RuntimeLayout.sml"', instrumented)
        private = Path("/private")
        use = "@@PAIR\t0\tused\t/private/Performance.sml\n"
        begin = "@@PAIR\t1\tuse\t/private/RuntimePools.sml\n"
        end = "@@PAIR\t2\tused\t/private/RuntimePools.sml\n"
        p.bind_extent(use + begin + capture() + end, private)
        with self.assertRaises(ValueError):
            p.bind_extent(use + capture() + begin + end, private)

    def test_no_ordinary_environment_change_and_retained_failure(self):
        execute, compact, install = (p.paired.execute, p.paired.compact,
                                     p.paired.install_fixtures)
        with tempfile.TemporaryDirectory() as tmp:
            dst, report = Path(tmp), {"stdout": {}}
            receipt = dict(fixture="performance", accepted=True,
                selection="baseline", stdout="bad pools\n",
                environment={"PAIR_PRIVATE": "/private"})
            with self.assertRaises(ValueError):
                with p.diagnostic_loader(dst, report):
                    p.paired.compact(receipt, dst, "failed")
            self.assertEqual(gzip.decompress(
                (dst / "failed.stdout.txt.gz").read_bytes()), b"bad pools\n")
            self.assertFalse(report["stdout"]["failed"]["diagnostic_accepted"])
            rejected = p.load(dst / "failed.json.gz")
            self.assertEqual(rejected["environment"], receipt["environment"])
            self.assertFalse(rejected["diagnostic_accepted"])
            self.assertIn("pool_rejection", rejected)
        self.assertIs(p.paired.execute, execute)
        self.assertIs(p.paired.compact, compact)
        self.assertIs(p.paired.install_fixtures, install)

    def test_authorization_and_timing_rejection(self):
        with self.assertRaisesRegex(ValueError, "unknown performance suite"):
            suite_options({"suite": p.SUITE})
        with tempfile.TemporaryDirectory() as tmp:
            dst = Path(tmp) / "not-created"
            with self.assertRaisesRegex(ValueError, "authorization"):
                p.main(["--output", str(dst)])
            self.assertFalse(dst.exists())

    @unittest.skipUnless(os.environ.get("RUNTIME_POOLS_EVIDENCE"),
                         "requires real runtime pools archive")
    def test_real_replay_and_coherent_mutations(self):
        source = (Path(os.environ["RUNTIME_POOLS_EVIDENCE"]) /
                  "baseline-candidate")
        result = p.replay(source, p.HERE.parents[3])
        self.assertEqual(result["baseline"]["omitted_pools"], 0)
        with self.assertRaisesRegex(ValueError, "control/source role"):
            p.replay(source, p.HERE.parents[3], control=True)
        with tempfile.TemporaryDirectory() as tmp:
            dst = Path(tmp) / "archive"
            for mutation, reason in (("comparison", "comparison changed"),
                    ("source", "source differs from Git"),
                    ("loader", "post-workload loader"),
                    ("postlude", "pool postlude"),
                    ("fixture", "fixture interposer"),
                    ("inventory", "process inventory"),
                    ("preload", "preload admission"),
                    ("binary", "interposer/build changed"),
                    ("build", "native build command"),
                    ("build-output", "command output"),
                    ("proof", "proof trace mismatch")):
                with self.subTest(mutation=mutation):
                    shutil.copytree(source, dst)
                    try:
                        rp = dst / "report.json.gz"
                        report = p.load(rp)
                        mp = dst / "paired/manifest.json"
                        manifest = json.loads(mp.read_text())
                        fixture = manifest["selections"]["candidate"]
                        if mutation == "comparison":
                            report["comparison"]["matched_objects"] += 1
                        elif mutation == "source":
                            fixture["sources"][0]["sha256"] = "0" * 64
                        elif mutation in ("loader", "postlude", "fixture"):
                            name = dict(loader="runner.sml",
                                postlude="RuntimePools.sml",
                                fixture="runtime-pools.so")[mutation]
                            fixture["fixture_products"][name]["sha256"] = (
                                "0" * 64)
                        elif mutation == "inventory":
                            report["stdout"].pop("pair-00-candidate")
                        elif mutation == "binary":
                            (dst / "runtime-pools.so").write_bytes(b"wrong")
                        elif mutation in ("build", "build-output"):
                            path = dst / "native-build.json"
                            build = json.loads(path.read_text())
                            if mutation == "build":
                                build["command"][0] = "/bin/true"
                            else:
                                build["stdout_sha256"] = "0" * 64
                            path.write_text(json.dumps(build) + "\n")
                            report["native"]["build_receipt"] = p.seal(path)
                        else:
                            path = dst / "paired/pair-00-candidate.json.gz"
                            receipt = p.load(path)
                            if mutation == "preload":
                                receipt["pool_environment"]["LD_PRELOAD"] = (
                                    "bad")
                            else:
                                receipt["result"]["events"].pop()
                            path.unlink()
                            p.save(path, receipt)
                        mp.write_text(json.dumps(manifest) + "\n")
                        report["paired_manifest"] = p.seal(mp)
                        rp.unlink()
                        p.save(rp, report)
                        with self.assertRaisesRegex(ValueError, reason):
                            p.replay(dst, p.HERE.parents[3])
                    finally:
                        shutil.rmtree(dst)


@unittest.skipUnless(os.environ.get("RUNTIME_POOLS_NATIVE"),
                     "requires audited native Arm64 Poly/ML")
class NativePoolTests(unittest.TestCase):
    def test_executable_hook_and_extent_negative_controls(self):
        with tempfile.TemporaryDirectory(prefix="runtime-pool-test-") as tmp:
            dst = Path(tmp)
            p.build(dst, 120)
            library = str(dst / "runtime-pools.so")
            prelude = (p.HERE / "RuntimePools.sml").read_text()
            roots = ("fun run x = x * 37 + 19;\n"
                     "val step = Int.toString;\n"
                     "val measured = run;\nval experiment = run;\n")
            script = dst / "selftest.sml"
            env = dict(os.environ, LD_PRELOAD=library,
                       RUNTIME_POOLS_LIBRARY=library)
            script.write_text(roots + prelude)
            result = subprocess.run(["poly", "--script", str(script)],
                env=env, text=True, capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0,
                             result.stdout + result.stderr)
            self.assertFalse(result.stderr)
            inv = p.inventory(p.parse(result.stdout))
            self.assertGreater(inv["unique_split_pools"], 0)
            self.assertEqual(inv["omitted_pools"], 0)
            for text in (prelude.replace("beginPools ()", "()")
                               .replace("endPools ()", "()"),
                         prelude.replace("(run,step,measured,experiment)",
                                         "7")):
                script.write_text(roots + text)
                result = subprocess.run(["poly", "--script", str(script)],
                    env=env, text=True, capture_output=True, timeout=120)
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertNotIn(p.POOL, result.stdout)
                with self.assertRaises(ValueError):
                    p.parse(result.stdout)
            # dlopen alone is not proof the runtime's PLT was interposed.
            script.write_text(roots + prelude)
            without_preload = dict(env)
            without_preload.pop("LD_PRELOAD")
            result = subprocess.run(["poly", "--script", str(script)],
                env=without_preload, text=True, capture_output=True,
                timeout=120)
            # RTLD_NEXT may itself reject the late-loaded hook; either way
            # missing preload must never produce an admissible capture.
            self.assertNotIn(p.POOL, result.stdout)
            with self.assertRaisesRegex(ValueError, "admission"):
                p.parse(result.stdout)


if __name__ == "__main__":
    unittest.main()
