"""Replay real extended allocator controls; synthetic mutations must reject."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "allocator-counter"))
import control_schema
import worker_schema
import interpreter_schema
import failure_schema

ARCHIVE = HERE / "evidence/task29/managed-coverage/controls.json.gz"


class CoverageReceiptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = json.loads(gzip.decompress(ARCHIVE.read_bytes()))

    def test_complete_real_controls_and_original_input_seals(self):
        r = self.receipt
        self.assertEqual(r["schema"], "task29-managed-counter-controls-v2")
        self.assertTrue(r["success"])
        self.assertFalse(r["task29_complete"])
        self.assertTrue(all(c["exit"] == 0 and not c["timed_out"]
                            for c in r["commands"]))
        for path in (HERE / "allocator-counter").iterdir():
            if not path.is_file():
                continue
            matches = [v for p, v in r["inputs"].items()
                       if p.endswith("/allocator-counter/" + path.name)]
            self.assertEqual(len(matches), 1, path.name)
            self.assertEqual(matches[0], dict(bytes=path.stat().st_size,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        for name in ("worker_schema.py", "interpreter_schema.py",
                     "failure_schema.py", "acceptance.py", "loading.py"):
            matches = [v for p, v in r["inputs"].items()
                       if p.endswith("/performance/" + name)]
            self.assertEqual(len(matches), 1, name)
            digest = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
            self.assertEqual(matches[0]["sha256"], digest)

    def test_real_protocols_recompute_without_private_builds(self):
        r = self.receipt
        total = 0
        for prefix, schema in (("", control_schema), ("worker_", worker_schema),
                               ("interpreter_", interpreter_schema),
                               ("failure_", failure_schema)):
            key = "control_output" if not prefix else prefix + "output"
            observed = schema.observations(r[key])
            total += observed["brackets"]
            self.assertEqual(json.dumps(observed, sort_keys=True), json.dumps(
                r[prefix + "observations"], sort_keys=True))
            identity = r[prefix + "process_identity"]
            self.assertEqual(identity["symbol"], r[key].split(
                "_RUNTIME_V1\t", 1)[1].splitlines()[0])
            runtime = identity["symbol"]
            library = [v for p, v in r["instrumented_libraries"].items()
                       if Path(p).name.startswith("libpolyml.so")]
            self.assertEqual(len(library), 1)
            self.assertEqual(library[0]["sha256"], r["runtime"]["sha256"])
            # Resolve only archived lexical identities: private files have
            # correctly been deleted. Runtime-path checks ran live in driver.
            self.assertEqual(Path(runtime).name, "libpolyml.so.16")
            self.assertTrue(all("libpolyml" not in m or runtime.rsplit(
                "/", 1)[0] + "/libpolyml.so.16.0.0" in m
                for m in identity["maps"]))
        self.assertEqual(total, 122)
        process = next(c for c in r["commands"] if
                       c["command"][0].endswith("/failure-controls.exe"))
        self.assertEqual(failure_schema.validate_receipt(process, timeout=300),
                         failure_schema.observations(r["failure_output"]))

    def test_real_record_loss_and_changes_reject(self):
        for prefix, schema in (("worker_", worker_schema),
                               ("interpreter_", interpreter_schema),
                               ("failure_", failure_schema)):
            text = self.receipt[prefix + "output"]
            lines = text.splitlines()
            for suffix in ("ENDPOINT_V1", "RESULT_V1", "COMPLETE_V1"):
                i = next(i for i, line in enumerate(lines)
                         if line.startswith("@@TASK29_") and suffix in line)
                for changed in (lines[:i] + lines[i+1:],
                                lines[:i] + [lines[i]] + lines[i:]):
                    with self.subTest(prefix=prefix, suffix=suffix):
                        with self.assertRaises(ValueError):
                            schema.observations("\n".join(changed))
        text = self.receipt["failure_output"]
        with self.assertRaises(ValueError):
            failure_schema.observations(text.replace(failure_schema.EXHAUSTION,
                                                     "", 1))


if __name__ == "__main__":
    unittest.main()
