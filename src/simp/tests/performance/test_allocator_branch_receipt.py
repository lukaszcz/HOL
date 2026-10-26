"""Replay real private branch controls; not TASK29 performance acceptance."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
COUNTER = HERE / "allocator-counter"
sys.path.insert(0, str(COUNTER))
import control_schema
import worker_schema
import interpreter_schema
import interpreter_branch_schema as branches
import failure_schema

ARCHIVE = HERE / "evidence/task29/managed-branches/controls.json.gz"


def replay(r):
    if not (r["schema"] == "task29-managed-counter-controls-v3" and
            r["success"] is True and r["task29_complete"] is False and
            len(r["commands"]) == 25 and all(
                c["exit"] == 0 and not c["timed_out"] for c in r["commands"])):
        raise ValueError("incomplete private controls")
    output = r["interpreter_output"]
    split = branches.observations(output)
    original = "\n".join(line for line in output.splitlines()
                         if not line.startswith("@@TASK29_IBRANCH"))
    parsed = {"observations": control_schema.observations(r["control_output"]),
              "worker_observations": worker_schema.observations(
                  r["worker_output"]),
              "interpreter_observations": interpreter_schema.observations(
                  original),
              "interpreter_branch_observations": split,
              "failure_observations": failure_schema.observations(
                  r["failure_output"])}
    for key, value in parsed.items():
        if json.dumps(value, sort_keys=True) != json.dumps(r[key], sort_keys=True):
            raise ValueError("changed parsed controls: " + key)
    if sum(p["brackets"] for p in parsed.values()) != 138:
        raise ValueError("missing control brackets")
    for prefix in ("", "worker_", "interpreter_", "failure_"):
        launcher = "counter" if not prefix else prefix[:-1]
        command = next(c for c in r["commands"] if c["command"][0].endswith(
            "/" + launcher + "-controls.exe"))
        text = r["control_output" if not prefix else prefix + "output"]
        if command["stdout"] != text:
            raise ValueError("changed original stdout")
        if prefix == "failure_":
            failure_schema.validate_receipt(command, timeout=900)
        identity = r[prefix + "process_identity"]
        if identity["symbol"] != text.split("_RUNTIME_V1\t", 1)[1].splitlines()[0]:
            raise ValueError("different snapshot identity")
        runtime = identity["symbol"]
        library = [v for p, v in r["instrumented_libraries"].items()
                   if Path(p).name.startswith("libpolyml.so")]
        if not (len(library) == 1 and
                library[0]["sha256"] == r["runtime"]["sha256"] and
                identity["maps"] and all("libpolyml" not in m or
                    runtime.rsplit("/", 1)[0] + "/libpolyml.so.16.0.0" in m
                    for m in identity["maps"])):
            raise ValueError("different mapped runtime")
    return parsed


class BranchReceiptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = json.loads(gzip.decompress(ARCHIVE.read_bytes()))

    def test_real_controls_replay_without_private_trees(self):
        parsed = replay(self.receipt)
        self.assertEqual(parsed["interpreter_branch_observations"]
                         ["no_op_words"], [31, 31, 0, 0, 0])
        self.assertEqual(parsed["interpreter_branch_observations"]
                         ["deltas"]["refs-131072-1"],
                         [655391, 31, 0, 655360, 0])

    def test_live_instrument_and_schemas_are_bound(self):
        inputs = self.receipt["inputs"]
        paths = [p for p in COUNTER.iterdir() if p.is_file()]
        paths += [HERE / name for name in (
            "worker_schema.py", "interpreter_schema.py",
            "interpreter_branch_schema.py", "failure_schema.py",
            "acceptance.py", "loading.py")]
        for path in paths:
            suffix = "/" + str(path.relative_to(HERE))
            matches = [v for p, v in inputs.items() if p.endswith(suffix)]
            self.assertEqual(len(matches), 1, suffix)
            raw = path.read_bytes()
            self.assertEqual(matches[0], dict(bytes=len(raw),
                sha256=hashlib.sha256(raw).hexdigest()), suffix)

    def test_real_branch_record_loss_duplication_and_change_reject(self):
        text = self.receipt["interpreter_output"]
        lines = text.splitlines()
        for suffix in ("ENDPOINT", "BRANCH", "RAW", "SPLIT", "RESULT",
                       "COMPLETE"):
            i = next(i for i, line in enumerate(lines)
                     if line.startswith(branches.PREFIX + suffix + "_V1"))
            for changed in (lines[:i] + lines[i+1:],
                            lines[:i] + [lines[i]] + lines[i:]):
                with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                    branches.observations("\n".join(changed))
        for old, new in (("\t1\t8\t0\t", "\t1\t8\t1\t"),
                         ("\t131072\t8590000128", "\t131072\t0")):
            self.assertIn(old, text)
            with self.assertRaises(ValueError):
                branches.observations(text.replace(old, new))


if __name__ == "__main__":
    unittest.main()
