#!/usr/bin/env python3
"""Offline synthetic controls only: no builds, HOL processes or timings."""
import contextlib
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
import run_exclusions as runner
import schema
import summarize
import audit_sources


def schedule():
    return {key: 2 for key in schema.KEYS}


def encode(events):
    return "".join(schema.paired.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                   for i, e in enumerate(events))


def events():
    times = ".25,.15,.02,.03,.01,.18,.03,.03,"
    result = [["observation", "timer.accounting", times + "5"],
              ["check", "timer accounting", "pass"]]
    total = 5
    for n in schema.SIZES:
        for label in schema.LABELS:
            key = f"{label}.{n}"
            for phase, i in [("calibration", 0)] + [
                    ("batch", i) for i in range(3)]:
                prefix = f"{i},2," if phase == "batch" else "2,"
                callbacks = f"{2*n},2" if label == "replay" else "0,0"
                result += [["observation", phase + "." + key,
                            prefix + times + "2"],
                           ["observation", "callbacks." + phase + "." + key,
                            callbacks],
                           ["check", phase + " results " + key, "pass"]]
                total += 2
    return result + [["observation", "sink", str(total)],
                     ["observation", "complete", schema.EVIDENCE]]


class ProtocolTests(unittest.TestCase):
    def validate(self, es):
        return schema.timing(encode(es), 3, schedule())

    def test_complete(self):
        obs, data = self.validate(events())
        self.assertEqual(obs, events())
        self.assertEqual(set(data), set(schema.KEYS))
        self.assertEqual(len(data), 44)
        row = data["missing.1000"][0]
        self.assertAlmostEqual(row["cpu"], .105)
        self.assertAlmostEqual(row["nongc_cpu"], .085)
        self.assertAlmostEqual(row["gc_cpu"], .02)
        self.assertAlmostEqual(row["user_cpu"], .09)
        self.assertAlmostEqual(row["system_cpu"], .015)
        self.assertEqual(row["iterations"], 2)

    def test_every_event_required(self):
        es = events()
        for i in range(len(es)):
            with self.subTest(missing=i), self.assertRaises(ValueError):
                self.validate(es[:i] + es[i+1:])

    def test_extra_or_reordered_events(self):
        es = events()
        for i in (0, 2, 5, -1):
            with self.subTest(duplicate=i), self.assertRaises(ValueError):
                self.validate(es[:i] + [es[i]] + es[i:])
        es[2], es[3] = es[3], es[2]
        with self.assertRaises(ValueError):
            self.validate(es)

    def test_wrong_counts_accounting_and_callbacks(self):
        # Calibration fields: count, 8 timers, consumption. Samples add index.
        for i, field, value in ((2, 0, "1"), (2, 9, "0"), (5, 0, "1"),
                                (5, 1, "1"), (5, 10, "1"), (2, 6, "99"),
                                (3, 0, "1"), (-2, 0, "0"),
                                (2, 1, "NaN"), (2, 1, "inf"),
                                (2, 1, "~1"), (2, 1, "0")):
            es = copy.deepcopy(events())
            fields = es[i][2].split(",")
            fields[field] = value
            es[i][2] = ",".join(fields)
            with self.subTest(i=i, field=field, value=value):
                with self.assertRaises(ValueError):
                    self.validate(es)
        es = events()
        index = next(i for i, e in enumerate(es) if e[1] ==
                     "callbacks.batch.replay.1000")
        es[index][2] = "1999,2"
        with self.assertRaises(ValueError):
            self.validate(es)

    def test_failed_check_and_wrong_footer(self):
        es = events()
        es[4][2] = "fail"
        with self.assertRaises(ValueError):
            self.validate(es)
        es = events()
        es[-1][2] = "wrong"
        with self.assertRaises(ValueError):
            self.validate(es)

    def test_schedule_rejects_missing_unknown_and_noninteger(self):
        valid = schedule()
        bad = [None, [], {}, dict(valid, extra=1)]
        partial = dict(valid)
        partial.pop(schema.KEYS[0])
        bad.append(partial)
        for value in (0, -1, True, False, 2.0, "2", None, 1073741825):
            bad.append(dict(valid, **{schema.KEYS[0]: value}))
        for value in bad:
            with self.subTest(value=value), self.assertRaises(ValueError):
                schema.fixed_iterations(value)

    def test_schedule_json_duplicate_and_seal(self):
        with tempfile.TemporaryDirectory(prefix="task17-offline-") as temp:
            path = Path(temp) / "schedule.json"
            path.write_text(json.dumps(schedule()))
            fixed, seal = schema.load_fixed(path)
            self.assertEqual(fixed, schedule())
            self.assertEqual(seal, schema.paired.fingerprint(path))
            path.write_text('{"missing.0":1,"missing.0":2}')
            with self.assertRaises(ValueError):
                schema.load_fixed(path)

    def test_runner_requires_authorization_before_output_or_build(self):
        args = ["--output", "/unused", "--fixed-iterations", "/unused"]
        for suffix in ([], ["--authorize-measurements", "--pairs", "9"],
                       ["--authorize-measurements", "--samples", "2"]):
            with contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    runner.options(args + suffix)
        parsed = runner.options(args + ["--authorize-measurements"])
        self.assertEqual(parsed.pairs, 10)
        self.assertEqual(parsed.repo.resolve(), schema.HERE.parents[4])

    def test_slower_and_uncertain_not_parity(self):
        for ratios in ([1.1]*10, [1.2, 1.1]*5):
            self.assertEqual(summarize.estimate(ratios)["individual95"]
                             ["decision"], "slower")
        uncertain = summarize.estimate([.8, 1.2]*5)
        self.assertEqual(uncertain["individual95"]["decision"], "unresolved")
        self.assertEqual(summarize.estimate([None]*10)["status"],
                         "unresolved_zero_timer")
        self.assertEqual(summarize.estimate([0]*10)["status"],
                         "unresolved_zero_timer")

    def test_launcher_path_exit_footer_and_source_controls(self):
        # Synthetic files/protocol only; execute() is never called.
        with tempfile.TemporaryDirectory(prefix="task17-paths-") as temp:
            repo, private = Path(temp) / "repo", Path(temp) / "private"
            repo.mkdir()
            private.mkdir()
            heap = repo / "shared.sml"
            heap.write_text("shared\n")
            names = ("Traverse", "simpLib", "ExclusionPerformance")
            for name in names:
                (private / (name + ".sml")).write_text(name + "\n")
            payload = events()
            es = [["begin", "baseline", "exclusion-performance", "none"],
                  ["cwd", str(private)], ["holdir", str(repo), str(repo)],
                  ["preloaded", "Meta"], ["heapfile", str(heap)],
                  ["search", str(private)], ["search", str(repo / "sigobj")]]
            loaded = [str(heap)]
            for name in names:
                path = str(private / (name + ".sml"))
                es.append(["use", path])
                if name == names[-1]:
                    es.extend(payload)
                es.append(["used", path])
                loaded.append(path)
            es.extend([["loaded", path] for path in loaded])
            es.append(["end", "pass", str(sum(e[0] == "check" for e in payload))])
            seals = {path: schema.paired.fingerprint(Path(path))
                     for path in loaded}
            receipt = dict(stdout=encode(es), exit=0, timed_out=False)
            def validate(r, hashes=seals):
                return schema.paired.validate(r, selection="baseline",
                    fixture="exclusion-performance", control="none",
                    private=private, repo=repo, private_names=set(names),
                    flavor="baseline", signature="pass", source_hashes=hashes,
                    contract=dict(target=names[-1], observations=payload,
                        red=False, modules=["simpLib", "Traverse"], signatures=[]))
            self.assertEqual(validate(receipt)["outcome"], "pass")
            for bad in (dict(receipt, exit=1), dict(receipt, timed_out=True),
                        dict(receipt, stdout=encode(es[:-1]))):
                with self.assertRaises(ValueError):
                    validate(bad)
            wrong = copy.deepcopy(es)
            wrong[5][1] = str(repo / "wrong")
            with self.assertRaises(ValueError):
                validate(dict(receipt, stdout=encode(wrong)))
            wrong = dict(seals)
            wrong[str(heap)] = dict(bytes=0, sha256="0"*64)
            with self.assertRaises(ValueError):
                validate(receipt, wrong)

    def test_summary_reads_compacted_receipts_and_rejects_missing_footer(self):
        with tempfile.TemporaryDirectory(prefix="task17-summary-") as temp:
            root = Path(temp)
            fixed = schedule()
            obs, data = self.validate(events())
            manifest = dict(success=True, evidence_id=schema.EVIDENCE,
                baseline_control=False, performance=dict(pairs=10, samples=3,
                    fixed_iterations=fixed), runs=[], selections={
                    "baseline": dict(reference=schema.paired.BASE,
                        compiler_matches_pinned={"simpLib.sml": True,
                                                 "simpLib.sig": True})})
            for pair in range(10):
                for side in (("baseline", "candidate") if pair % 2 == 0 else
                             ("candidate", "baseline")):
                    protocol = [["begin", side, "exclusion-performance", "none"]]
                    protocol += obs + [["end", "pass", str(sum(
                        e[0] == "check" for e in obs))]]
                    receipt = dict(stdout=encode(protocol), accepted=True,
                        exit=0, timed_out=False, pair=pair, selection=side,
                        fixture="exclusion-performance", measurements=data,
                        environment=dict(PERF_SAMPLES="3", PERF_FIXED=",".join(
                            f"{k}={v}" for k, v in fixed.items())),
                        result=dict(outcome="pass", events=protocol,
                            observations=obs, expected_test_count=sum(
                                e[0] == "check" for e in obs)))
                    label = f"{side}-{pair}"
                    schema.paired.compact(receipt, root, label)
                    manifest["runs"].append(dict(pair=pair, selection=side,
                        accepted=True, receipt=label + ".json.gz"))
            path = root / "manifest.json"
            path.write_text(json.dumps(manifest))
            _, medians, _ = summarize.load(root, False)
            self.assertEqual(len(medians), 20)
            self.assertAlmostEqual(medians[0, "baseline"]
                                   ["missing.1000"]["cpu"], .105)
            entry = manifest["runs"][0]
            rpath = root / entry["receipt"]
            r = summarize.read_json(rpath)
            self.assertNotIn("stdout", r)
            r["result"]["events"].pop()
            import gzip
            rpath.write_bytes(gzip.compress(json.dumps(r).encode()))
            with self.assertRaises(ValueError):
                summarize.load(root, False)
            manifest["runs"].pop()
            path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                summarize.load(root, False)

    def test_source_audit_rejects_single_byte_drift(self):
        with tempfile.TemporaryDirectory(prefix="task17-source-") as temp:
            repo = Path(temp)
            src = repo / "src/simp/src"
            src.mkdir(parents=True)
            for name in ("simpLib.sml", "simpLib.sig"):
                (src / name).write_bytes(b"baseline\n")
            with mock.patch.object(schema.paired, "git", return_value=b"baseline\n"):
                self.assertTrue(audit_sources.audit(repo)["success"])
                (src / "simpLib.sml").write_bytes(b"baseline\r\n")
                self.assertFalse(audit_sources.audit(repo)["success"])

    def test_sml_schema_keys_agree(self):
        source = (schema.HERE / "ExclusionInputs.sml").read_text()
        for label in schema.LABELS:
            self.assertIn('"' + label + '"', source)
        for name in ("ExclusionInputs.sml", "ExclusionPerformance.sml"):
            raw = (schema.HERE / name).read_text()
            self.assertNotIn("\t", raw)
            self.assertFalse(any(line.rstrip() != line
                                 for line in raw.splitlines()))
        fixed, _ = schema.load_fixed(schema.HERE / "fixed-iterations.json")
        self.assertEqual(set(fixed), set(schema.KEYS))


if __name__ == "__main__":
    unittest.main()
