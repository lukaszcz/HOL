#!/usr/bin/env python3
"""Offline fail-closed controls; no HOL execution, build or measurement."""
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import run_tactics as runner
import schema
import summarize
import audit_sources


def schedule():
    return {key: 2 for key in schema.KEYS}


def events():
    times = ".25,.15,.02,.03,.01,.18,.03,.03,"
    result = [["observation", "timer.accounting", times + "5"],
              ["check", "timer accounting", "pass"]]
    total = 5
    for n in schema.SIZES:
        for label in schema.LABELS:
            key = f"{label}.{n}"
            stage = label.rsplit("_", 1)[1]
            counts = {"construct": "2,0,0", "reuse": "0,2,2",
                      "complete": "2,2,2"}[stage]
            for phase, i in [("calibration", 0)] + [
                    ("batch", i) for i in range(3)]:
                prefix = f"{i},2," if phase == "batch" else "2,"
                result += [["observation", phase + "." + key,
                            prefix + times + "2"],
                           ["observation", "stages." + phase + "." + key,
                            counts],
                           ["check", phase + " results " + key, "pass"]]
                total += 2
    return result + [["observation", "sink", str(total)],
                     ["observation", "complete", schema.EVIDENCE]]


def encode(es):
    return "".join(schema.paired.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                   for i, e in enumerate(es))


class ProtocolTests(unittest.TestCase):
    def validate(self, es):
        return schema.timing(encode(es), 3, schedule())

    def test_complete_and_separate_gc(self):
        obs, data = self.validate(events())
        self.assertEqual(obs, events())
        self.assertEqual(len(data), 66)
        row = data["global_complete.8"][0]
        for metric, expected in (("cpu", .105), ("nongc_cpu", .085),
                                 ("gc_cpu", .02), ("user_cpu", .09),
                                 ("system_cpu", .015)):
            self.assertAlmostEqual(row[metric], expected)

    def test_explicit_row_filter_preserves_all_selected_gates(self):
        keys = ("full_complete.0", "no_strip_rev_reuse.8")
        es = events()
        selected = es[:2]
        for i in range(2, len(es)-2, 12):
            block = es[i:i+12]
            if block[0][1].removeprefix("calibration.") in keys:
                selected.extend(block)
        selected += [["observation", "sink", "21"], es[-1]]
        _, data = schema.timing_events(selected, 3, schedule(), keys)
        self.assertEqual(tuple(data), keys)
        for i in range(len(selected)):
            with self.assertRaises(ValueError):
                schema.timing_events(selected[:i] + selected[i+1:],
                                     3, schedule(), keys)
        for bad in ([], [keys[0]]*2, list(reversed(keys)), ["unknown"]):
            with self.assertRaises(ValueError):
                schema.selected_keys(bad)
        with self.assertRaises(ValueError):
            schema.timing_events(es, 3, schedule(), keys)

    def test_gc_parser_separate_and_fail_closed(self):
        import gc_diagnostic as gc
        keys = ("full_complete.0",)
        block = events()[2+8*12:2+9*12]
        self.assertEqual(block[0][1], "calibration.full_complete.0")
        es = events()[:2]
        for i, phase in enumerate(['calibration', 'batch0', 'batch1', 'batch2']):
            marker = 'calibration0' if i == 0 else phase
            es += [['observation', f'gctrace.begin.{marker}.{keys[0]}', 'begin'],
                   ['observation', f'gctrace.end.{marker}.{keys[0]}', 'end']]
            es += block[i*3:i*3+2]
            for edge in ('before', 'after'):
                es.append(['observation', f'gcstats.{phase}.{keys[0]}.{edge}',
                           '1,2,0,100,90,80,50,40,30,20'])
            es.append(block[i*3+2])
        es += [['observation', 'sink', '13'], events()[-1]]
        data, stats = gc.parse_events(es, 3, schedule(), keys)
        self.assertEqual(tuple(data), keys)
        self.assertEqual(len(stats), 8)
        for i in range(len(es)):
            with self.assertRaises(ValueError):
                gc.parse_events(es[:i] + es[i+1:], 3, schedule(), keys)
        self.assertEqual(gc.size('1.5M'), 1.5*2**20)

    def test_every_event_required(self):
        es = events()
        for i in range(len(es)):
            with self.subTest(missing=i), self.assertRaises(ValueError):
                self.validate(es[:i] + es[i+1:])

    def test_extra_reorder_fail_and_completion(self):
        es = events()
        for i in (0, 2, 5, -1):
            with self.assertRaises(ValueError):
                self.validate(es[:i] + [es[i]] + es[i:])
        es[2], es[3] = es[3], es[2]
        with self.assertRaises(ValueError):
            self.validate(es)
        for i in (1, 4, -1):
            bad = copy.deepcopy(events())
            bad[i][2] = "fail"
            with self.assertRaises(ValueError):
                self.validate(bad)

    def test_wrong_counts_timers_consumption_and_stages(self):
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

    def test_schedule_rejects_missing_unknown_and_noninteger(self):
        valid = schedule()
        partial = dict(valid)
        partial.pop(schema.KEYS[0])
        bad = [None, [], {}, dict(valid, extra=1), partial]
        for value in (0, -1, True, False, 2.0, "2", None, 1073741825):
            bad.append(dict(valid, **{schema.KEYS[0]: value}))
        for value in bad:
            with self.assertRaises(ValueError):
                schema.fixed_iterations(value)

    def test_schedule_duplicate_and_seal(self):
        with tempfile.TemporaryDirectory(prefix="task18-offline-") as temp:
            path = Path(temp) / "schedule.json"
            path.write_text(json.dumps(schedule()))
            fixed, seal = schema.load_fixed(path)
            self.assertEqual(fixed, schedule())
            self.assertEqual(seal, schema.paired.fingerprint(path))
            path.write_text('{"simp_reuse.0":1,"simp_reuse.0":2}')
            with self.assertRaises(ValueError):
                schema.load_fixed(path)

    def test_authorization_before_any_build(self):
        args = ["--output", "/unused", "--fixed-iterations", "/unused"]
        for suffix in ([], ["--authorize-measurements", "--pairs", "9"],
                       ["--authorize-measurements", "--samples", "2"]):
            with contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    runner.options(args + suffix)
        parsed = runner.options(args + ["--authorize-measurements"])
        self.assertEqual(parsed.repo.resolve(), schema.TESTS.parents[2])

    def test_slower_is_failure_uncertain_not_parity(self):
        for ratios in ([1.1]*10, [1.2, 1.1]*5):
            self.assertEqual(summarize.estimate(ratios)["individual95"]
                             ["decision"], "slower")
        self.assertEqual(summarize.estimate([.8, 1.2]*5)["individual95"]
                         ["decision"], "unresolved")
        self.assertEqual(summarize.estimate([0]*10)["status"],
                         "unresolved_zero_timer")

    def test_launcher_exit_path_footer_source_controls(self):
        with tempfile.TemporaryDirectory(prefix="task18-paths-") as temp:
            repo, private = Path(temp) / "repo", Path(temp) / "private"
            repo.mkdir()
            private.mkdir()
            heap = repo / "shared.sml"
            heap.write_text("shared\n")
            names = ("Traverse", "simpLib", "TacticPerformance")
            for name in names:
                (private / (name + ".sml")).write_text(name + "\n")
            payload = events()
            es = [["begin", "baseline", "tactic-performance", "none"],
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
                    fixture="tactic-performance", control="none",
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

    def test_summary_compacted_receipts_and_missing_pairs(self):
        with tempfile.TemporaryDirectory(prefix="task18-summary-") as temp:
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
                    protocol = [["begin", side, "tactic-performance", "none"]]
                    protocol += obs + [["end", "pass", str(sum(
                        e[0] == "check" for e in obs))]]
                    receipt = dict(stdout=encode(protocol), accepted=True,
                        exit=0, timed_out=False, pair=pair, selection=side,
                        fixture="tactic-performance", measurements=data,
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
                                   ["global_complete.8"]["cpu"], .105)
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
        with tempfile.TemporaryDirectory(prefix="task18-source-") as temp:
            repo = Path(temp)
            src = repo / "src/simp/src"
            src.mkdir(parents=True)
            for name in ("simpLib.sml", "simpLib.sig"):
                (src / name).write_bytes(b"baseline\n")
            with mock.patch.object(schema.paired, "git", return_value=b"baseline\n"):
                self.assertTrue(audit_sources.audit(repo)["success"])
                (src / "simpLib.sml").write_bytes(b"baseline\r\n")
                self.assertFalse(audit_sources.audit(repo)["success"])

    def test_sml_labels_schedule_and_clean_source(self):
        source = (schema.HERE / "TacticInputs.sml").read_text()
        for name in schema.OPERATIONS + schema.STAGES:
            self.assertIn('"' + name + '"', source)
        for path in schema.HERE.glob("*.sml"):
            raw = path.read_text()
            self.assertNotIn("\t", raw)
            self.assertFalse(any(line.rstrip() != line
                                 for line in raw.splitlines()))
        fixed, _ = schema.load_fixed(schema.HERE / "fixed-iterations.json")
        self.assertEqual(set(fixed), set(schema.KEYS))


if __name__ == "__main__":
    unittest.main()
