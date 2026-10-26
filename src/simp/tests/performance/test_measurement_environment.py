#!/usr/bin/env python3
"""Synthetic environment controls; no workloads or real sampling sleeps."""
import copy
import unittest
from unittest.mock import patch

import measurement_environment as env


SCOPE = "/cg/session.scope"
PARENT = "/cg"
LEAF = SCOPE + "/init"


def synthetic(scope, parent, leaf=0):
    target = {
        "scope": SCOPE, "leaf": LEAF,
        "ancestors": [LEAF, SCOPE, PARENT],
    }
    files = {}
    for path, value in ((SCOPE, scope), (PARENT, parent), (LEAF, leaf)):
        raw = None if value is None else f"usage_usec {value}\n"
        files[path] = {"cpu.stat": {"raw": raw}}
    return {"targets": [target], "cgroups": files}


class ActivityTests(unittest.TestCase):
    def test_concurrent_activity_excludes_entire_scope_not_just_leaf(self):
        before = synthetic(100, 1000, 10)
        after = synthetic(130, 1100, 11)
        result = env.activity(before, after)
        self.assertEqual(len(result["rows"]), 1)
        row = result["rows"][0]
        self.assertEqual(row["scope_delta"]["delta_ns"], 30000)
        self.assertEqual(row["ancestor_delta"]["delta_ns"], 100000)
        self.assertEqual(row["outside_scope_cpu_ns"], 70000)
        self.assertEqual(row["status"], "observed_estimate")

    def test_nested_ancestors_are_not_added(self):
        before, after = synthetic(0, 0), synthetic(20, 50)
        for data, value in ((before, 100), (after, 180)):
            data["targets"][0]["ancestors"].append("/")
            data["cgroups"]["/"] = {
                "cpu.stat": {"raw": f"usage_usec {value}\n"}}
        result = env.activity(before, after)
        self.assertEqual([r["outside_scope_cpu_ns"] for r in result["rows"]],
                         [30000, 60000])
        self.assertIn("none", result["aggregation"])
        self.assertNotIn("total", result)

    def test_quiet_is_not_exclusive(self):
        before, after = synthetic(10, 100), synthetic(20, 110)
        result = env.activity(before, after)
        self.assertEqual(result["rows"][0]["outside_scope_cpu_ns"], 0)
        self.assertIn("never establishes exclusivity",
                      result["interpretation"])

    def test_regression_is_not_clamped_or_reported_as_quiet(self):
        for after in (synthetic(9, 110), synthetic(11, 99)):
            with self.subTest(after=after):
                row = env.activity(synthetic(10, 100), after)["rows"][0]
                self.assertEqual(row["status"], "counter_regression")
                self.assertIsNone(row["outside_scope_cpu_ns"])

    def test_negative_residual_is_invalid_not_zero(self):
        row = env.activity(synthetic(10, 100),
                           synthetic(40, 110))["rows"][0]
        self.assertEqual(row["status"], "inconsistent_nonatomic_counters")
        self.assertIsNone(row["outside_scope_cpu_ns"])

    def test_unavailable_and_malformed_counters(self):
        for missing in (SCOPE, PARENT):
            for raw in (None, "garbage", "usage_usec broken\n"):
                before = synthetic(10, 100)
                before["cgroups"][missing]["cpu.stat"]["raw"] = raw
                row = env.activity(before, synthetic(20, 120))["rows"][0]
                self.assertEqual(row["status"], "unavailable")
                self.assertIsNone(row["outside_scope_cpu_ns"])
        self.assertEqual(env.activity({}, {})["status"], "unavailable")

    def test_membership_or_mount_change_invalidates_delta(self):
        before, after = synthetic(10, 100), synthetic(20, 120)
        after["targets"][0]["leaf"] = SCOPE + "/other"
        row = env.activity(before, after)["rows"][0]
        self.assertEqual(row["status"], "membership_or_mount_changed")
        self.assertIsNone(row["outside_scope_cpu_ns"])

    def test_v1_cpuacct_fallback_has_nanosecond_units(self):
        data = {"cgroups": {SCOPE: {
            "cpu.stat": {"raw": "nr_periods 5\n"},
            "cpuacct.usage": {"raw": "12345\n"},
        }}}
        self.assertEqual(env.usage(data, SCOPE), 12345)
        data["cgroups"][SCOPE]["cpuacct.usage"]["raw"] = None
        self.assertIsNone(env.usage(data, SCOPE))


class DiscoveryTests(unittest.TestCase):
    def test_cgroup_mount_root_mapping_and_scope(self):
        raw = ("1 0 0:1 /user.slice /cg ro - cgroup2 cgroup rw\n"
               "2 0 0:2 / /other rw - ext4 /dev/sda rw\n")
        mounts = env.mount_records(raw)
        self.assertEqual(len(mounts), 1)
        targets = env.cgroup_targets(
            "0::/user.slice/session-5.scope/init\n", mounts)
        target = targets[0]
        self.assertEqual(target["leaf"], "/cg/session-5.scope/init")
        self.assertEqual(target["scope"], "/cg/session-5.scope")
        self.assertEqual(target["ancestors"],
                         [target["leaf"], target["scope"], "/cg"])

    def test_no_scope_is_explicitly_membership_only(self):
        mounts = env.mount_records("1 0 0:1 / /cg ro - cgroup2 cg rw")
        target = env.cgroup_targets("0::/container/init", mounts)[0]
        self.assertEqual(target["scope"], target["leaf"])
        self.assertIn("no_session_scope_found", target["scope_basis"])

    def test_v1_controller_matching_and_escaped_mounts(self):
        raw = (r"1 0 0:1 / /cg\040cpu rw - cgroup cg rw,cpu,cpuacct"
               "\n2 0 0:2 / /memory rw - cgroup cg rw,memory\n")
        targets = env.cgroup_targets("2:cpu,cpuacct:/session.scope",
                                     env.mount_records(raw))
        self.assertEqual(len(targets), 1)
        self.assertEqual(targets[0]["scope"], "/cg cpu/session.scope")

    def test_unavailable_discovery_and_hidden_roots(self):
        self.assertEqual(env.mount_records(None), [])
        self.assertEqual(env.cgroup_targets(None, []), [])
        mounts = env.mount_records("1 0 0:1 /hidden /cg ro - cgroup2 cg rw")
        self.assertEqual(env.cgroup_targets("0::/elsewhere", mounts), [])
        mounts[0]["root"] = "/"
        self.assertEqual(env.cgroup_targets("0::/../escape", mounts), [])

    def test_read_errors_are_preserved_not_empty_success(self):
        for exc in (FileNotFoundError("missing"), PermissionError("denied")):
            with patch.object(env.Path, "read_text", side_effect=exc):
                result = env.read_file("/synthetic/missing")
            self.assertIsNone(result["raw"])
            self.assertTrue(result["error"])

    def test_entirely_unavailable_snapshot_is_safe(self):
        unavailable = {"raw": None, "error": "synthetic unavailable"}
        with patch.object(env, "read_file", return_value=unavailable), \
                patch.object(env, "namespaces", return_value={}), \
                patch.object(env, "disk_space", return_value={}):
            result = env.snapshot()
        self.assertEqual(result["targets"], [])
        self.assertEqual(result["cgroups"], {})
        self.assertEqual(result["mountinfo"]["error"], unavailable["error"])


class ReportTests(unittest.TestCase):
    def test_always_fail_closed_for_busy_quiet_or_missing(self):
        cases = [(synthetic(10, 100), synthetic(20, 150)),
                 (synthetic(10, 100), synthetic(20, 110)), ({}, {})]
        for before, after in cases:
            with self.subTest(before=before), \
                    patch.object(env, "snapshot", side_effect=[
                        copy.deepcopy(before), copy.deepcopy(after)]), \
                    patch.object(env, "cpuinfo", return_value={}), \
                    patch.object(env.time, "sleep") as sleep:
                result = env.collect()
                sleep.assert_called_once_with(2.0)
            self.assertEqual(result["status"], "exclusive_not_verified")
            self.assertFalse(result["exclusive_verified"])
            self.assertTrue(result["diagnostic_only"])
            self.assertTrue(any("quiet" in x for x in result["limitations"]))


if __name__ == "__main__":
    unittest.main()
