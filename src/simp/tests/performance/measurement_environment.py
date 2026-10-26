#!/usr/bin/env python3
"""Read-only TASK29A environment diagnostic; never certifies exclusivity.

Run from any directory with --output NEW.json. Only the requested output is
written; no workloads, builds, affinity changes or cgroup writes are made.
The two-second sample observes activity, not benchmark performance.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import time


STATUS = "exclusive_not_verified"
SAMPLE_SECONDS = 2.0
CGROUP_FILES = (
    "cpu.stat", "cpu.max", "cpu.max.burst", "cpu.weight",
    "cpu.cfs_quota_us", "cpu.cfs_period_us", "cpu.shares",
    "cpuacct.usage", "cpuset.cpus", "cpuset.cpus.effective",
    "cpuset.effective_cpus", "cpuset.mems", "cpuset.mems.effective",
    "memory.current", "memory.max", "memory.high", "memory.low",
    "memory.min", "memory.peak", "memory.stat", "memory.events",
    "memory.swap.current", "memory.swap.max", "memory.usage_in_bytes",
    "memory.limit_in_bytes", "memory.memsw.limit_in_bytes",
)
LIMITATIONS = [
    "A quiet two-second sample cannot prove exclusive host access.",
    "Namespaces, containers, VMs and unreadable ancestors hide activity.",
    "Counters are read sequentially, not atomically; deltas are estimates.",
    "Ancestor-minus-scope rows overlap: never sum them.",
    "Affinity, capabilities and CPU limits are not exclusivity guarantees.",
    "No benchmark, performance admission or causal noise claim is made.",
]


def read_file(path):
    try:
        return {"raw": Path(path).read_text(), "error": None}
    except (OSError, UnicodeError) as exc:
        return {"raw": None, "error": str(exc)}


def stamp():
    return {
        "utc": datetime.now(timezone.utc).isoformat(),
        "monotonic_ns": time.monotonic_ns(),
    }


def unescape_mount(text):
    return re.sub(r"\\([0-7]{3})",
                  lambda match: chr(int(match[1], 8)), text)


def mount_records(raw):
    records = []
    for line in (raw or "").splitlines():
        left, sep, right = line.partition(" - ")
        fields, tail = left.split(), right.split()
        if not sep or len(fields) < 6 or len(tail) < 3:
            continue
        if tail[0] not in ("cgroup", "cgroup2"):
            continue
        records.append({
            "raw": line, "root": unescape_mount(fields[3]),
            "mountpoint": unescape_mount(fields[4]), "kind": tail[0],
            "controllers": tail[2].split(","),
        })
    return records


def cgroup_targets(cgroup_raw, mounts):
    targets = []
    for line in (cgroup_raw or "").splitlines():
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        _, names, member = parts
        controllers = names.split(",") if names else []
        for mount in mounts:
            if controllers:
                if not set(controllers) & set(mount["controllers"]):
                    continue
            elif mount["kind"] != "cgroup2":
                continue
            root = Path(mount["root"])
            try:
                relative = Path(member).relative_to(root)
            except ValueError:
                continue
            if ".." in relative.parts:
                continue
            base = Path(mount["mountpoint"])
            leaf = base / relative
            scopes = [p for p in [leaf, *leaf.parents]
                      if p.is_relative_to(base) and
                      p.name.endswith(".scope")]
            scope = scopes[0] if scopes else leaf
            targets.append({
                "membership": member, "controllers": controllers,
                "mount": mount, "leaf": str(leaf), "scope": str(scope),
                "scope_basis": ("nearest_enclosing_scope" if scopes else
                                "membership_only_no_session_scope_found"),
                "ancestors": [str(p) for p in [leaf, *leaf.parents]
                              if p.is_relative_to(base)],
            })
    return targets


def namespaces():
    result = {}
    try:
        paths = sorted(Path("/proc/self/ns").iterdir())
    except OSError as exc:
        return {"error": str(exc)}
    for path in paths:
        try:
            result[path.name] = {"target": os.readlink(path)}
        except OSError as exc:
            result[path.name] = {"error": str(exc)}
    return result


def cpuinfo():
    source = read_file("/proc/cpuinfo")
    raw = source.pop("raw")
    if raw is None:
        return source
    fields = {}
    processors = 0
    selected = {
        "vendor_id", "model name", "cpu family", "model", "stepping",
        "microcode", "cpu cores", "siblings", "flags", "Features",
        "CPU implementer", "CPU architecture", "CPU variant", "CPU part",
        "CPU revision", "Hardware", "Revision",
    }
    for line in raw.splitlines():
        key, sep, value = line.partition(":")
        key, value = key.strip(), value.strip()
        processors += int(bool(sep) and key == "processor")
        if sep and key in selected:
            fields.setdefault(key, set()).add(value)
    return {
        "source": "/proc/cpuinfo", "error": None,
        "raw_sha256": hashlib.sha256(raw.encode()).hexdigest(),
        "processor_records": processors,
        "unique_selected_fields": {k: sorted(v) for k, v in fields.items()},
        "note": "Deduplicated identity/features; volatile MHz omitted.",
    }


def disk_space():
    result = {}
    for path in dict.fromkeys([os.getcwd(), "/", "/tmp"]):
        try:
            stat = os.statvfs(path)
            result[path] = {
                "device": os.stat(path).st_dev,
                "total_bytes": stat.f_blocks * stat.f_frsize,
                "available_bytes": stat.f_bavail * stat.f_frsize,
                "free_inodes": stat.f_favail,
            }
        except OSError as exc:
            result[path] = {"error": str(exc)}
    return result


def snapshot():
    start = stamp()
    membership = read_file("/proc/self/cgroup")
    mountinfo = read_file("/proc/self/mountinfo")
    mounts = mount_records(mountinfo["raw"])
    targets = cgroup_targets(membership["raw"], mounts)
    paths = sorted({p for t in targets for p in t["ancestors"]})
    status = read_file("/proc/self/status")
    if status["raw"] is not None:
        status["raw"] = "\n".join(
            line for line in status["raw"].splitlines()
            if line.split(":", 1)[0] in {
                "Name", "Pid", "PPid", "NSpid", "Uid", "Gid",
                "CapInh", "CapPrm", "CapEff", "CapBnd", "CapAmb",
                "NoNewPrivs", "Seccomp", "Cpus_allowed",
                "Cpus_allowed_list", "Mems_allowed_list",
            }) + "\n"
    try:
        affinity = {"cpus": sorted(os.sched_getaffinity(0))}
    except (AttributeError, OSError) as exc:
        affinity = {"error": str(exc)}
    return {
        "read_start": start,
        "membership": membership,
        "mountinfo": {
            "raw": "\n".join(m["raw"] for m in mounts),
            "error": mountinfo["error"], "filter": "cgroup/cgroup2 only",
        },
        "targets": targets,
        "cgroups": {p: {f: read_file(Path(p) / f) for f in CGROUP_FILES}
                    for p in paths},
        "namespaces": namespaces(), "status": status,
        "affinity": affinity,
        "system": {p: read_file(p) for p in (
            "/proc/stat", "/proc/loadavg", "/proc/diskstats",
            "/sys/devices/system/cpu/online",
            "/sys/devices/system/cpu/isolated",
            "/sys/devices/system/cpu/possible",
        )},
        "disk_space": disk_space(), "read_end": stamp(),
    }


def usage(snapshot_data, path):
    files = snapshot_data.get("cgroups", {}).get(path, {})
    raw = files.get("cpu.stat", {}).get("raw")
    try:
        fields = dict(line.split() for line in (raw or "").splitlines())
        if "usage_usec" in fields:
            return int(fields["usage_usec"]) * 1000
        raw = files.get("cpuacct.usage", {}).get("raw")
        return int(raw) if raw is not None else None
    except (ValueError, TypeError):
        return None


def counter_delta(before, after):
    if before is None or after is None:
        return {"status": "unavailable", "delta_ns": None}
    if before < 0 or after < before:
        return {"status": "counter_regression", "delta_ns": None}
    return {"status": "observed", "delta_ns": after - before}


def activity(before, after):
    """Independent ancestor residuals, not a sum of nested counters."""
    rows = []
    after_targets = after.get("targets", [])
    for target in before.get("targets", []):
        scope = target["scope"]
        ancestors = target["ancestors"]
        if scope not in ancestors:
            continue
        scope_delta = counter_delta(usage(before, scope),
                                    usage(after, scope))
        for ancestor in ancestors[ancestors.index(scope) + 1:]:
            total = counter_delta(usage(before, ancestor),
                                  usage(after, ancestor))
            row = {"scope": scope, "ancestor": ancestor,
                   "scope_delta": scope_delta, "ancestor_delta": total,
                   "outside_scope_cpu_ns": None}
            if target not in after_targets:
                row["status"] = "membership_or_mount_changed"
            elif scope_delta["status"] != "observed":
                row["status"] = scope_delta["status"]
            elif total["status"] != "observed":
                row["status"] = total["status"]
            else:
                residual = total["delta_ns"] - scope_delta["delta_ns"]
                if residual < 0:
                    row["status"] = "inconsistent_nonatomic_counters"
                else:
                    row["status"] = "observed_estimate"
                    row["outside_scope_cpu_ns"] = residual
            rows.append(row)
    valid = [r for r in rows if r["status"] == "observed_estimate"]
    return {
        "status": "observed_estimates" if valid else "unavailable",
        "rows": rows,
        "aggregation": "none; ancestors and controller mounts may overlap",
        "coverage": "Visible ancestors only; not verified whole host.",
        "interpretation": (
            "Positive residual is concurrent CPU outside the selected scope; "
            "zero or unavailable never establishes exclusivity."),
    }


def collect():
    started = stamp()
    before = snapshot()
    wait_start = stamp()
    time.sleep(SAMPLE_SECONDS)
    wait_end = stamp()
    after = snapshot()
    return {
        "schema": 1, "task": "TASK29A", "diagnostic_only": True,
        "status": STATUS, "exclusive_verified": False,
        "limitations": LIMITATIONS, "started": started,
        "requested_sample_seconds": SAMPLE_SECONDS,
        "sleep_bracket": {"before": wait_start, "after": wait_end},
        "before": before, "after": after, "cpuinfo": cpuinfo(),
        "non_session_cpu_activity": activity(before, after),
        "finished": stamp(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    # Exclusive creation prevents accidentally replacing historical evidence.
    if args.output.exists():
        parser.error("output already exists; choose a new evidence path")
    report = collect()
    report["collector"] = {
        "path": str(Path(__file__).resolve()),
        "sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(f"{STATUS}: {args.output}")


if __name__ == "__main__":
    main()
