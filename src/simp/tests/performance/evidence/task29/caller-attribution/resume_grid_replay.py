#!/usr/bin/env python3
"""Finish the archived grid replay after the recorded 900s process timeout.

The prefix log contains a line only AFTER the original check_report returns.
This is locally trusted checkpoint evidence, not hostile-producer proof. All
archives are resealed here; the prefix is not reanalysed a second time. Every
suffix cell uses the original admission/statistics without changes. There is
no new timing experiment or numerical policy in this script.
"""
import gzip
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2]))
import task29_gate as gate

root = HERE.parent / "full-grid"
log = HERE / "grid-prefix.log.gz"
lines = gzip.decompress(log.read_bytes()).decode().splitlines()
prefix = []
for line in lines:
    marker, case, size = line.split()
    assert marker == "REPLAY"
    prefix.append((case, int(size)))
assert prefix == gate.keys()[:len(prefix)] and len(prefix) == 135
inventory = gate.a.load(root / "inventory.json")
assert inventory["driver"] == gate.a.seal(gate.__file__)
assert [(r["case"], r["size"]) for r in inventory["runs"]] == gate.keys()
reports, suffix = {}, []
for i, row in enumerate(inventory["runs"]):
    key = row["case"], row["size"]
    archive = gate.a.safe_child(root, row["archive"])
    assert gate.a.seal(archive) == row["seal"]
    with tempfile.TemporaryDirectory(prefix="task29-replay-suffix-") as tmp:
        folder = Path(tmp) / "unpacked"
        assert gate.bundle.unpack(archive, folder) == row["files"]
        report = gate.a.load(folder / "acceptance.json")
        assert row["exit"] == gate.a.report_exit_status(report)
        assert row["protocol"] == report["success"]
        if i >= len(prefix):
            gate.check_report(folder, report, inventory["baseline"],
                inventory["candidate"], inventory["seconds"], *key)
            suffix.append(key)
            print("REPLAY_SUFFIX %s %d" % key, flush=True)
        reports[key] = report
assert gate.summary(reports) == gate.a.load(root / "decisions.json")
receipt = dict(status="blocked", prefix_cells=len(prefix),
    suffix_cells=suffix, total_cells=len(reports),
    prefix_log=gate.a.seal(log), driver=gate.a.seal(gate.__file__),
    inventory=gate.a.seal(root / "inventory.json"),
    decisions=gate.a.seal(root / "decisions.json"),
    protocol="135 completed cells before timeout; remaining 27 reanalysed; "
             "all 162 archive seals and aggregate decisions rechecked")
with (HERE / "grid-resumed.json").open("x") as stream:
    json.dump(receipt, stream, indent=2)
    stream.write("\n")
print(json.dumps(receipt, sort_keys=True))
