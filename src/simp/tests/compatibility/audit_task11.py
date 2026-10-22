#!/usr/bin/env python3
"""Recheck TASK_11 source identity and archived executable receipts."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BASE = "cccaa27d7099cbadc886983020cbe745db7793f3"
RESTORED = ("Traverse.sig", "Traverse.sml", "congLib.sig", "congLib.sml")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    data = path.read_bytes()
    if path.suffix == ".gz":
        data = gzip.decompress(data)
    return json.loads(data)


def seal(data):
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def audit(folder):
    restored = {}
    for name in RESTORED:
        path = "src/simp/src/" + name
        expected = subprocess.check_output(
            ["git", "-C", str(REPO), "show", BASE + ":" + path])
        actual = (REPO / path).read_bytes()
        require(actual == expected, "legacy source drift: " + name)
        restored[path] = seal(actual)
    paired = load(folder / "paired/manifest.json")
    require(paired["success"], "paired run failed")
    for selection in ("baseline", "candidate"):
        for target in ("signature", "PublicTraverseAscription",
                       "PublicTraverseFunctor", "PublicTraverseClient"):
            r = load(folder / "paired" /
                     (selection + "-" + target + "-none.json.gz"))
            require(r["exit"] == 0 and r["accepted"] and
                    r["result"]["outcome"] == "pass",
                    "original client not executed/passing: " + target)
        for target, count in (("PriorOriginal", 73),
                              ("PriorTraversal", 47),
                              ("PriorExclusion", 929), ("PriorLimits", 6)):
            r = load(folder / "paired" /
                     (selection + "-" + target + "-none.json.gz"))
            require(r["exit"] == 0 and r["accepted"],
                    "paired contract failed: " + target)
            require(r["prior"]["checks"] == count,
                    "wrong original assertion count: " + target)
    native = load(folder / "native/manifest.json")
    require(native["success"] and native["coverage"][
        "current_native_checks"] == 642, "native suite incomplete")
    for path, expected in native["inputs"].items():
        require(seal((REPO / path).read_bytes()) == expected,
                "native input drift: " + path)

    sys.path.insert(0, str(HERE.parent / "performance"))
    from audit_evidence import audit as performance_audit
    from summarize import summarize
    experiments = {}
    for name in ("broad-control", "broad-candidate", "traversal-control",
                 "traversal-candidate"):
        root = folder / name
        manifest = load(root / "manifest.json")
        require(manifest["success"] and
                manifest["performance"]["pairs"] >= 10,
                "incomplete timing run: " + name)
        # A validation snapshot need not stay reachable in Git: every selected
        # source is independently bound to the landing files or pinned base.
        for side, selected in manifest["selections"].items():
            baseline = side == "baseline" or name.endswith("control")
            for source in selected["sources"]:
                path = source["git_path"]
                data = (subprocess.check_output(
                    ["git", "-C", str(REPO), "show", BASE + ":" + path])
                    if baseline else (REPO / path).read_bytes())
                require(seal(data) == {k: source[k] for k in
                                      ("sha256", "bytes")},
                        "selected source drift: " + name + ":" + path)
        count = 0
        for run in manifest["runs"]:
            r = load(root / run["receipt"])
            if r.get("fixture") != "performance":
                continue
            performance_audit(manifest, r)
            if name.startswith("traversal"):
                loaded = {Path(p).name for p in r["result"]["paths"]}
                require(not ({"simpLib.sml", "Cond_rewr.sml",
                              "TraverseExt.sml", "simpExtLib.sml"} & loaded),
                        "mixed engine loaded in direct traversal probe")
            count += 1
        summary = summarize(root)
        archived = load(root / "summary.json")
        require(summary == archived, "summary drift: " + name)
        experiments[name] = dict(receipts=count,
                                 workloads=list(summary["workloads"]))
    return dict(restored=restored, original_clients="pass",
                paired_contracts="exact frozen observations",
                native_checks=642, experiments=experiments)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("folder", type=Path,
                        help="TASK_11 evidence directory")
    args = parser.parse_args()
    print(json.dumps(audit(args.folder), indent=2))


if __name__ == "__main__":
    main()
