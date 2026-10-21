#!/usr/bin/env python3
"""Recheck archived TASK_06 source binding, cases and explicit initial reds."""
import argparse
import gzip
import json
from pathlib import Path

import coverage_ledger as coverage
import prior_contracts as prior
import staging_contracts as staging
from run_paired import (BASE, HERE, digest, fingerprint, git, require)


def load(path):
    data = path.read_bytes()
    return json.loads(gzip.decompress(data) if path.suffix == ".gz" else data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    root, repo = args.evidence.resolve(), HERE.parents[3]
    ledger = load(HERE / "coverage-ledger.json.gz")
    coverage.verify(ledger)
    summary = {"cases": sum(s["checks"] for s in ledger["suites"].values()),
               "source_files": len(ledger["sources"]), "paired": {},
               "native": {}, "strict_red": {}}
    for name in ("current-head", "baseline-control", "strict-red"):
        folder = root / name
        manifest = load(folder / "manifest.json")
        require(manifest["success"] == (name != "strict-red"),
                "wrong experiment classification")
        for path, info in manifest["inputs"].items():
            require(fingerprint(repo / path) == info, "changed experiment input")
        for path, info in manifest["tools"].items():
            require(fingerprint(repo / path) == info, "changed experiment runtime")
        for selection, selected in manifest["selections"].items():
            for source in selected["sources"]:
                data = git(repo, "show", selected["revision"] + ":" +
                           source["git_path"])
                require(digest(data) == source["sha256"] and
                        len(data) == source["bytes"], "wrong selected Git source")
        rows = []
        for run in manifest["runs"]:
            record = load(folder / run["receipt"])
            require(record["exit"] == run["exit"], "changed archived exit")
            if record["accepted"]:
                selected = manifest["selections"][record["selection"]]
                private = Path(selected["private"])
                sources = {s["private_path"]: s for s in selected["sources"]}
                fixtures = selected["fixture_products"]
                for info in record["result"]["paths"].values():
                    path = Path(info["physical"])
                    if str(path) in sources:
                        expected = sources[str(path)]
                    elif path.is_relative_to(private):
                        expected = (fixtures[path.name] if path.name in fixtures
                                    else selected["products"][
                                        str(path.relative_to(private))])
                    else:
                        expected = fingerprint(path)
                    require(all(info[k] == expected[k] for k in
                                ("sha256", "bytes")), "archived source mismatch")
                if record["fixture"] in prior.FIXTURES:
                    observed = prior.validate(HERE, record["fixture"],
                        "\n".join(record["diagnostics"]) + "\n", require)
                    require(observed == record["prior"], "changed prior stream")
            if name != "strict-red":
                require(record["accepted"] == run["expected_acceptance"],
                        "failed/missing fixture normalized as success")
            rows.append({"receipt": run["receipt"], "exit": record["exit"],
                         "accepted": record["accepted"],
                         "outcome": record.get("result", {}).get("outcome"),
                         "checks": record.get("prior", {}).get("checks"),
                         "observations": record.get("prior", {}).get(
                             "observations")})
        summary["paired"][name] = rows
    current = root / "current-head"
    sig = load(current / "candidate-signature-none.json.gz")
    require(sig["exit"] == 1 and sig["result"]["outcome"] ==
            "expected-candidate-red", "initial signature red was hidden")
    behavior = load(current / "candidate-selftest-none.json.gz")
    require(behavior["result"]["outcome"] == "expected-candidate-red",
            "initial staging red was hidden")
    red = load(root / "strict-red/candidate-Staging-none.json.gz")
    events = [e for e in red["events"] if e[0] in ("observation", "check")]
    require(not red["accepted"] and red["exit"] == 0 and
            events == staging.expectation(HERE, "reviewed")["observations"],
            "strict red no longer has the known incompatibility")
    summary["strict_red"] = {"driver_exit": 1, "fixture_exit": red["exit"],
                             "accepted": False, "observed_checks": 57,
                             "required_checks": 60}
    native = load(root / "native/manifest.json")
    require(native["success"], "native run failed")
    for path, info in native["inputs"].items():
        require(fingerprint(repo / path) == info, "changed native input")
    for run in native["runs"]:
        record = load(root / "native" / run["receipt"])
        require(run["exit"] == record["exit"] == 0 and
                not record["timed_out"], "native process failed")
        if run["label"] != "build-focused":
            suite = ledger["suites"][run["label"]]
            require(record["stream"] == suite["stream"], "lost native case")
            summary["native"][run["label"]] = {
                "checks": suite["checks"], "observations": suite["observations"]}
    # The ledger generated from fresh receipts must equal the sealed input.
    fresh = coverage.build(root / "native", current)
    require(fresh == ledger, "fresh observations do not reproduce coverage ledger")
    for name in ("PriorOriginal", "PriorTraversal", "PriorExclusion", "PriorLimits"):
        a = load(current / ("baseline-" + name + "-none.json.gz"))
        b = load(current / ("candidate-" + name + "-none.json.gz"))
        require(a["prior"] == b["prior"], "legacy-equal stream changed")
    commands = load(root / "commands.json")
    require([r["exit"] for r in commands] == [0, 0, 0, 1],
            "wrong command/strict-red driver exits")
    require(git(repo, "show", BASE + ":src/simp/src/selftest.sml") ==
            (HERE / "inputs/develop/selftest.sml").read_bytes(),
            "original immutable input changed")
    summary["success"] = True
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
