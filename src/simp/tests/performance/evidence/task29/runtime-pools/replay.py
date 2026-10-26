#!/usr/bin/env python3
"""Replay complete post-workload pools; exit 0 is NOT TASK29A acceptance."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PERF = HERE.parents[2]
sys.path.insert(0, str(PERF))
import evidence_bundle as bundle
import runtime_pools as pools
import measurement_environment as environment


def summarize(result, fragment):
    sides = {}
    for side in ("baseline", "candidate"):
        inv = result[side]
        codes = {c["address"]: c for c in inv["code"]}
        roots = {label: codes[root["fields"][0]["address"]]
                 for label, root in inv["roots"].items()}
        if fragment:
            roots["build"] = codes[inv["roots"]["run"]["fields"][1][
                "entry_code_address"]]
        sides[side] = roots
    roots = {}
    for label in sides["baseline"]:
        a, b = (sides[s][label] for s in ("baseline", "candidate"))
        roots[label] = dict(baseline_name=a["name"], candidate_name=b["name"],
            baseline_words=a["words"], candidate_words=b["words"],
            baseline_address_mod64=a["address"] % 64,
            candidate_address_mod64=b["address"] % 64,
            exact_native_words_equal=(a["native_words_sha256"] ==
                                      b["native_words_sha256"]),
            immediate_masked_words_equal=(
                a["code_references"]["normalized_instructions"] ==
                b["code_references"]["normalized_instructions"]),
            operands={s: sides[s][label]["code_references"]["references"]
                      for s in sides})
    return dict(scope="static pool/correspondence diagnostic, NOT parity",
        roots=roots,
        graph={s: {k: result[s][k] for k in (
            "total_words", "objects", "kinds", "split_pools",
            "unique_split_pools", "split_pool_words_with_headers",
            "split_pool_words_already_in_showSize", "pool_records",
            "omitted_pools", "unresolved_slots", "bad_addresses")}
            for s in sides},
        static_references={s: dict(
            all_code_unresolved=sum(c["code_references"][
                "unresolved_references"] for c in result[s]["code"]),
            split_code_unresolved=sum(c["code_references"][
                "unresolved_references"] for c in result[s]["code"]
                if c["pool_status"].startswith("split")),
            split_code_resolved=sum(sum(r["status"].startswith("resolved")
                for r in c["code_references"]["references"])
                for c in result[s]["code"]
                if c["pool_status"].startswith("split"))) for s in sides},
        raw_slot_correspondence=dict(matched=result["matched_objects"],
            matched_pools=result["matched_pools"],
            differences=len(result["differences"]),
            categories=dict(Counter(d.get("reason", d.get("field"))
                                    for d in result["differences"])),
            native_word_differences=len(result["native_word_differences"]),
            first_twelve_bfs_mismatches=result["differences"][:12]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate", action="store_true")
    args = parser.parse_args()
    validation = json.loads((HERE / "validation.json").read_text())
    pools.require(validation["schema"] == "task29-runtime-pools-validation-v1"
                  and validation["status"] == "blocked; NOT task acceptance",
                  "wrong validation scope")
    repo = PERF.parents[3]
    for name, fingerprint in validation["inputs"].items():
        path = repo / name
        pools.require(path.is_relative_to(repo) and
                      pools.seal(path) == fingerprint,
                      "changed attribution input")
    for name, fingerprint in validation["checks"].items():
        pools.require(Path(name).name == name and
                      pools.seal(HERE / name) == fingerprint,
                      "changed check log/environment")
    observed = json.loads((HERE / "environment.json").read_text())
    pools.require(observed["status"] == environment.STATUS and
        observed["exclusive_verified"] is False and
        observed["collector"]["sha256"] ==
        pools.seal(Path(environment.__file__))["sha256"] and
        observed["non_session_cpu_activity"] == environment.activity(
            observed["before"], observed["after"]),
        "changed environment derivation/scope")
    for name, fingerprint in validation["archives"].items():
        pools.require(Path(name).name == name and
                      pools.seal(HERE / name) == fingerprint,
                      "changed capture archive")
    results = {}
    for case in ("record", "collector"):
        archive = HERE / (case + ".json.xz")
        pools.require(pools.seal(archive) ==
                      validation["archives"][archive.name], "changed bundle")
        with tempfile.TemporaryDirectory(prefix="task29-pools-replay-") as tmp:
            dst = Path(tmp) / "data"
            bundle.unpack(archive, dst)
            options = [json.loads((dst / label / "paired/manifest.json")
                                 .read_text())["performance"] for label in
                       ("baseline-control", "baseline-candidate")]
            expected = (("frag_record", 0, 33554432) if case == "record" else
                        ("compile_collector", 10000, 64))
            pools.require(options[0] == options[1] and tuple(options[0][k]
                for k in ("case", "size", "batch_iterations")) == expected,
                "wrong diagnostic cell/schedule")
            results[case] = {}
            for label in ("baseline-control", "baseline-candidate"):
                manifest = json.loads((dst / label / "paired/manifest.json")
                                      .read_text())
                revision = validation["baseline" if
                    label == "baseline-control" else "candidate"]
                pools.require(manifest["selections"]["candidate"][
                    "revision"] == revision, "wrong diagnostic candidate")
                result = pools.replay(dst / label, repo,
                                      control=label == "baseline-control")
                results[case][label] = summarize(result, case == "record")
                print(case, label, "diagnostic replay OK", flush=True)
    path = HERE / "attribution.json"
    if args.generate:
        with path.open("x") as stream:
            stream.write(json.dumps(results, indent=2) + "\n")
    else:
        pools.require(results == json.loads(path.read_text()),
                      "changed pool attribution")
    print("TASK29A remains incomplete; no timing gate was evaluated.")


if __name__ == "__main__":
    main()
