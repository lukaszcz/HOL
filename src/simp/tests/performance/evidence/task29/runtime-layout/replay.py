#!/usr/bin/env python3
"""Replay post-workload objects; exit 0 means diagnostics, NOT TASK29A pass."""
import argparse
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PERF = HERE.parents[2]
sys.path.insert(0, str(PERF))
import evidence_bundle as bundle
import runtime_layout as layout


def code_at(inventory, address):
    matches = [c for c in inventory["code"] if c["address"] == address]
    layout.require(len(matches) == 1, "missing actual root code object")
    return matches[0]


def summarize(result, record):
    sides = {}
    for side in ("baseline", "candidate"):
        inv = result[side]
        rows = {label: code_at(inv, root["fields"][0]["address"])
                for label, root in inv["roots"].items()}
        if record:
            rows["build"] = code_at(inv, inv["roots"]["run"]["fields"][1][
                "entry_code_address"])
        sides[side] = rows
    roots = {}
    for label in sides["baseline"]:
        aa, bb = (sides[s][label] for s in ("baseline", "candidate"))
        roots[label] = dict(
            baseline_name=aa["name"], candidate_name=bb["name"],
            baseline_words=aa["words"], candidate_words=bb["words"],
            baseline_address_mod64=aa["address"] % 64,
            candidate_address_mod64=bb["address"] % 64,
            baseline_address_mod4096=aa["address"] % 4096,
            candidate_address_mod4096=bb["address"] % 4096,
            exact_native_words_equal=(aa["native_words_sha256"] ==
                                      bb["native_words_sha256"]),
            immediate_masked_words_equal=(
                aa["code_references"]["normalized_instructions"] ==
                bb["code_references"]["normalized_instructions"]),
            operands={s: sides[s][label]["code_references"]["references"]
                      for s in sides})
    return dict(
        scope="Actual root operands; names/masked words do NOT prove parity",
        roots=roots,
        graph={s: {k: result[s][k] for k in
                   ("total_words", "objects", "kinds", "split_pools",
                    "unresolved_slots", "bad_addresses")}
               for s in sides},
        raw_slot_correspondence=dict(
            matched=result["matched_objects"],
            differences=len(result["differences"]),
            native_word_differences=len(result["native_word_differences"])))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate", action="store_true")
    args = parser.parse_args()
    validation = json.loads((HERE / "validation.json").read_text())
    layout.require(validation["schema"] ==
                   "task29-runtime-layout-validation-v1" and
                   validation["status"] == "blocked; NOT task acceptance",
                   "wrong validation scope")
    for name, fingerprint in validation["inputs"].items():
        path = PERF.parents[3] / name
        layout.require(path.is_relative_to(PERF.parents[3]) and
                       layout.seal(path) == fingerprint,
                       "changed attribution input")
    for name, fingerprint in validation["checks"].items():
        layout.require(Path(name).name == name and
                       layout.seal(HERE / name) == fingerprint,
                       "changed test log")
    results = {}
    for case in ("record", "collector"):
        archive = HERE / (case + ".json.xz")
        layout.require(layout.seal(archive) == validation["archives"][archive.name],
                       "changed runtime layout bundle")
        with tempfile.TemporaryDirectory(prefix="task29-layout-replay-") as tmp:
            dst = Path(tmp) / "data"
            bundle.unpack(archive, dst)
            options = [json.loads((dst / label / "paired/manifest.json")
                                 .read_text())["performance"] for label in
                       ("baseline-control", "baseline-candidate")]
            layout.require(options[0] == options[1], "unequal paired schedules")
            expected = (("frag_record", 0, 33554432) if case == "record" else
                        ("compile_collector", 10000, 64))
            layout.require(tuple(options[0][k] for k in
                           ("case", "size", "batch_iterations")) == expected,
                           "wrong diagnostic cell/schedule")
            results[case] = {}
            for label in ("baseline-control", "baseline-candidate"):
                manifest = json.loads((dst / label / "paired/manifest.json")
                                      .read_text())
                expected_candidate = validation[
                    "baseline" if label == "baseline-control" else "candidate"]
                layout.require(manifest["selections"]["candidate"]["revision"] ==
                               expected_candidate, "wrong validation candidate")
                result = layout.replay(dst / label, PERF.parents[3],
                                       control=label == "baseline-control")
                results[case][label] = summarize(result, case == "record")
                print(case, label, "diagnostic replay OK", flush=True)
    path = HERE / "attribution.json"
    if args.generate:
        with path.open("x") as stream:
            stream.write(json.dumps(results, indent=2) + "\n")
    else:
        layout.require(results == json.loads(path.read_text()),
                       "changed root-operand attribution")
    print("TASK29A remains blocked; no timing gate was evaluated.")


if __name__ == "__main__":
    main()
