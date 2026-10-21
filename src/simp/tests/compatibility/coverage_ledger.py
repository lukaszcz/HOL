#!/usr/bin/env python3
"""Build/verify a source-tied case ledger. Never rewrite it implicitly in tests.

Relocation keeps old case IDs and assertions; update destinations explicitly.
The ledger includes ordered duplicate cases and complete observed parameters,
not merely aggregate check counts. Full sources are sealed, not copied here.
"""
import argparse
import gzip
import json
from pathlib import Path
import re

import prior_contracts as prior
from run_paired import HERE, fingerprint, require

REPO = HERE.parents[3]
SIMP = "src/simp/"
SUITES = {
    "original": ["tests/compatibility/inputs/develop/selftest.sml"],
    "traversal": ["tests/contracts/TraversalContracts.sml"],
    "exclusion": ["tests/contracts/" + n + ".sml" for n in
                  ("LegacyFailures", "ExclusionHistory", "ExclusionParsing")],
    "native": ["src/selftest.sml"],
    "limits": ["tests/compatibility/paired/PriorLimits.sml"],
    **{n: ["tests/" + n + "/selftest.sml"] for n in
       ("markers", "replay-order", "split-registration")},
    "fresh": ["tests/fresh-load/" + n for n in
              ("selftest.sml", "control.ML", "syntax.ML", "identity-before.ML",
               "identity-after.ML")],
    "persistence": ["tests/split-persistence/" + n for n in
                    ("selftest.sml", "verify.ML", "heapSave.ML", "heapVerify.ML",
                     "splitParentScript.sml", "splitChildScript.sml",
                     "splitDescendantScript.sml", "optIn.ML")]}


def text_literals(path, text):
    # Textual anchors, not an SML parser; hashes bind actual assertions.
    result = []
    for match in re.finditer(r'"(?:[^"\\\n]|\\.)*"', text):
        value = match.group()[1:-1]
        value = value.replace(r'\"', '"').replace(r'\\', '\\')
        result.append({"path": path, "line": text.count("\n", 0,
                       match.start()) + 1, "literal": value})
    return result


def literals(paths):
    return [a for path in paths for a in
            text_literals(path, (REPO / path).read_text())]


def anchors(label, choices):
    def score(value):
        if value == label:
            return len(value) + 1000
        if len(value) < 6:
            return 0
        if label.startswith(value) or label.endswith(value) or value in label:
            return len(value)
        if value.startswith(label):  # testutils terminal-width truncation
            return len(label)
        return 0
    scores = [(score(c["literal"]), c) for c in choices]
    best = max((s for s, _ in scores), default=0)
    return [c for s, c in scores if s == best and s > 0]


def case_anchors(name, number, label, choices):
    if name == "native":
        # Native selftest is sequential; constrain dynamic-label matching to
        # its actual block, never a later fixture with a similarly named term.
        blocks = [(1, 1), (87, 621), (107, 730), (160, 1534),
                  (180, 1875), (181, 1900), (232, 2489), (252, 2703),
                  (314, 2996), (325, 3131), (345, 3521), (350, 3592),
                  (371, 3681), (491, 3871), (503, 5020), (530, 5146),
                  (542, 5207), (548, 5269), (556, 5402), (582, 5598),
                  (607, 5717), (611, 5793), (615, 5855), (617, 5903),
                  (631, 6302)]
        low, high = next((line, end) for (start, line), (stop, end) in
                         zip(blocks, blocks[1:]) if start <= number < stop)
        choices = [c for c in choices if low <= c["line"] < high]
        if number == 177:
            # shouldfail uses printarg=term_to_string, not a literal label.
            path = SIMP + "src/selftest.sml"
            line = 1846
            return [{"path": path, "line": line,
                     "text": (REPO / path).read_text().splitlines()[line - 1]}]
    elif name == "exclusion":
        module = ("LegacyFailures.sml" if number <= 374 else
                  "ExclusionHistory.sml" if number <= 398 else
                  "ExclusionParsing.sml")
        choices = [c for c in choices if c["path"].endswith(
            (module, "LegacyFailures.sml"))]
    elif name == "traversal" and 40 <= number <= 43:
        choices = [c for c in choices if c["line"] == 366]
    return anchors(label, choices)


def receipt(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def build(native, paired):
    streams = {}
    fixtures = {"original": "PriorOriginal", "traversal": "PriorTraversal",
                "exclusion": "PriorExclusion", "limits": "PriorLimits"}
    for name, fixture in fixtures.items():
        record = receipt(paired / ("baseline-" + fixture + "-none.json.gz"))
        require(record["accepted"], "unaccepted paired evidence")
        streams[name] = record["prior"]["stream"]
    nm = json.loads((native / "manifest.json").read_text())
    require(nm["success"], "native experiment failed")
    for run in nm["runs"]:
        if run["label"] == "build-focused":
            continue
        record = receipt(native / run["receipt"])
        require(record["exit"] == 0 and not record["timed_out"],
                "failed native fixture")
        streams[run["label"]] = [
            "OBS load.path=$REPO/src/simp/src/simpLib" if
            s == "OBS load.path=" + str(REPO / "src/simp/src/simpLib")
            else s for s in record["stream"]]
    ledger = {"schema": 1, "policy": "preserve IDs/assertions on relocation",
              "sources": {}, "suites": {}}
    for name, stream in streams.items():
        group = "fresh" if name.startswith("fresh-") else name
        paths = [SIMP + p for p in SUITES[group]]
        for path in paths:
            ledger["sources"][path] = fingerprint(REPO / path)
        choices = literals(paths)
        cases, context, observations = [], [], []
        for event in stream:
            if event.startswith("OBS "):
                context.append(event)
                observations.append(event)
            elif event.endswith(" ... OK"):
                label = event[:-len(" ... OK")]
                cases.append({"id": name + ":" + str(len(cases) + 1).zfill(4),
                              "label": label, "sources": case_anchors(
                                  name, len(cases) + 1, label, choices),
                              "preceding_observations": context})
                context = []
        ledger["suites"][name] = {
            "checks": len(cases), "observations": len(observations),
            "cases": cases, "stream": stream,
            "classification": "legacy-equal" if name in fixtures else
                              "native mixed/cleanup; not baseline differential"}
    return ledger


def verify(ledger, supplement=None):
    import task10_relocation as relocation
    supplement = relocation.load() if supplement is None else supplement
    moved = relocation.verify(ledger, supplement)
    relocated_paths = supplement["sources"]
    source_literals = {p: literals([p]) for p in ledger["sources"]}
    for path, info in ledger["sources"].items():
        if path not in relocated_paths:
            require(fingerprint(REPO / path) == info,
                    "stale source ledger: " + path)
    for name, suite in ledger["suites"].items():
        require(suite["checks"] == len(suite["cases"]), "lost ledger case")
        labels = [s[:-len(" ... OK")] for s in suite["stream"]
                  if s.endswith(" ... OK") and not s.startswith("OBS ")]
        require(labels == [c["label"] for c in suite["cases"]],
                "changed case labels/order: " + name)
        for index, case in enumerate(suite["cases"], 1):
            require(case["id"] == name + ":" + str(index).zfill(4),
                    "changed stable case ID")
            require(case["sources"], "unmapped case: " + case["id"] + " " +
                    case["label"])
            for anchor in case["sources"]:
                anchor = moved.get(relocation.key(anchor), anchor)
                if "text" in anchor:
                    require((REPO / anchor["path"]).read_text().splitlines()[
                        anchor["line"] - 1] == anchor["text"],
                        "stale expression anchor: " + case["id"])
                else:
                    require(anchor in source_literals[anchor["path"]],
                            "stale case anchor: " + case["id"])
    for name, count in (("original", 73), ("traversal", 47),
                        ("exclusion", 929), ("native", 630), ("limits", 6)):
        require(ledger["suites"][name]["checks"] == count,
                "missing prior case family: " + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path)
    parser.add_argument("--paired", type=Path)
    parser.add_argument("--ledger", type=Path, default=HERE / "coverage-ledger.json.gz")
    args = parser.parse_args()
    if args.native or args.paired:
        require(args.native and args.paired, "both evidence paths required")
        require(not args.ledger.exists(), "refusing to overwrite coverage ledger")
        ledger = build(args.native, args.paired)
        args.ledger.write_bytes(gzip.compress(
            (json.dumps(ledger, indent=2) + "\n").encode(), mtime=0))
    else:
        ledger = receipt(args.ledger)
    verify(ledger)
    print("Source-tied cases:", sum(s["checks"] for s in ledger["suites"].values()))


if __name__ == "__main__":
    main()
