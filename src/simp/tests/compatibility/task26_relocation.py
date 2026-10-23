"""Physical relocation composed after the immutable TASK10 typed mapping."""
import copy
import gzip
import json
import re

from run_paired import HERE, fingerprint, git, require

REPO = HERE.parents[3]
SUPPLEMENT = HERE / "migration/task26-relocation.json"
NATIVE = "src/simp/src/selftest.sml"
DESTINATION = "src/simp/tests/native-extension/selftest.sml"


def apply(typed):
    spec = json.loads(SUPPLEMENT.read_text())
    require(spec["schema"] == 1 and spec["task"] == "TASK_26",
            "unknown physical relocation schema")
    require(fingerprint(HERE / "migration/task10-relocation.json") ==
            spec["typed_mapping"], "changed typed relocation input")
    require(spec["from"] == NATIVE and spec["to"] == DESTINATION,
            "unexpected physical relocation")
    require(fingerprint(REPO / DESTINATION) == spec["source"] ==
            typed["sources"][NATIVE]["current"],
            "physical relocation changed native assertion bytes")
    # The ordinary selftest is the COMPLETE pinned develop input, not an
    # extraction of selected old cases or a generated smaller oracle.
    original = HERE / "inputs/develop/selftest.sml"
    require(fingerprint(original) == spec["original"],
            "changed original selftest input")
    require(original.read_bytes() == git(REPO, "show", spec["baseline"] +
            ":" + NATIVE) == (REPO / NATIVE).read_bytes(),
            "ordinary selftest differs from pinned develop")
    result = copy.deepcopy(typed)
    record = result["sources"][NATIVE]
    record["current_path"] = DESTINATION
    for anchor in record["current_anchors"]:
        anchor["path"] = DESTINATION
    for row in result["anchors"]:
        if row["current"]["path"] == NATIVE:
            row["current"]["path"] = DESTINATION
    for row in result["native"]["additions"]:
        for anchor in row["sources"]:
            anchor["path"] = DESTINATION
    return result


def validate_vectors(text):
    original = gzip.decompress((HERE.parent /
        "performance/review-20261021/native-selftest.log.gz").read_bytes())

    def vectors(source):
        return [line for line in source.splitlines()
                if re.match(r"[A-Z_]+_RESULTS ", line)]

    expected = vectors(original.decode())
    require(len(expected) == 11 and vectors(text) == expected,
            "missing/changed native aggregate observations")
    require(text.endswith("\n") and "FAILED!" not in text and
            "Static Errors" not in text, "incomplete/failed native output")
