"""Explicit TASK_10 relocation overlay; the TASK_06 oracle stays immutable.

No source mismatch or extra event is accepted without this reviewed supplement.
Historical Git blobs are verified against the frozen source hashes, not HEAD.
"""
import json
from functools import lru_cache

from run_paired import HERE, digest, fingerprint, git, require

REPO = HERE.parents[3]
SUPPLEMENT = HERE / "migration/task10-relocation.json"
LEDGER = HERE / "coverage-ledger.json.gz"
NATIVE = "src/simp/src/selftest.sml"


def key(anchor):
    return json.dumps(anchor, sort_keys=True)


def load():
    import task26_relocation
    return task26_relocation.apply(json.loads(SUPPLEMENT.read_text()))


def pinned_revisions():
    """Every revision the relocation records read, taken from the data."""
    import task26_relocation
    revisions = {r["old_revision"] for r in
                 json.loads(SUPPLEMENT.read_text())["sources"].values()
                 if "old_revision" in r}
    revisions.add(json.loads(
        task26_relocation.SUPPLEMENT.read_text())["baseline"])
    return sorted(revisions)


def historical_source(path, record):
    data = git(REPO, "show", record["old_revision"] + ":" + path)
    require({"sha256": digest(data), "bytes": len(data)} == record["old"],
            "stale source relocation history: " + path)
    return data.decode()


@lru_cache(maxsize=16)
def source_literals(path, text):
    from coverage_ledger import text_literals
    return {key(a) for a in text_literals(path, text)}


def check_anchor(anchor, text):
    lines = text.splitlines()
    line = anchor["line"]
    require(0 < line <= len(lines), "relocation anchor outside source")
    if "text" in anchor:
        require(lines[line - 1] == anchor["text"],
                "stale relocation expression anchor")
    else:
        # Use the same literal extraction/escaping as the frozen ledger.
        require(key(anchor) in source_literals(anchor["path"], text),
                "stale relocation literal anchor")


def verify(ledger, supplement=None):
    relocation = load() if supplement is None else supplement
    require(relocation["schema"] == 1 and relocation["task"] == "TASK_10",
            "unknown relocation schema")
    require(fingerprint(LEDGER) == relocation["frozen_ledger"],
            "changed frozen relocation ledger")
    sources = relocation["sources"]
    require(set(sources) == {NATIVE,
            "src/simp/tests/split-registration/selftest.sml",
            "src/simp/tests/split-persistence/selftest.sml",
            "src/simp/tests/split-persistence/verify.ML",
            "src/simp/tests/fresh-load/syntax.ML",
            "src/simp/tests/fresh-load/identity-before.ML",
            "src/simp/tests/fresh-load/identity-after.ML",
            "src/simp/tests/split-persistence/heapSave.ML",
            "src/simp/tests/split-persistence/heapVerify.ML"},
            "unexpected TASK_10 relocation source")
    old_text, current_text = {}, {}
    for path, record in sources.items():
        require(record["old"] == ledger["sources"][path],
                "stale source relocation origin: " + path)
        destination = record.get("current_path", path)
        require(destination == (
            "src/simp/tests/native-extension/selftest.sml"
            if path == NATIVE else path), "wrong physical destination")
        require(fingerprint(REPO / destination) == record["current"],
                "stale source relocation destination: " + path)
        old_text[path] = historical_source(path, record)
        current_text[path] = (REPO / destination).read_text()
        require(record["decision"], "missing source relocation decision")
        for side, text in (("old", old_text[path]),
                           ("current", current_text[path])):
            require(record[side + "_anchors"], "missing import/body anchors")
            for anchor in record[side + "_anchors"]:
                require(anchor["path"] == (path if side == "old" else
                        destination), "wrong source anchor path")
                check_anchor(anchor, text)

    expected = {key(a) for suite in ledger["suites"].values()
                for case in suite["cases"] for a in case["sources"]
                if a["path"] in sources}
    moved = {}
    for row in relocation["anchors"]:
        before, after = row["old"], row["current"]
        require(key(before) not in moved, "duplicate relocation anchor")
        path = before["path"]
        require(path in sources and after["path"] ==
                sources[path].get("current_path", path),
                "unexpected anchor destination")
        check_anchor(before, old_text[path])
        check_anchor(after, current_text[path])
        moved[key(before)] = after
    require(set(moved) == expected, "missing/extra relocated case anchor")

    suite = relocation["native"]
    frozen = ledger["suites"]["native"]
    stream = suite["stream"]
    checks = [s for s in stream if s.endswith(" ... OK") and
              not s.startswith("OBS ")]
    require(len(checks) == suite["checks"] == 642,
            "wrong relocated native check count")
    positions = suite["original_event_positions"]
    require(len(positions) == len(frozen["stream"]) and
            positions == sorted(set(positions)) and
            all(1 <= p <= len(stream) for p in positions),
            "lost ordered frozen native event")
    require([stream[p - 1] for p in positions] == frozen["stream"],
            "changed frozen native subsequence")
    extras = [s for i, s in enumerate(stream, 1) if i not in positions]
    require(len(extras) == 12 and all(s.startswith("extension registry: R4 ")
            and s.endswith(" ... OK") for s in extras),
            "unexpected added native event")
    rows = suite["cases"]
    require(len(rows) == len(frozen["cases"]) == 630,
            "lost original native case mapping")
    mapped = []
    for before, row in zip(frozen["cases"], rows):
        require(row["id"] == before["id"], "changed stable relocation ID")
        number = row["current_check"]
        require(1 <= number <= len(checks) and
                checks[number - 1] == before["label"] + " ... OK",
                "changed relocated native case")
        require(row["decision"] in relocation["decisions"],
                "missing typed body decision")
        require(row["anchor_ids"] and
                [relocation["anchors"][i]["old"] for i in row["anchor_ids"]]
                == before["sources"], "wrong relocated case anchors")
        mapped.append(number)
    require(mapped == sorted(set(mapped)), "reordered original native cases")
    additions = suite["additions"]
    require([r["current_check"] for r in additions] ==
            [i for i in range(1, 643) if i not in mapped],
            "unmapped added native check")
    r4 = {c["id"]: c for c in frozen["cases"]
          if c["label"].startswith("R4 ")}
    require([r["repeats"] for r in additions] == list(r4),
            "changed extension registry repeat order")
    for row in additions:
        require(row["repeats"] in r4, "added check is not an R4 repeat")
        # testutils truncates tprint labels to 73 columns with TERM=dumb.
        expected = ("extension registry: " + r4[row["repeats"]]["label"])[:73]
        require(checks[row["current_check"] - 1] == expected + " ... OK",
                "changed extension registry assertion label")
        require(row["sources"], "unanchored added native check")
        for anchor in row["sources"]:
            require(anchor["path"] == sources[NATIVE].get(
                "current_path", NATIVE), "wrong added-check source")
            check_anchor(anchor, current_text[NATIVE])
    return moved


def validate_stream(ledger, label, stream, supplement=None):
    """Exact stream, including duplicates/warnings/OBS; never count-only."""
    relocation = load() if supplement is None else supplement
    expected = (relocation["native"]["stream"] if label == "native" else
                ledger["suites"][label]["stream"])
    require(stream == expected, "changed current native cases: " + label)
    if label == "native":
        positions = relocation["native"]["original_event_positions"]
        require([stream[p - 1] for p in positions] ==
                ledger["suites"][label]["stream"],
                "changed frozen native subsequence")
