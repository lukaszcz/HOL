"""The reviewed table of the TASK31 candidate, as the timing grid reads it.

The data is task31_attributed.json (a separate file, so that adding a
reviewed file changes no seal of the counts: it is not among the sealed
files of the timing table; every record carries its seal instead):

    {"schema": "task31-attributed-v1",
     "entries": [{"path", "kind", "baseline_blob", "candidate_blob",
                  "reason", "gate"}, ...],
     "history": {SHA256 OF AN EARLIER FILE: [its entries]}}

This module reads and validates that file and projects it onto the sources
of a timing table (`pins`, `pin_history`): the pins a timing grid is judged
by. It is sealed into the timing table (task31_grid.SEALED), so the timing
grid seals the code that computes its pins; it imports nothing of the
identity gate (task31_attribution.py, which imports this module).
`kind` is one of

- `source`: a simplifier source that a cell elaborates and whose private
  copy differs between the two sides; a cell whose every difference is of
  such entries is `attributed`;
- `heap`: a file of the shared heap (hol.state0), which both sides load;
- `build`: a build file (Holmakefile, MANIFEST, a .ML tool script, a
  project file) of a directory a cell loads from, or a file of a name
  Holmake reads beside the directories it builds in (UPWARD), wherever it
  is.

`gate` names what measures the difference. `baseline_blob` is the git blob
at the baseline (null for a file the baseline lacks). `candidate_blob` is
the reviewed git blob at the candidate; null is the placeholder of an entry
whose blob is to be filled at integration, and the identity grid refuses to
run while one is left.
"""
import json
import re

import acceptance as a

FILE = a.HERE / "task31_attributed.json"
SCHEMA = "task31-attributed-v1"
KINDS = ("source", "heap", "build")
FIELDS = ("baseline_blob", "candidate_blob", "gate", "kind", "path",
          "reason")
SOURCE_SUFFIXES = (".sml", ".sig")


def blob_ok(value):
    return value is None or (isinstance(value, str) and re.fullmatch(
        "[0-9a-f]{40}", value) is not None)


def validate(entries):
    """The entries, if they are well formed: exact fields, a known kind,
    blob-or-null, a reason and a gate, sorted by path, no path twice, the
    two blobs of an entry different."""
    a.require(isinstance(entries, list), "malformed attribution entries")
    for e in entries:
        a.require(isinstance(e, dict) and sorted(e) == list(FIELDS),
                  "malformed attribution entry: %r" % (e,))
        a.require(isinstance(e["path"], str) and e["path"] and
                  e["kind"] in KINDS, "malformed attribution entry: %r"
                  % (e,))
        a.require(blob_ok(e["baseline_blob"]) and
                  blob_ok(e["candidate_blob"]),
                  "attribution blob is not a git blob: " + e["path"])
        a.require(all(isinstance(e[k], str) and e[k].strip()
                      for k in ("reason", "gate")),
                  "attribution without a reason and a gate: " + e["path"])
        a.require(e["kind"] == "build" or
                  e["path"].endswith(SOURCE_SUFFIXES),
                  "a %s attribution is of a source file: %s"
                  % (e["kind"], e["path"]))
        a.require(e["candidate_blob"] is None or
                  e["candidate_blob"] != e["baseline_blob"],
                  "attribution blobs do not differ: " + e["path"])
    paths = [e["path"] for e in entries]
    a.require(paths == sorted(set(paths)),
              "attribution entries are not sorted and unique by path")
    return entries


def load(path=None):
    """The document of the attribution file (validated): {entries, history}
    and the seal of the file."""
    path = FILE if path is None else path
    found = json.loads(path.read_text())
    a.require(isinstance(found, dict) and sorted(found) == [
        "entries", "history", "schema"] and found["schema"] == SCHEMA,
        "not a TASK31 attribution file: %s" % path)
    validate(found["entries"])
    a.require(isinstance(found["history"], dict), "malformed history")
    for seal, earlier in found["history"].items():
        a.require(re.fullmatch("[0-9a-f]{64}", seal) is not None,
                  "malformed attribution history key")
        validate(earlier)
    return dict(entries=found["entries"], history=found["history"],
                seal=a.seal(path))


def pins(entries, within):
    """The pins of a timing table: {path: {blob, reason}} of the filled
    entries whose path is one of `within`, the table's sources. The other
    entries (the shared heap and the build files) are no source of the
    table: adding one changes no pin."""
    within = set(within)
    return {e["path"]: dict(blob=e["candidate_blob"], reason=e["reason"])
            for e in entries
            if e["candidate_blob"] is not None and e["path"] in within}


def pin_history(document, within):
    """The pins of each earlier version of the file (by its sha256), as
    `pins` reads them."""
    return {seal: pins(earlier, within)
            for seal, earlier in document["history"].items()}
