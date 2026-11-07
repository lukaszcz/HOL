"""The reviewed differences of the TASK31 candidate from the baseline.

The data is task31_attributed.json (a separate file, so that adding a
reviewed file changes no seal of the counts: it is not among the sealed
files of the timing table; every record carries its seal instead):

    {"schema": "task31-attributed-v1",
     "entries": [{"path", "kind", "baseline_blob", "candidate_blob",
                  "reason", "gate"}, ...],
     "history": {SHA256 OF AN EARLIER FILE: [its entries]}}

`kind` is one of

- `source`: a simplifier source that a cell elaborates and whose private
  copy differs between the two sides; a cell whose every difference is of
  such entries is `attributed`;
- `heap`: a file of the shared heap (hol.state0), which both sides load;
- `build`: a build file (Holmakefile, MANIFEST, a .ML tool script) of a
  directory a cell loads from.

`gate` names what measures the difference. `baseline_blob` is the git blob
at the baseline (null for a file the baseline lacks). `candidate_blob` is
the reviewed git blob at the candidate; null is the placeholder of an entry
whose blob is to be filled at integration, and the identity grid refuses to
run while one is left (`unfilled`).

`account` classifies every file below src/ that differs between the two
commits, from the git blobs and from the files the receipts show were
loaded: a file is attributed (an entry with exactly the blobs), or decisive
(loaded and unattributed, a build file of a loaded directory and
unattributed, an entry with other blobs), or not loaded (proved by the
receipts), or harness (installed from the checkout, the same file on both
sides).
"""
import json
import posixpath
import re

import acceptance as a
import timing_grid as tg

FILE = a.HERE / "task31_attributed.json"
SCHEMA = "task31-attributed-v1"
KINDS = ("source", "heap", "build")
FIELDS = ("baseline_blob", "candidate_blob", "gate", "kind", "path",
          "reason")
SOURCE_SUFFIXES = (".sml", ".sig")
BUILD_NAMES = ("Holmakefile", "MANIFEST")
# The performance harness is installed from the checkout, the same file in
# both private trees, and is bound by the harness seals and the checkout
# record; it is never read from either commit.
HARNESS_TREE = "src/simp/tests/"
DECISIVE = ("unattributed", "unattributed-build", "mismatch")


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


def digest(entries):
    """The seal of a table of entries."""
    import hashlib
    return hashlib.sha256(tg.canonical(entries).encode()).hexdigest()


def entries_of(document, seal):
    """The entries an inventory was judged by, given the seal of the file
    it recorded: the file's now, or those the history keeps."""
    if seal == document["seal"]:
        return document["entries"]
    a.require(isinstance(seal, dict) and seal.get("sha256") in
              document["history"], "changed attribution file")
    return document["history"][seal["sha256"]]


def paths(document):
    """Every path any version of the table names."""
    found = {e["path"] for e in document["entries"]}
    for earlier in document["history"].values():
        found |= {e["path"] for e in earlier}
    return sorted(found)


def unfilled(entries):
    """The paths whose candidate blob is still the placeholder."""
    return [e["path"] for e in entries if e["candidate_blob"] is None]


def pins(entries):
    """The pins of a timing table: {path: {blob, reason}} of the filled
    entries."""
    return {e["path"]: dict(blob=e["candidate_blob"], reason=e["reason"])
            for e in entries if e["candidate_blob"] is not None}


def pin_history(document):
    return {seal: pins(earlier)
            for seal, earlier in document["history"].items()}


def check_blobs(repo, baseline, candidate, entries):
    """Each entry names the git blobs of its file at the two commits. A
    refusal names every entry that does not, with the blob git has."""
    wrong = []
    for e in entries:
        have = (tg.git_blob(repo, baseline, e["path"]),
                tg.git_blob(repo, candidate, e["path"]))
        if have != (e["baseline_blob"], e["candidate_blob"]):
            wrong.append("%s (git: %s, %s)" % (e["path"], *have))
    a.require(not wrong, "the attribution names blobs git does not have "
              "at these commits: " + ", ".join(wrong))


def is_build(path):
    """Neither a source nor documentation: a build file in the wide sense
    (a Holmakefile, a manifest, a tool script, a data file)."""
    name = posixpath.basename(path)
    return name in BUILD_NAMES or not (
        name.endswith(SOURCE_SUFFIXES) or name.endswith(".md") or
        name.startswith("README"))


def account(blobs, entries, loaded):
    """{path: (class, note)} of every path of `blobs` whose two blobs
    differ. `blobs` is {path: {baseline, candidate}} (every path that
    differs below src/, and the sources), `loaded` the set of tracked paths
    that any measured cell loaded on either side (elaborated, found loaded,
    or in the initial heap). The classes:

    - attributed: an entry names exactly these blobs;
    - mismatch: an entry names other blobs;
    - unattributed: loaded, with no entry;
    - harness: below HARNESS_TREE and not loaded from the repository;
    - unattributed-build: a build file in a directory that something
      loaded came from, with no entry;
    - unloaded: no loaded file of either side is this one, and it is no
      build file of a loaded directory."""
    by_path = {e["path"]: e for e in entries}
    a.require(set(by_path) <= set(blobs),
              "attributed path unknown to the record: " + ", ".join(
                  sorted(set(by_path) - set(blobs))))
    loaded = set(loaded)
    folders = {posixpath.dirname(p) for p in loaded}
    out = {}
    for path in sorted(blobs):
        found = blobs[path]
        if found["baseline"] == found["candidate"]:
            a.require(path not in by_path, "attributed path identical to "
                      "the baseline: " + path)
            continue
        entry = by_path.get(path)
        if entry is not None:
            same = (entry["baseline_blob"], entry["candidate_blob"]) == (
                found["baseline"], found["candidate"])
            out[path] = ("attributed", entry["reason"]) if same else (
                "mismatch", "reviewed blobs %s, %s; git has %s, %s" % (
                    entry["baseline_blob"], entry["candidate_blob"],
                    found["baseline"], found["candidate"]))
        elif path in loaded:
            out[path] = ("unattributed", "loaded by a measured cell or "
                         "the initial heap")
        elif path.startswith(HARNESS_TREE):
            out[path] = ("harness", "installed from the checkout, the "
                         "same file in both trees")
        elif is_build(path) and posixpath.dirname(path) in folders:
            out[path] = ("unattributed-build", "build file of a directory "
                         "a measured cell loads from")
        else:
            out[path] = ("unloaded", "no measured cell loaded it on "
                         "either side")
    return out
