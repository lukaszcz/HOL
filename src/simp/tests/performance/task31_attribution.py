"""The reviewed differences of the TASK31 candidate from the baseline.

The data is task31_attributed.json, read and validated by task31_pins.py
(which describes its shape and kinds, and projects it onto the pins of the
timing table). It is a separate file, so that adding a reviewed file
changes no seal of the counts; every record carries its seal instead.

`account` classifies every tracked file that differs between the two
commits, from the git blobs and from the files the receipts show were
loaded: a file is attributed (an entry with exactly the blobs), or decisive
(loaded and unattributed, a build tool or build sequence and unattributed, a
build file of a loaded directory and unattributed, a file of a name
Holmake reads beside its build directories (UPWARD) anywhere and
unattributed, an entry with other blobs), or not loaded (proved by the
receipts), or excluded. EXCLUDED is the reviewed list of the paths that
are no part of any build a cell measures, each with its reason; no other
path is left out.
"""
import hashlib
import posixpath

import acceptance as a
import timing_grid as tg
from task31_pins import FILE, SOURCE_SUFFIXES, load

BUILD_NAMES = ("Holmakefile", "MANIFEST")
# The files Holmake reads beside the directories it builds in
# (holpathdb.files_upward_in_hierarchy and HMProject.load): the project file
# and its local override, the holpath registration and the pre-exec script.
# They decide what a build does. A difference in a file of one of these
# names is decisive wherever it is in the repository (unless EXCLUDED), not
# only in a loaded directory or above one: Holmake looks for them in the
# ancestors of every directory it visits, and it visits more than the
# directories a cell loads from (it also follows INCLUDES, PRE_INCLUDES and
# the external directories of a project), so the loaded directories and
# their ancestors are not the whole set. No include closure is computed;
# the rule is conservative, and a file that cannot matter is attributed.
UPWARD = ("holproject.toml", "holproject.local.toml", ".holpath",
          ".hol_preexec")
# The reviewed exclusions: (path or directory, reason). A path is excluded
# only if no receipt shows it loaded. The measuring harness and the paired
# runner are installed from the checkout, the same file in both private
# trees, and are bound by the harness seals and the checkout record; neither
# is read from either commit. The documentation sources are read only by the
# help-database step of the build (`build_help`, which runs after the sources
# are built and the build is stamped): it makes the help database and the
# manuals, nothing a cell loads.
EXCLUDED = (
    ("src/simp/tests/performance/",
     "the measuring harness: installed from the checkout, the same file in "
     "both private trees"),
    ("src/simp/tests/compatibility/run_paired.py",
     "the paired runner: run from the checkout for both sides"),
    ("src/simp/tests/compatibility/paired/",
     "the paired fixtures: installed from the checkout, the same file in "
     "both private trees"),
    ("help/", "documentation sources (Docfiles): read only by the "
     "help-database step of the build, which makes nothing a cell loads"),
    ("CLAUDE.md", "instructions for assistants: documentation, outside "
     "every build"))
# The build tools, their prelude and the build sequences decide what is
# built into the shared tree and how, which the receipts do not record: a
# difference there is attributed or the grid is different.
TOOLCHAIN = ("tools/", "tools-poly/", "bin/")
DECISIVE = ("unattributed", "unattributed-build", "mismatch")


def digest(entries):
    """The seal of a table of entries."""
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


def excluded(path):
    """The reason a path is on the reviewed exclusion list, or None."""
    for found, reason in EXCLUDED:
        if path == found or (found.endswith("/") and
                             path.startswith(found)):
            return reason
    return None


def toolchain(path):
    """A file of the build tools, the prelude or the sequences (not a
    document)."""
    name = posixpath.basename(path)
    return path.startswith(TOOLCHAIN) and not (
        name.endswith(".md") or name.startswith("README"))


def account(blobs, entries, loaded):
    """{path: (class, note)} of every path of `blobs` whose two blobs
    differ. `blobs` is {path: {baseline, candidate}} (every tracked path
    that differs, and the sources), `loaded` the set of tracked paths
    that any measured cell loaded on either side (elaborated, found loaded,
    or in the initial heap). The classes:

    - attributed: an entry names exactly these blobs;
    - mismatch: an entry names other blobs;
    - unattributed: loaded, with no entry;
    - excluded: on the reviewed exclusion list (EXCLUDED) and not loaded;
    - unattributed-build: a file of the build tools or the sequences
      (TOOLCHAIN), a file of an UPWARD name anywhere, or a build file in a
      directory that something loaded came from, with no entry;
    - unloaded: no loaded file of either side is this one, and it is no
      build file."""
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
        elif excluded(path) is not None:
            out[path] = ("excluded", excluded(path))
        elif toolchain(path):
            out[path] = ("unattributed-build", "a build tool or sequence: "
                         "the receipts record no file of it, so they "
                         "cannot show it unused")
        elif posixpath.basename(path) in UPWARD:
            out[path] = ("unattributed-build", "a file Holmake reads "
                         "beside the directories it builds in, which "
                         "include more than the ones a cell loads from")
        elif is_build(path) and posixpath.dirname(path) in folders:
            out[path] = ("unattributed-build", "build file of a directory "
                         "a measured cell loads from")
        else:
            out[path] = ("unloaded", "no measured cell loaded it on "
                         "either side")
    return out
