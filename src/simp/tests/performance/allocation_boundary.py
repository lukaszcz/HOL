"""Boundary of the isolated-source attribution of the TASK29B matrix.

The matrix measures src/simp/src of the baseline against src/simp/src of the
candidate. Everything else a process loads comes from the one toolchain,
built at the candidate commit and shared by both sides: the HOL heap
(bin/hol.state0, deposited by HEAP_DIRECTORY), the libraries sigobj gives
the fixture and the fixtures. A difference between the two commits outside
src/simp/src therefore changes the measured processes of both sides alike,
and the comparison cannot see it. This module makes the boundary explicit
and fails closed: every path that differs between baseline and candidate
must be covered by the reviewed manifest (allocation_boundary.json), or the
run is refused before any cell.

Two kinds of manifest entry, and no others:

  prefix  a directory that nothing the subject loads is built from. A prefix
          may not contain, or lie inside, any directory the toolchain
          sequence builds up to and including the subject directory
          (SUBJECT_DIRECTORY: whatever src/simp/src loads, it loads from
          directories built before it, so the bound is structural), nor
          tools/, tools-poly/ or bin/; this is computed from the
          candidate's sequence files, never trusted from the manifest. The
          matrix driver checks the other half per process: no shared file a
          process loads lies under a prefix.
  file    an exact path with the git blob it has in the candidate. Heap
          files and anything not under a prefix are listed this way, so a
          change of the file demands a new review.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

import allocation_schema as sc

SCHEMA = "task29b-boundary-v2"
# The measured subject, built from isolated sources. The walk of directories
# the subject can load stops here, as a constant and not as a manifest value.
SUBJECT_DIRECTORY = "src/simp/src"
SUBJECT = SUBJECT_DIRECTORY + "/"
# The directory whose Holmakefile deposits bin/hol.state0; it must be built
# at or before the subject.
HEAP_DIRECTORY = "src/proofman"
FIXED_ROOTS = ("tools/", "tools-poly/", "bin/")  # compile hol and Holmake
KERNELS = ("src/0/", "src/experimental-kernel/")  # for **KERNEL**
KEYS = {"schema", "prefixes", "files"}
BLOB = re.compile(r"[0-9a-f]{40}")


def entry_list(data, key, fields):
    sc.require(isinstance(data.get(key), list), "boundary: bad " + key)
    for item in data[key]:
        sc.require(isinstance(item, dict) and set(item) == fields,
                   "boundary: malformed %s entry" % key)
        sc.require(all(isinstance(item[f], str) and item[f] for f in fields),
                   "boundary: empty field in " + key)
        path = item["path"]
        sc.require("\\" not in path and not path.startswith("/") and
                   ".." not in path.split("/") and "" not in path.rstrip(
                       "/").split("/"), "boundary: bad path " + path)
    paths = [item["path"] for item in data[key]]
    sc.require(len(set(paths)) == len(paths), "boundary: duplicate " + key)
    return data[key]


def load_manifest(path):
    """The reviewed manifest, validated for shape only."""
    data = json.loads(Path(path).read_text())
    sc.require(isinstance(data, dict) and set(data) == KEYS and
               data["schema"] == SCHEMA, "boundary: wrong manifest shape")
    for item in entry_list(data, "prefixes", {"path", "reason"}):
        sc.require(item["path"].endswith("/"),
                   "boundary: prefix must end with /: " + item["path"])
    for item in entry_list(data, "files", {"path", "blob", "reason"}):
        sc.require(not item["path"].endswith("/") and
                   BLOB.fullmatch(item["blob"]),
                   "boundary: bad file entry " + item["path"])
    return data


def read_blob(repo, rev, path):
    """Text of rev:path, or None when the path does not exist there."""
    done = subprocess.run(["git", "-C", str(repo), "show",
                           "%s:%s" % (rev, path)], stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE)
    return done.stdout.decode() if done.returncode == 0 else None


def sequence_entries(repo, rev, path, seen=()):
    """Directories a build sequence file names, in order, with the number
    of `!` marks (selftest levels) each carries. Includes are followed as
    the build does: relative to tools/."""
    text = read_blob(repo, rev, path)
    sc.require(text is not None, "boundary: no sequence file " + path)
    entries = []
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if raw.strip().startswith("#include "):
            name = "tools/" + raw.strip().split(None, 1)[1].strip()
            sc.require(name not in seen and name != path,
                       "boundary: recursive include " + name)
            entries += sequence_entries(repo, rev, name, seen + (path,))
            continue
        if not line:
            continue
        for opening, closing in (("[", "]"), ("(", ")")):
            if line.startswith(opening):
                sc.require(closing in line, "boundary: bad sequence entry")
                line = line.split(closing, 1)[1]
        marks = len(line) - len(line.lstrip("!"))
        entries.append((line[marks:].strip(), marks))
    return entries


def barred_directories(repo, rev, sequence):
    """Directories built before the subject, with their sub-trees
    (slash-terminated): every non-selftest entry of the sequence up to and
    including SUBJECT_DIRECTORY, which is where the walk stops. The
    sequence is built without -t, so entries marked `!` are not built and
    cannot contribute. The heap directory must be among them: bin/hol.state0
    is deposited at or before the subject."""
    found, out = False, []
    for name, marks in sequence_entries(repo, rev, sequence):
        if marks:
            continue
        out += list(KERNELS) if name == "**KERNEL**" else [name + "/"]
        if name == SUBJECT_DIRECTORY:
            found = True
            break
    sc.require(found, "boundary: the sequence never builds the subject "
               "directory " + SUBJECT_DIRECTORY)
    sc.require(HEAP_DIRECTORY + "/" in out, "boundary: the heap directory "
               "%s is not built at or before %s" % (HEAP_DIRECTORY,
                                                    SUBJECT_DIRECTORY))
    makefile = read_blob(repo, rev, HEAP_DIRECTORY + "/Holmakefile")
    sc.require(makefile is not None and "hol.state0" in makefile,
               "boundary: the heap directory does not deposit hol.state0")
    return out


def overlaps(a, b):
    return a.startswith(b) or b.startswith(a)


def check_manifest(repo, rev, manifest, sequence):
    """Prefixes must not touch anything built before the subject."""
    built = barred_directories(repo, rev, sequence)
    barred = built + list(FIXED_ROOTS)  # built ends with the subject
    for item in manifest["prefixes"]:
        for root in barred:
            sc.require(not overlaps(item["path"], root),
                       "boundary: prefix %s overlaps %s, which is built "
                       "before the subject" % (item["path"], root))
    return built


def changed_paths(repo, baseline, candidate):
    """Every path that differs, deletions and renames as separate paths."""
    done = subprocess.run(
        ["git", "-C", str(repo), "diff", "--name-only", "--no-renames", "-z",
         baseline, candidate], stdout=subprocess.PIPE,
        stderr=subprocess.PIPE)
    sc.require(done.returncode == 0,
               "boundary: git diff failed: " + done.stderr.decode())
    return sorted(p.decode() for p in done.stdout.split(b"\0") if p)


def candidate_blobs(repo, candidate, paths):
    """git blob of each path in the candidate (absent when deleted)."""
    if not paths:
        return {}
    done = subprocess.run(
        ["git", "-C", str(repo), "ls-tree", "-z", candidate, "--", *paths],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    sc.require(done.returncode == 0,
               "boundary: git ls-tree failed: " + done.stderr.decode())
    blobs = {}
    for row in done.stdout.split(b"\0"):
        if row:
            meta, name = row.split(b"\t", 1)
            blobs[name.decode()] = meta.split()[2].decode()
    return blobs


def resolve(repo, baseline, candidate, sequence, manifest_path):
    """The resolved boundary of one comparison, or a rejection.

    Covered: paths below src/simp/src (the subject), paths below a prefix
    entry, and exact paths whose candidate blob is the listed one. Anything
    else is an unreviewed difference. `subject_changed` counts the changed
    files in the subject directory, among them files no matrix process
    loads (Holmakefile, MANIFEST, notes), not only measured sources."""
    manifest = load_manifest(manifest_path)
    check_manifest(repo, candidate, manifest, sequence)
    prefixes = {i["path"]: i["reason"] for i in manifest["prefixes"]}
    files = {i["path"]: i for i in manifest["files"]}
    paths = changed_paths(repo, baseline, candidate)
    blobs = candidate_blobs(repo, candidate, [
        p for p in paths if p in files])
    counts = dict.fromkeys(prefixes, 0)
    subject_changed, listed, unknown = 0, [], []
    for path in paths:
        covering = [p for p in prefixes if path.startswith(p)]
        if path.startswith(SUBJECT):
            subject_changed += 1
        elif path in files:
            if blobs.get(path) == files[path]["blob"]:
                listed.append(dict(path=path, blob=files[path]["blob"]))
            else:
                unknown.append("%s (changed blob: %s)" % (
                    path, blobs.get(path, "deleted")))
        elif covering:
            counts[max(covering, key=len)] += 1
        else:
            unknown.append(path)
    sc.require(not unknown,
               "boundary: differences outside src/simp/src that the "
               "reviewed manifest does not cover: " + ", ".join(unknown[:8])
               + (" ..." if len(unknown) > 8 else ""))
    digest = hashlib.sha256("\0".join(paths).encode()).hexdigest()
    return dict(
        schema=SCHEMA, baseline=baseline, candidate=candidate,
        sequence=sequence, subject_directory=SUBJECT_DIRECTORY,
        heap_directory=HEAP_DIRECTORY,
        manifest=hashlib.sha256(Path(manifest_path).read_bytes()
                                ).hexdigest(),
        changed=len(paths), changed_sha256=digest,
        subject_changed=subject_changed,
        prefixes={p: n for p, n in counts.items() if n},
        manifest_prefixes=sorted(prefixes), files=listed)
