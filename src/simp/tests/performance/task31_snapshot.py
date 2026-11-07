#!/usr/bin/env python3
"""Run the paired runner unchanged, and record its private trees.

The identity gate of TASK31 (task31_grid.py) compares what each side
compiled. The runner keeps a hash of every private source and product, but
a product is a loader descriptor (`.uo`, `.ui`) that names the directory of
its side, so the hashes of two sides differ whatever they were built from.
This wrapper runs run_paired.py as the real program (`runpy`, the same
`__main__`, the same arguments, so that its manifest, its audits and its exit
status are the runner's) and, just before the runner deletes a private tree,
writes one record of it: for each file its size, its sha256 and its sha256
with the directory of the side replaced by `<PRIVATE>`.

The record is `private-snapshot.json` in the runner's output directory:

    {"<side>": {"root": ABSOLUTE,
                "spellings": [the spellings of the root, longest first],
                "files": {RELATIVE: [bytes, raw, normalized]},
                "texts": {RELATIVE: the file's text}}}

(`<side>` is the name of the directory, `baseline` or `candidate`). A file
above LIMIT is recorded by its raw hash alone (the normalized one is the
raw one). The text (latin-1, so that any bytes are kept) is recorded of
every file but a source (`.sml`, `.sig`) up to LIMIT: the loader
descriptors are a few hundred bytes, and with their text the offline
replay recomputes the normalized digest instead of reading it. It reads the
trees and changes nothing in them. Usage: task31_snapshot.py RUNNER-ARGS.
"""
import hashlib
import json
import os
from pathlib import Path
import runpy
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
RUNNER = HERE.parent / "compatibility" / "run_paired.py"
SNAPSHOT = "private-snapshot.json"
PLACEHOLDER = b"<PRIVATE>"
PREFIX = "simp-paired-"
# A file above this size is not text that names its directory (a loader
# descriptor is a few hundred bytes; a theory's data is large), and is
# recorded by its raw hash alone.
LIMIT = 256 * 1024
SOURCE_SUFFIXES = (".sml", ".sig")


def spellings(root):
    """The spellings of a root a file may name, longest first."""
    return sorted({str(root), os.path.realpath(root)},
                  key=lambda s: (-len(s), s))


def normalize(data, names):
    """`data` (bytes) with every spelling of the root replaced by the
    placeholder."""
    for spelling in names:
        data = data.replace(spelling.encode(), PLACEHOLDER)
    return data


def digests(root, path):
    """[bytes, raw sha256, normalized sha256] of one file of the tree
    `root`: the normalized one has every spelling of the root replaced by
    the placeholder."""
    data = path.read_bytes()
    raw = hashlib.sha256(data).hexdigest()
    if len(data) > LIMIT:
        return [len(data), raw, raw]
    return [len(data), raw, hashlib.sha256(
        normalize(data, spellings(root))).hexdigest()]


def snapshot(root):
    """The record of one private tree."""
    root = Path(root)
    files, texts = {}, {}
    for folder, _, names in os.walk(root):
        for name in names:
            path = Path(folder) / name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                files[relative] = ["link", os.readlink(path)]
            elif path.is_file():
                files[relative] = digests(root, path)
                if files[relative][0] <= LIMIT and \
                        not relative.endswith(SOURCE_SUFFIXES):
                    texts[relative] = path.read_bytes().decode("latin-1")
    return {"root": str(root), "spellings": spellings(root),
            "files": dict(sorted(files.items())),
            "texts": dict(sorted(texts.items()))}


def install(output):
    """Make every private tree the runner removes leave its record."""
    original = tempfile.TemporaryDirectory.cleanup
    found = {}

    def cleanup(self):
        root = Path(self.name)
        if root.name.startswith(PREFIX) and root.is_dir():
            for side in sorted(root.iterdir()):
                if side.is_dir():
                    found[side.name] = snapshot(side)
            (Path(output) / SNAPSHOT).write_text(
                json.dumps(found, indent=1, sort_keys=True) + "\n")
        original(self)

    tempfile.TemporaryDirectory.cleanup = cleanup


def main(argv):
    if "--output" not in argv:
        raise SystemExit("task31_snapshot.py: the runner needs --output")
    install(Path(argv[argv.index("--output") + 1]).resolve())
    sys.argv = [str(RUNNER), *argv]
    runpy.run_path(str(RUNNER), run_name="__main__")


if __name__ == "__main__":
    main(sys.argv[1:])
