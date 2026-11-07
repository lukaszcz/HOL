"""Refuse an unset, relative or in-repository output directory.

Usage: require_output.py DIR [NAME].  Every runner writes receipts that
must never land in the checkout; the Holmakefiles run this before any
runner.  NAME is the variable shown in messages (default PAIRED_OUTPUT).
DIR is compared with the checkout by identity (device and inode of each
existing ancestor), so symlinks and bind-mounted aliases of the checkout
are caught too.  It need not exist yet: the runners create it and refuse
an existing one.
"""
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]


def inside(path, root):
    """True if path or an existing ancestor of it is the same as root."""
    p = Path(os.path.abspath(path))
    while True:
        try:
            if os.path.samefile(p, root):
                return True
        except OSError:
            pass
        if p.parent == p:
            return False
        p = p.parent


def main(argv):
    if len(argv) not in (2, 3):
        sys.exit("usage: require_output.py DIR [NAME]")
    name = argv[2] if len(argv) == 3 else "PAIRED_OUTPUT"
    if not argv[1]:
        sys.exit("%s must name a directory outside the repository "
                 "(pass %s=/absolute/path)" % (name, name))
    out = Path(argv[1])
    if not out.is_absolute():
        sys.exit(name + " must be an absolute path: " + argv[1])
    if inside(out.resolve(), ROOT) or inside(out, ROOT):
        sys.exit(name + " must be outside the repository: " + argv[1])


if __name__ == "__main__":
    main(sys.argv)
