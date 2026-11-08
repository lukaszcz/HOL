"""Refuse an unset, relative or in-repository output directory.

Usage: require_output.py DIR [NAME].  Every runner writes receipts that
must never land in the checkout; the Holmakefiles run this before any
runner.  NAME is the variable shown in messages (default PAIRED_OUTPUT).
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]


def main(argv):
    if len(argv) not in (2, 3):
        sys.exit("usage: require_output.py DIR [NAME]")
    name = argv[2] if len(argv) == 3 else "PAIRED_OUTPUT"
    if not argv[1]:
        sys.exit("%s must name a new directory outside the repository "
                 "(pass %s=/absolute/path)" % (name, name))
    out = Path(argv[1])
    if not out.is_absolute():
        sys.exit(name + " must be an absolute path: " + argv[1])
    out = out.resolve()
    if out == ROOT or ROOT in out.parents:
        sys.exit(name + " must be outside the repository: " + argv[1])


if __name__ == "__main__":
    main(sys.argv)
