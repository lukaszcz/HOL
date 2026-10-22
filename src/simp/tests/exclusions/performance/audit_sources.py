#!/usr/bin/env python3
"""Offline whole-file correspondence, not runtime or timing evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import schema


def audit(repo):
    files = {}
    for name in ("simpLib.sml", "simpLib.sig"):
        path = "src/simp/src/" + name
        baseline = schema.paired.git(
            repo, "show", schema.paired.BASE + ":" + path)
        current = (repo / path).read_bytes()
        files[path] = dict(baseline=dict(bytes=len(baseline),
            sha256=hashlib.sha256(baseline).hexdigest()),
            candidate=dict(bytes=len(current),
                sha256=hashlib.sha256(current).hexdigest()),
            byte_identical=baseline == current)
    return dict(baseline=schema.paired.BASE, files=files,
        success=all(row["byte_identical"] for row in files.values()),
        scope="Whole ordinary source/signature bytes, including literal "
              "filter_net_by_names, dproc filter, -* and history replay; "
              "does not certify runtime environment, codegen or timing parity")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parents[4])
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    result = audit(args.repo.resolve())
    with args.output.open("x") as out:
        json.dump(result, out, indent=2)
        out.write("\n")
    if not result["success"]:
        raise SystemExit("ordinary sources differ from pinned baseline")


if __name__ == "__main__":
    main()
