#!/usr/bin/env python3
"""Fresh testutils launchers with unique source-tied receipts."""
import argparse
import datetime
import gzip
import hashlib
import itertools
import json
import os
import re
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import uuid

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCES = ("Holmakefile", "selftest.sml", "ordinary.ML", "runtime.ML",
           "Documentation.sml", "run.py")


def seal(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def validate_output(text, returncode, kind, owner):
    """Reject truncated observations, wrong counts and foreign core inputs."""
    lines = text.splitlines()
    expected = {("attribute", "before"): 172,
                ("attribute", "after"): 168,
                ("exporter", "before"): 176,
                ("exporter", "after"): 171}[kind, owner]
    clean = re.sub(r"\x1b\[[0-9;]*[mCG]", "", text)
    checks = clean.count("OK\n")
    if (returncode != 0 or not text.endswith("\n") or
            lines.count("OBS result=pass") != 1 or checks != expected or
            "FAILED!" in text):
        raise ValueError("incomplete API audit output")
    # Meta.loadPlan actually uses these files. Requested names alone are not
    # evidence; reject sigobj/foreign copies and bind the receipt to live bytes.
    used = {line.split("=", 1)[1] for line in lines
            if line.startswith("OBS used.path=")}
    for module in ("simpLib", "congLib", "Traverse", "Cond_rewr", "Trace",
                   "SimpTracking", "simpExtLib", "TraverseExt",
                   "Cond_rewrExt", "congExtLib"):
        for suffix in (".sig", ".sml"):
            path = ROOT / "src/simp/src" / (module + suffix)
            if str(path) not in used or not path.is_file():
                raise ValueError("missing actual native input: " + str(path))
            if any(Path(p).name == path.name and p != str(path) for p in used):
                raise ValueError("foreign native input: " + path.name)
    return checks


def resolve_observed(path):
    """Theory maps keep canonical paths; Holmake stores outputs in .hol."""
    target = Path(path)
    if target.is_file():
        return target
    product = target.parent / ".hol/objs" / target.name
    if target.name.endswith(("Theory.sml", "Theory.sig")) and product.is_file():
        return product
    raise ValueError("missing observed input: " + path)


def inside(path, root):
    """True if path or an existing ancestor of it is the same as root.

    The comparison is by identity (device and inode), so symlinks and
    bind-mounted aliases of the checkout are caught too.  The same check
    exists in compatibility/tools/require_output.py; it is kept separate
    so that the audit receipt seals all of its inputs.
    """
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        help="absolute directory receiving one unique receipt subdirectory "
             "per run (default: a new private directory made with mkdtemp "
             "in the temporary directory); it must be outside the repository")
    args = parser.parse_args()
    if args.output is None:
        args.output = Path(tempfile.mkdtemp(prefix="api-audit-receipts-"))
    if not args.output.is_absolute():
        parser.error("--output must be an absolute path: " + str(args.output))
    given = args.output
    args.output = args.output.resolve()
    if inside(args.output, ROOT) or inside(given, ROOT):
        parser.error("--output must be outside the repository: " +
                     str(args.output))
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime(
        "%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
    evidence = args.output / stamp
    evidence.mkdir(parents=True, exist_ok=False)
    receipt = {
        "task": 27,
        "command": sys.argv,
        "cwd": str(HERE),
        "reproduce": "Holmake -C src/simp/tests/api-audit check",
        "head": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "sources": {name: seal(HERE / name) for name in SOURCES},
        "products": {str(path): seal(path) for path in (
            HERE / 'selftest.exe', ROOT / 'bin/hol.state0',
            ROOT / 'bin/Holmake')},
        "runtime": subprocess.check_output(
            [shutil.which('poly'), '--version'], text=True).strip(),
        "cases": [],
    }
    actual_paths = set()
    for order, kind, owner in itertools.product(
            ("simp-first", "cong-first"), ("attribute", "exporter"),
            ("before", "after")):
        env = dict(os.environ, API_AUDIT_SRC=str(ROOT / "src/simp/src"),
                   API_AUDIT_ORDER=order, API_AUDIT_KIND=kind,
                   API_AUDIT_OWNER=owner)
        command = [str(HERE / "selftest.exe")]
        proc = subprocess.run(command, cwd=HERE, env=env,
                              stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
        name = f"{order}-{kind}-{owner}.log.gz"
        (evidence / name).write_bytes(gzip.compress(proc.stdout, mtime=0))
        text = proc.stdout.decode("utf-8", errors="replace")
        observations = [line for line in text.splitlines()
                        if line.startswith("OBS ")]
        paths = [line.split("=", 1)[1] for line in observations
                 if ".path=" in line and not line.startswith(
                     "OBS requested.path=")]
        actual_paths.update(paths)
        error = None
        try:
            checks = validate_output(text, proc.returncode, kind, owner)
        except ValueError as failure:
            error = str(failure)
            checks = 0
        passed = error is None
        receipt["cases"].append({
            "order": order, "foreign_kind": kind,
            "foreign_owner": owner, "command": command,
            "environment": {key: env[key] for key in (
                "API_AUDIT_SRC", "API_AUDIT_ORDER", "API_AUDIT_KIND",
                "API_AUDIT_OWNER")},
            "returncode": proc.returncode, "pass": passed,
            "log": name, "log_seal": seal(evidence / name),
            "checks": checks, "validation_error": error,
            "observations": len(observations),
        })
        print(f"{order}/{kind}/{owner}: "
              f"{'PASS' if passed else 'FAIL'}", flush=True)
        if not passed:
            print(text[-16000:], flush=True)
    actual_files = {
        path: {"resolved": str(resolve_observed(path)),
               **seal(resolve_observed(path))}
        for path in sorted(actual_paths)
    }
    files_path = evidence / "actual-files.json.gz"
    files_path.write_bytes(gzip.compress(
        (json.dumps(actual_files, indent=2, sort_keys=True) + "\n").encode(),
        mtime=0))
    receipt["actual_files"] = {
        "file": files_path.name, "count": len(actual_files),
        "seal": seal(files_path),
    }
    receipt["pass"] = all(case["pass"] for case in receipt["cases"])
    (evidence / "receipt.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("Receipt: " + str(evidence))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
