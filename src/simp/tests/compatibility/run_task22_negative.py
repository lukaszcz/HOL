#!/usr/bin/env python3
"""Execute source-isolated TASK22 policy-abort negative controls."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
BASE = "fef39229ccd854bf5936174c4f0b31010a4f0f0a"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = HERE.parents[3]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    src = repo / "src/simp/src"
    tests = repo / "src/simp/tests/simp-ext"
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "SIMP_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    manifest = {"baseline": BASE, "success": False, "runs": [],
                "inputs": {str(p.relative_to(repo)): digest(p.read_bytes())
                           for p in [src / (m + suffix)
                                     for m in ("TraverseExt", "simpExtLib")
                                     for suffix in (".sml", ".sig")] +
                           [tests / (f + ".sml") for f in
                            ("derivation", "lifetimes")] + [Path(__file__)]}}

    def execute(label, command, cwd, expected):
        p = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=900)
        log = p.stdout.decode(errors="replace")
        name = label + ".log.gz"
        (output / name).write_bytes(gzip.compress(p.stdout, mtime=0))
        receipt = {"label": label, "command": list(map(str, command)),
                   "cwd": str(cwd), "exit": p.returncode, "log": name,
                   "stdout_sha256": digest(p.stdout)}
        manifest["runs"].append(receipt)
        if p.returncode != expected:
            raise RuntimeError(label + ": wrong exit: " + log[-2000:])
        return log

    cases = [
        ("starting", "derivation", "normalize/keep_abstraction/HOL_ERR"),
        ("preparation", "derivation", "normalize/native ETA/HOL_ERR"),
        ("traversal", "lifetimes", "child/HOL_ERR: exact policy abort"),
        ("arguments", "lifetimes", "arguments/HOL_ERR: exact policy abort"),
        ("pretest", "derivation",
         "pretest/false/HOL_ERR: pretest recovers immediately"),
        ("direct", "derivation",
         "direct/native ETA/HOL_ERR: exact abort after descent")]
    try:
        for mode, fixture, marker in cases:
            with tempfile.TemporaryDirectory(prefix="simp-task22-") as tmp:
                dst = Path(tmp)
                for module in ("TraverseExt", "simpExtLib"):
                    for suffix in (".sig", ".sml"):
                        name = module + suffix
                        data = (src / name).read_bytes()
                        if mode == "starting" and suffix == ".sml":
                            data = subprocess.check_output(
                                ["git", "-C", str(repo), "show",
                                 BASE + ":src/simp/src/" + name])
                        text = data.decode()
                        old = new = None
                        if mode == "preparation" and name == "simpExtLib.sml":
                            old = "keep_abstraction=protected (#keep_abstraction policy)"
                            new = "keep_abstraction= #keep_abstraction policy"
                        if mode == "pretest" and name == "simpExtLib.sml":
                            old = ("may_reduce_arguments = "
                                   "with_child_first_callbacks callback_failure\n"
                                   "       (fn tm => opaque orelse "
                                   "arguments_reducible tm)")
                            new = ("may_reduce_arguments = fn tm => "
                                   "opaque orelse arguments_reducible tm")
                        if mode == "direct" and name == "simpExtLib.sml":
                            old = ("protect_child_first_callback failure "
                                   "(#keep_abstraction policy)")
                            new = "#keep_abstraction policy"
                        if mode == "traversal" and name == "TraverseExt.sml":
                            old = "keep_abstraction=protected keep_abstraction"
                            new = "keep_abstraction=keep_abstraction"
                        if mode == "arguments" and name == "TraverseExt.sml":
                            old = "keep_abstraction=protected (#keep_abstraction policy)"
                            new = "keep_abstraction= #keep_abstraction policy"
                        if old is not None:
                            if text.count(old) != 1:
                                raise RuntimeError("nonunique mutation: " + mode)
                            text = text.replace(old, new)
                            manifest.setdefault("mutations", {})[mode] = {
                                "file": name, "old": old, "new": new}
                        (dst / name).write_text(text)
                shutil.copyfile(tests / (fixture + ".sml"),
                                dst / (fixture + ".sml"))
                makefile = ("HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
                            "INCLUDES = " + str(src) + "\n" + fixture +
                            ".exe: " + fixture + ".uo\n"
                            "\t$(HOLMOSMLC) -o $@ $<\n")
                (dst / "Holmakefile").write_text(makefile)
                manifest.setdefault("isolated_sources", {})[mode] = {
                    p.name: digest(p.read_bytes()) for p in dst.iterdir()}
                execute(mode + "-build", [str(repo / "bin/Holmake"),
                        "--no-project", "--no-cache", "--no_prereqs", "-j1",
                        "-C", tmp, fixture + ".exe"], repo, 0)
                products = {p.name: p.read_text()
                            for p in (dst / ".hol/objs").glob("*.uo")}
                required = ["TraverseExt"]
                if fixture == "derivation":
                    required += ["simpExtLib"]
                for module in required:
                    if str(dst / module) not in products[fixture + ".uo"]:
                        raise RuntimeError("nonlocal fixture import: " + module)
                if fixture == "derivation" and str(dst / "TraverseExt") not in (
                        products["simpExtLib.uo"]):
                    raise RuntimeError("nonlocal simplifier traversal")
                manifest.setdefault("isolated_products", {})[mode] = products
                log = execute(mode + "-run", [str(dst / (fixture + ".exe"))],
                              dst, 1)
                # Fail on a semantic assertion, never a deferred static error.
                if "Static Errors" in log or "Uncaught exception" in log:
                    raise RuntimeError(mode + ": not a semantic failure")
                if not any(marker in line and "FAILED" in line
                           for line in log.splitlines()):
                    raise RuntimeError(mode + ": missing expected rejection")
                if fixture == "derivation" and "DERIVATION_CHECKS=" not in log:
                    raise RuntimeError(mode + ": derivation did not finish")
                manifest.setdefault("observations", {})[mode] = marker
        manifest["success"] = True
    finally:
        (output / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")


if __name__ == "__main__":
    main()
