#!/usr/bin/env python3
"""Fail-closed isolated-source comparison; NOT independent repository builds."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile

BASE = "cccaa27d7099cbadc886983020cbe745db7793f3"
REVIEWED = "cf1f863b4e5a9712ce1b179f18274eb3451f3954"
HERE = Path(__file__).resolve().parent
PREFIX = "@@PAIR\t"


class InvalidRun(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidRun(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fingerprint(path):
    data = path.read_bytes()
    return {"sha256": digest(data), "bytes": len(data)}


def physical(path):
    """HOL's HFS maps generated logical filenames into .hol/objs."""
    path = Path(path)
    if not path.exists():
        path = path.parent / ".hol/objs" / path.name
    return path.resolve(strict=True)


def behavior_events(flavor):
    counts = ("1", "1", "1") if flavor == "baseline" else ("0", "1", "2")
    outcome = "goals=1" if flavor == "baseline" else "PrinterFailure"
    return [
        ["observation", "construction.printers", counts[0]],
        ["check", "requirement failure", "pass"],
        ["observation", "first.printers", counts[1]],
        ["check", "requirement failure", "pass"],
        ["observation", "second.printers", counts[2]],
        ["observation", "saved.outcome", outcome],
        ["check", "ordinary simplification", "pass"],
    ]


def parse_events(text):
    require(not text or text.endswith("\n"),
            "truncated output (no final newline)")
    events = []
    for line in text.splitlines():
        if line.startswith(PREFIX):
            fields = line[len(PREFIX):].split("\t")
            require(len(fields) >= 2 and fields[1], "missing protocol event kind")
            require(fields[0] == str(len(events)), "missing/unordered protocol event")
            events.append(fields[1:])
        else:
            require("@@PAIR" not in line, "malformed protocol line")
    return events


def validate(receipt, *, selection, fixture, control, private, repo,
             private_names, flavor, signature, source_hashes):
    """Strict ordered protocol + exit + source/path audit. Never infer success
    from .uo creation, expected exit alone, or a success substring in a log.
    The only allowed error is the explicitly requested old-datatype rejection.
    """
    require(not receipt["timed_out"], "process timed out")
    events = parse_events(receipt["stdout"])
    header = [
        ["begin", selection, fixture, control],
        ["cwd", str(private)],
        ["holdir", str(repo), str(repo)],
    ]
    require(events[:3] == header, "launcher not executed or wrong header")
    require(len(events) > 6, "incomplete protocol")
    require(events[3][0] == "preloaded" and len(events[3]) == 2,
            "missing preloaded-module inventory")
    preloaded = events[3][1].split(",")
    require(not (set(preloaded) & private_names),
            "simplifier already present in shared heap")
    searches = [["search", str(private)], ["search", str(repo / "sigobj")]]
    start = 4
    heapfiles = []
    while start < len(events) and events[start][0] == "heapfile":
        require(len(events[start]) == 2, "invalid heap source inventory")
        heapfiles.append(events[start][1])
        start += 1
    require(heapfiles and len(heapfiles) == len(set(heapfiles)),
            "missing/duplicate initial heap source inventory")
    require(events[start:start + 2] == searches, "wrong ordered search paths")
    start += 2
    expected = behavior_events(flavor) if fixture == "selftest" else [
        ["check", "legacy signature", "pass"]]
    red = fixture == "signature" and signature == "reject"
    if red:
        expected = [["exception", "Fail", r'Fail \"Static Errors\"']]
    checks = sum(e[0] == "check" for e in expected)
    require(events[-1] == ["end", "error" if red else "pass", str(checks)],
            "missing or wrong completion/test count")
    require(receipt["exit"] == (1 if red else 0), "failed process/wrong exit")
    observations, used, completed, loaded = [], [], [], []
    pending = None
    phase = "use"
    for event in events[start:-1]:
        require(event, "empty event")
        kind = event[0]
        if kind == "use":
            require(phase == "use" and len(event) == 2 and pending is None,
                    "unordered source-use event")
            pending = event[1]
            used.append(pending)
        elif kind == "used":
            require(phase == "use" and len(event) == 2 and pending == event[1],
                    "unmatched source-use completion")
            completed.append(pending)
            pending = None
        elif kind in ("observation", "check", "exception"):
            require(phase == "use", "observation after loaded inventory")
            observations.append(event)
        elif kind == "loaded":
            require(len(event) == 2, "invalid loaded-source event")
            phase = "loaded"
            loaded.append(event[1])
        else:
            raise InvalidRun("unknown protocol event: " + kind)
    require(bool(loaded), "missing loaded-source inventory")
    require(len(loaded) == len(set(loaded)), "duplicate loaded-source inventory")
    require(set(loaded) == set(heapfiles + completed),
            "incomplete or untraced loaded-source inventory")
    if red:
        require(pending == str(private / "SignatureCheck.sml"),
                "error was not in the signature fixture")
        for constructor in ("CONFIG_REDUCER", "CONTEXT_REDUCER"):
            require(re.search(r"constructor " + constructor +
                              r" was present in the structure but not in the "
                              r"signature", receipt["stdout"]),
                    "missing exact datatype rejection: " + constructor)
    else:
        require(pending is None, "unfinished source elaboration")
    # Both attempted and completed paths matter: expected-red elaboration
    # never enters fileDirMap for the failing source. Audit either inventory.
    paths = {}
    for raw in dict.fromkeys(used + loaded):
        p = physical(raw)
        name = p.stem
        if name in private_names or p.is_relative_to(private):
            require(p.is_relative_to(private), "wrong loaded simplifier path: " + raw)
        else:
            require(p.is_relative_to(repo), "source outside shared repository: " + raw)
            require(not p.is_relative_to(repo / "src/simp"),
                    "shared simplifier leaked into private run: " + raw)
        info = fingerprint(p)
        if str(p) in source_hashes:
            require(info == source_hashes[str(p)], "source changed during run: " + raw)
        related = {}
        for suffix in (".uo", ".ui", ".dat"):
            try:
                product = physical(Path(raw).with_suffix(suffix))
            except FileNotFoundError:
                continue
            related[str(product)] = fingerprint(product)
        paths[raw] = {"physical": str(p), **info, "related_products": related,
                      "origin": "elaborated" if raw in used else "initial-map"}
    require(observations == expected, "incomplete or wrong ordered observations")
    target = "SignatureCheck.sml" if fixture == "signature" else "selftest.sml"
    require(str(private / target) in used, "requested fixture never elaborated")
    for name in ("Traverse",) if fixture == "signature" else ("Traverse", "simpLib"):
        require(str(private / (name + ".sml")) in used,
                "selected implementation not elaborated: " + name)
    outcome = "pass"
    if red or (fixture == "selftest" and flavor == "reviewed"):
        outcome = "expected-candidate-red"
    return {"observations": observations, "expected_test_count": checks,
            "outcome": outcome,
            "events": events, "paths": paths}


def execute(command, cwd, env, timeout):
    p = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         start_new_session=True)
    expired = False
    try:
        text, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        # Shell launchers do not exec HOL. Kill/reap the whole group before
        # removing private inputs, or a timed-out HOL child could leak out.
        expired = True
        os.killpg(p.pid, signal.SIGKILL)
        text, _ = p.communicate()
    except BaseException:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        raise
    code = p.returncode
    return {"command": list(map(str, command)), "cwd": str(cwd),
            "exit": code, "timed_out": expired, "stdout": text,
            "stdout_sha256": digest(text.encode()), "stdout_bytes": len(text.encode())}


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def extract(repo, rev, dst):
    inventory = []
    for path in git(repo, "ls-tree", "-r", "--name-only", rev,
                    "src/simp/src").decode().splitlines():
        p = Path(path)
        if p.suffix not in (".sml", ".sig") or p.name == "selftest.sml":
            continue
        if p.parent.name == "mosml":
            continue
        require(p.parent.as_posix() in ("src/simp/src", "src/simp/src/poly"),
                "unexpected source layout: " + path)
        data = git(repo, "show", rev + ":" + path)
        out = dst / p.name
        require(not out.exists(), "flattened source collision: " + path)
        out.write_bytes(data)
        inventory.append({"git_path": path, "private_path": str(out),
                          "git_blob": git(repo, "rev-parse", rev + ":" + path)
                          .decode().strip(), **fingerprint(out)})
    return inventory


def install_fixtures(dst):
    for p in (HERE / "paired").iterdir():
        if p.suffix == ".sml" or p.name == "Holmakefile":
            shutil.copyfile(p, dst / p.name)
    # Preserve the complete immutable signature and ascription. Only replace
    # the review probe's process exit with a counted testutils assertion, so
    # the launcher can emit its mandatory completion footer after elaboration.
    abi = (HERE.parent / "performance/review-20261021/abicheck.sml").read_text()
    ending = "val _ = OS.Process.exit OS.Process.success\n"
    require(abi.endswith(ending), "unexpected immutable signature fixture")
    (dst / "SignatureCheck.sml").write_text(
        abi[:-len(ending)] + 'val _ = Paired.check "legacy signature" true\n')


def verify_control(receipt, control, private):
    """A control must hit its intended guard, not just fail for any reason."""
    reasons = {
        "missing": "incomplete or wrong ordered observations",
        "truncated": "missing or wrong completion/test count",
        "failed": "failed process/wrong exit",
        "wrong-path": "wrong loaded simplifier path:",
        "deferred": "missing or wrong completion/test count",
        "unexecuted": "launcher not executed or wrong header",
    }
    require(receipt.get("rejection", "").startswith(reasons[control]),
            "negative control missed intended guard: " + control)
    if control == "deferred":
        events = receipt["events"]
        path = str(private / "Deferred.sml")
        require(receipt["exit"] == 1 and ["use", path] in events and
                ["used", path] not in events and
                ["exception", "Fail", r'Fail \"Static Errors\"'] in events and
                "deferred_elaboration_control" in receipt["stdout"] and
                "Can't unify int" in receipt["stdout"],
                "deferred elaboration error was not executed/detected")


def compact(receipt, output, label):
    text = receipt.pop("stdout")
    # Raw logs are useful on failure, but repeated loader traces are retained
    # once as structured events/hashed path inventories, not duplicated logs.
    diagnostics = [line for line in text.splitlines()
                   if not line.startswith(PREFIX)]
    receipt["diagnostics"] = diagnostics
    data = (json.dumps(receipt, indent=2) + "\n").encode()
    (output / (label + ".json.gz")).write_bytes(gzip.compress(data, mtime=0))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parents[3])
    p.add_argument("--baseline", default=BASE)
    p.add_argument("--candidate", default=REVIEWED)
    p.add_argument("--candidate-signature", choices=("reject", "pass"), default="reject")
    p.add_argument("--candidate-behavior", choices=("reviewed", "baseline"), default="reviewed")
    p.add_argument("--negative-controls", action="store_true")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=300)
    args = p.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    # Never overwrite historical/user evidence, even on a failed invocation.
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    manifest = {"schema_version": 1, "evidence_id": "TASK_02-paired-v1",
                "scope": "mixed-source isolation, not independent repository builds",
                "command": ["python3", *os.sys.argv], "repo": str(repo),
                "head": git(repo, "rev-parse", "HEAD").decode().strip(),
                "dirty": git(repo, "status", "--porcelain=v1").decode().splitlines(),
                "runtime_options": ["--gcthreads=1", "run", "--holstate=" +
                                    str(repo / "bin/hol.state0")],
                "environment": {k: v for k, v in env.items()
                                if k in ("HOLDIR", "TERM", "LC_ALL", "TZ", "PATH")},
                "tools": {}, "inputs": {}, "selections": {}, "runs": [],
                "success": False}
    try:
        for name in ("bin/hol", "bin/hol.state0", "bin/hol.state.min",
                     "bin/Holmake", "holproject.toml"):
            manifest["tools"][name] = fingerprint(repo / name)
        poly = shutil.which("poly", path=env["PATH"])
        require(poly is not None, "poly not found")
        manifest["tools"][poly] = fingerprint(Path(poly).resolve())
        manifest["poly_version"] = execute([poly, "--version"], repo, env,
                                            args.timeout)
        require(manifest["poly_version"]["exit"] == 0, "poly --version failed")
        inputs = [HERE / "run_paired.py", HERE / "test_runner.py",
                  HERE / "Holmakefile", HERE / "SCHEMA.md",
                  HERE / "paired/Holmakefile",
                  *sorted((HERE / "paired").glob("*.sml")),
                  HERE / "inputs/develop/Traverse.sig",
                  HERE.parent / "performance/review-20261021/abicheck.sml"]
        for path in inputs:
            manifest["inputs"][str(path.relative_to(repo))] = fingerprint(path)
        sources = {}
        with tempfile.TemporaryDirectory(prefix="simp-paired-") as tmp:
            root = Path(tmp)
            for selection, ref in (("baseline", args.baseline), ("candidate", args.candidate)):
                dst = root / selection
                dst.mkdir()
                rev = git(repo, "rev-parse", ref + "^{commit}").decode().strip()
                inventory = extract(repo, rev, dst)
                install_fixtures(dst)
                manifest["selections"][selection] = {
                    "requested_ref": ref, "revision": rev, "private": str(dst),
                    "sources": inventory,
                    "fixture_products": {f.name: fingerprint(f) for f in dst.iterdir()
                                         if f.name not in {Path(s["git_path"]).name
                                                           for s in inventory}}}
                for f in dst.iterdir():
                    if f.is_file():
                        sources[str(f)] = fingerprint(f)
            names = {Path(s["git_path"]).stem for v in manifest["selections"].values()
                     for s in v["sources"]}
            # Signature files are copied, never weakened to make candidate pass.
            original = (HERE / "inputs/develop/Traverse.sig").read_bytes()
            from_git = git(repo, "show", BASE + ":src/simp/src/Traverse.sig")
            require(original == from_git, "immutable old signature changed")
            abi = (HERE.parent / "performance/review-20261021/abicheck.sml").read_bytes()
            require(original.replace(b"signature Traverse =", b"signature LegacyTraverse =")
                    in abi, "original complete signature absent from fixture")
            for selection in ("baseline", "candidate"):
                dst = root / selection
                cmd = [str(repo / "bin/Holmake"), "--no-project", "--no-cache",
                       "--no_prereqs", "--holstate=" + str(repo / "bin/hol.state0"),
                       "-C", str(dst), "-j1", "paired.exe"]
                build = execute(cmd, root, env, args.timeout)
                manifest["selections"][selection]["build_exit"] = build["exit"]
                compact(dict(build), output, selection + "-build")
                require(build["exit"] == 0 and not build["timed_out"],
                        selection + " build failed")
                launcher = dst / "paired.exe"
                text = launcher.read_text()
                require(str(repo / "bin/hol") + " --gcthreads=1 run " in text and
                        "--holstate=" + str(repo / "bin/hol.state0") in text,
                        "unexpected launcher runtime/options")
                manifest["selections"][selection]["launcher"] = text
                products = {}
                for pattern in ("*.exe", ".hol/objs/*", ".hol/make-deps/*"):
                    for f in sorted(dst.glob(pattern)):
                        if f.is_file():
                            products[str(f.relative_to(dst))] = fingerprint(f)
                            sources[str(f.resolve())] = fingerprint(f)
                manifest["selections"][selection]["products"] = products
            for selection in ("baseline", "candidate"):
                dst = root / selection
                flavor = "baseline" if selection == "baseline" else args.candidate_behavior
                signature = "pass" if selection == "baseline" else args.candidate_signature
                cases = [("selftest", "none"), ("signature", "none")]
                if args.negative_controls:
                    cases += [("selftest", c) for c in
                              ("missing", "truncated", "failed", "wrong-path",
                               "deferred", "unexecuted")]
                for fixture, control in cases:
                    target = "SignatureCheck" if fixture == "signature" else "selftest"
                    if control == "wrong-path":
                        other = "candidate" if selection == "baseline" else "baseline"
                        target = str(root / other / "selftest")
                    if control == "deferred":
                        target = "Deferred"
                    runenv = dict(env, PAIR_SELECTION=selection, PAIR_FIXTURE=fixture,
                                  PAIR_CONTROL=control, PAIR_PRIVATE=str(dst), PAIR_TARGET=target)
                    command = [str(dst / "paired.exe")]
                    if control == "unexecuted":
                        command = [shutil.which("true", path=env["PATH"])]
                    receipt = execute(command, dst, runenv, args.timeout)
                    receipt["environment"] = {k: v for k, v in runenv.items()
                                              if k.startswith("PAIR_")}
                    receipt["fixture"] = fixture
                    receipt["control"] = control
                    receipt["selection"] = selection
                    try:
                        result = validate(receipt, selection=selection, fixture=fixture,
                                          control=control, private=dst, repo=repo,
                                          private_names=names, flavor=flavor,
                                          signature=signature, source_hashes=sources)
                        receipt["result"] = result
                        receipt["accepted"] = True
                    except (InvalidRun, OSError) as e:
                        receipt["accepted"] = False
                        receipt["rejection"] = str(e)
                        try:
                            receipt["events"] = parse_events(receipt["stdout"])
                        except InvalidRun:
                            receipt["malformed_stdout"] = receipt["stdout"]
                    if control != "none":
                        try:
                            verify_control(receipt, control, dst)
                        except InvalidRun as e:
                            receipt["control_failure"] = str(e)
                    label = selection + "-" + fixture + "-" + control
                    manifest["runs"].append({"receipt": label + ".json.gz",
                                             "accepted": receipt["accepted"],
                                             "expected_acceptance": control == "none",
                                             "exit": receipt["exit"]})
                    compact(receipt, output, label)
                    require("control_failure" not in receipt,
                            receipt.get("control_failure", ""))
                    require(receipt["accepted"] == (control == "none"),
                            label + ": " + receipt.get("rejection", "negative control accepted"))
            # Shared dependencies are fingerprinted in accepted run inventories;
            # refuse source/tool mutations across this entire comparison.
            for run in manifest["runs"]:
                if run["accepted"]:
                    record = json.loads(gzip.decompress(
                        (output / run["receipt"]).read_bytes()))
                    for info in record["result"]["paths"].values():
                        require(fingerprint(Path(info["physical"])) ==
                                {k: info[k] for k in ("sha256", "bytes")},
                                "loaded source changed during pair")
                        for path, expected in info["related_products"].items():
                            require(fingerprint(Path(path)) == expected,
                                    "loaded dependency product changed during pair")
            for name, info in manifest["tools"].items():
                require(fingerprint(repo / name) == info, "runtime/tool changed during pair")
        manifest["success"] = True
    except Exception as e:
        manifest["failure"] = str(e)
    finally:
        (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")
    if not manifest["success"]:
        raise SystemExit(manifest.get("failure", "paired validation failed"))


if __name__ == "__main__":
    main()
