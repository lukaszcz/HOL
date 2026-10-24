#!/usr/bin/env python3
"""Fresh TASK29 caller/compiler diagnostics, deliberately NOT timing approval.

Use the existing source-isolated runner's extraction, builds, proof/callback
checks, path/runtime seals and cleanup. Replace only its private loader with
exception-safe printing. Retain full output before parsing, including failures.
The original MatrixSupport and MatrixPerformance sources are not transformed.
No opaque closure/code/literal introspection is used.
"""
import argparse
from collections import Counter
from contextlib import contextmanager
import gzip
import importlib.util
import json
from pathlib import Path
import platform
import re
import signal
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
COMPAT = HERE.parent / "compatibility"
sys.path.insert(0, str(COMPAT))
import run_paired as paired
from acceptance import serial_lock

SPEC = importlib.util.spec_from_file_location("caller_assembly",
    HERE.parent / "fragments/assembly/run_assembly.py")
assembly = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(assembly)
require = paired.require
TARGETS = ("Cond_rewr.sml", "Traverse.sml", "simpLib.sml",
           "MatrixSupport.sml", "Performance.sml")
OPTIONAL = ("SimpTracking.sml",)
MARKER = "@@CALLER_CODEGEN\t"
HEADER = re.compile(r"(?:[^\s:]+|<top level>):?[ \t]*\n")
SCHEMA = "task29-caller-codegen-v1"


def instrument_runner(original, helper):
    require(original.count("    Meta.qquse path;\n") == 1,
            "unexpected paired loader source")
    require(original.count("open Paired\n") == 1,
            "unexpected paired runner header")
    result = original.replace("open Paired\n", "open Paired\n" + helper + "\n")
    return result.replace("    Meta.qquse path;\n", "    codegenUse path;\n")


def extents(text, private, optional):
    """Require complete, uniquely loaded private sources and printing spans.

    A duplicate, nested, missing, aborted or nonprivate extent is not evidence.
    Markers alone are insufficient: bind them to the paired use/used trace.
    Full raw stdout is kept separately; offsets below are one-indexed lines.
    """
    allowed = set(TARGETS) | set(OPTIONAL)
    require(set(optional) <= set(OPTIONAL), "unknown optional source")
    expected = set(TARGETS) | set(optional)
    lines = text.splitlines(keepends=True)
    require(text.endswith("\n"), "truncated compiler stdout")
    result, pending = {}, None
    events = paired.parse_events(text)
    used = [e[1] for e in events if e[0] == "use"]
    completed = [e[1] for e in events if e[0] == "used"]
    for i, line in enumerate(lines):
        if not line.startswith(MARKER):
            require("@@CALLER_CODEGEN" not in line, "malformed codegen marker")
            continue
        fields = line.rstrip("\n").split("\t")
        require(len(fields) == 3, "malformed codegen marker")
        _, stage, path = fields
        name = Path(path).name
        require(name in allowed and Path(path) == private / name,
                "unexpected/nonprivate compiler extent")
        if stage == "begin":
            require(pending is None and name not in result,
                    "nested/duplicate compiler extent")
            require(i > 0 and re.fullmatch(r"@@PAIR\t\d+\tuse\t" +
                    re.escape(path) + r"\n", lines[i-1]) is not None,
                    "compiler extent not bound to source use")
            pending = (name, i+1)
        else:
            require(stage == "end" and pending is not None and
                    pending[0] == name, "aborted/unmatched compiler extent")
            require(i+1 < len(lines) and re.fullmatch(
                r"@@PAIR\t\d+\tused\t" + re.escape(path) + r"\n",
                lines[i+1]) is not None,
                "compiler extent not bound to completed source use")
            require(used.count(path) == completed.count(path) == 1,
                    "source not uniquely loaded")
            start = pending[1]
            raw = "".join(lines[start:i])
            require(raw.strip(), "empty compiler extent")
            result[name] = dict(text=raw, stdout_start_line=start+1,
                                stdout_end_line=i)
            pending = None
    require(pending is None, "truncated compiler extent")
    require(set(result) == expected, "incomplete compiler source inventory")
    return result


def records(extent, *, require_optimized=True):
    """Keep every emitted pass/body, including repeated names, in order.

    Opaque printed constants and pool operands retain their literal text. This
    parser makes no claim that equal printed names imply equal literal values.
    """
    lines = extent["text"].splitlines(keepends=True)
    boundaries = [i for i, line in enumerate(lines) if
                  line.startswith("fn(") or HEADER.fullmatch(line)]
    result, occurrences = [], Counter()
    for start, end in zip(boundaries, boundaries[1:] + [len(lines)]):
        raw = "".join(lines[start:end])
        if lines[start].startswith("fn("):
            name = re.search(r'\(\*\s*"([^"]+)"', raw)
            require(name is not None, "optimized lambda has no name")
            name, kind = name[1], "optimized-tree"
        else:
            name = lines[start].strip()
            kind = ("assembly" if name.endswith(":") else
                    "backend-tree" if name == "LAMBDA(" else "icode")
            name = name.removesuffix(":")
        occurrences[kind, name] += 1
        row = dict(kind=kind, name=name,
            occurrence=occurrences[kind, name],
            stdout_start_line=extent["stdout_start_line"] + start,
            stdout_end_line=extent["stdout_start_line"] + end - 1,
            sha256=paired.digest(raw.encode()), bytes=len(raw.encode()))
        # Native bodies end before printer diagnostics/evaluation observations.
        # Do not feed trailing result/protocol text to the assembly decoder.
        if kind == "assembly":
            body = [lines[start]]
            for line in lines[start+1:end]:
                if assembly.ENTRY.fullmatch(line.rstrip("\n")):
                    body.append(line)
                elif not line.strip():
                    continue
                else:
                    require(not re.match(r"^[0-9A-F]{6}\s", line),
                            "unrecognized compiler listing entry")
                    break
            row["body"] = "".join(body)
            row["static"] = assembly.counts(row["body"])
            row["relocation_text"] = assembly.normalized(row["body"])
        result.append(row)
    required_kinds = ("icode", "assembly") + (
        ("optimized-tree",) if require_optimized else ())
    require(result and all(any(r["kind"] == k for r in result)
                           for k in required_kinds),
            "compiler did not emit every requested representation")
    return result


def compare(a, b):
    def keyed(rows):
        return {(r["kind"], r["name"], r["occurrence"]): r for r in rows}
    aa, bb = keyed(a), keyed(b)
    result = []
    for key in dict.fromkeys([*aa, *bb]):
        x, y = aa.get(key), bb.get(key)
        def metadata(r):
            return {k: v for k, v in r.items() if k not in
                    ("body", "relocation_text")} if r else None

        row = dict(kind=key[0], name=key[1], occurrence=key[2],
            baseline=metadata(x), candidate=metadata(y),
            exact_printed_text_equal=bool(x and y and
                                         x["sha256"] == y["sha256"]))
        if key[0] == "assembly":
            row["instruction_text_equal_after_pool_relocation"] = bool(
                x and y and x["relocation_text"] == y["relocation_text"])
        result.append(row)
    return result


def archive_stdout(output, label, text):
    path = output / (label + ".stdout.txt.gz")
    require(not path.exists(), "compiler output already archived")
    raw = text.encode()
    path.write_bytes(gzip.compress(raw, mtime=0))
    return dict(file=path.name, **paired.fingerprint(path),
                uncompressed_sha256=paired.digest(raw),
                uncompressed_bytes=len(raw))


@contextmanager
def diagnostic_loader(output, report):
    """Replace only a private loader, never production or workload sources."""
    original_install, original_compact = paired.install_fixtures, paired.compact
    helper = (HERE / "CallerCodegen.sml").read_text()
    collected = {}

    def install(dst, *args, **kwargs):
        original_install(dst, *args, **kwargs)
        runner = dst / "runner.sml"
        runner.write_text(instrument_runner(runner.read_text(), helper))

    def compact(receipt, dst, label):
        if receipt.get("fixture") == "performance":
            # Preserve the complete failed stdout too, before any parsing.
            saved = archive_stdout(output, label, receipt["stdout"])
            report["stdout"][label] = dict(saved)
            report["stdout"][label].update(
                process_accepted=receipt.get("accepted", False),
                diagnostic_accepted=False)
            if receipt.get("accepted"):
                private = Path(receipt["environment"]["PAIR_PRIVATE"])
                optional = [n for n in OPTIONAL if (private / n).exists()]
                spans = extents(receipt["stdout"], private, optional)
                collected[receipt["selection"]] = {
                    name: records(span, require_optimized=name not in OPTIONAL)
                    for name, span in spans.items()}
                report["stdout"][label]["extents"] = {
                    name: {k: v for k, v in span.items() if k != "text"}
                    for name, span in spans.items()}
                report["stdout"][label]["diagnostic_accepted"] = True
                receipt["compiler_stdout"] = saved
                # Complete output is archived once above. Retain protocol and
                # raw telemetry here, not another 66MB compiler dump. Original
                # stdout hash/length continue to describe the complete output.
                receipt["stdout"] = "".join(line for line in
                    receipt["stdout"].splitlines(keepends=True) if
                    line.startswith((paired.PREFIX, "@@MATRIX_")))
        original_compact(receipt, dst, label)

    paired.install_fixtures, paired.compact = install, compact
    try:
        yield collected
    finally:
        paired.install_fixtures = original_install
        paired.compact = original_compact


def collect(args, output, baseline_control):
    report = dict(schema=SCHEMA, success=False,
        baseline_control=baseline_control,
        scope="compiler printing diagnostic, NOT timing/allocation acceptance",
        stdout={}, inputs={}, limitations=[
            "Printing and the diagnostic loader alter layout and heap state.",
            "Equal disassembly after relocation does not bind pool contents.",
            "Printed opaque constant names do not establish value identity.",
            "Static reservations/calls are not dynamic execution totals.",
            "SimpTracking emits backend/ICode/native output but may omit the "
            "optimized-lambda printer form; no missing form is fabricated."])
    inputs = [Path(__file__), HERE / "CallerCodegen.sml",
              HERE / "test_caller_codegen.py",
              Path(assembly.__file__), Path(paired.__file__)]
    report["inputs"] = {str(p): paired.fingerprint(p) for p in inputs}
    old_argv = sys.argv
    error = None
    try:
        with diagnostic_loader(output, report) as collected:
            sys.argv = [str(Path(paired.__file__)), "--repo", str(args.repo),
                "--candidate",
                paired.BASE if baseline_control else args.candidate,
                "--candidate-signature", "pass", "--candidate-behavior",
                "baseline", "--matrix-performance", "--performance-case",
                args.case, "--performance-size", str(args.size),
                "--performance-pairs", "1", "--samples", "3",
                "--batch-seconds", "0.1", "--timeout", str(args.timeout),
                "--output", str(output / "paired")]
            if args.batch_iterations is not None:
                sys.argv += ["--batch-iterations", str(args.batch_iterations)]
            paired.main()
            require(set(collected) == {"baseline", "candidate"},
                    "missing compiler process")
            report["comparison"] = {name: compare(
                collected["baseline"].get(name, []),
                collected["candidate"].get(name, [])) for name in
                dict.fromkeys([*collected["baseline"],
                               *collected["candidate"]])}
            for path, seal in report["inputs"].items():
                require(paired.fingerprint(Path(path)) == seal,
                        "diagnostic input changed")
            report["success"] = True
    except (Exception, SystemExit, KeyboardInterrupt) as exc:
        report["failure"] = str(exc)
        error = exc
    finally:
        sys.argv = old_argv
        manifest_path = output / "paired/manifest.json"
        if manifest_path.exists():
            manifest = json.loads(manifest_path.read_text())
            # Deliberately incompatible with the timing acceptance schema.
            manifest["evidence_id"] = SCHEMA
            manifest["scope"] = report["scope"]
            if "performance" in manifest:
                manifest["performance"]["suite"] = "caller-codegen-diagnostic"
            manifest["diagnostic_inputs"] = report["inputs"]
            manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
            report["paired_manifest"] = paired.fingerprint(manifest_path)
        (output / "report.json.gz").write_bytes(gzip.compress(
            (json.dumps(report, indent=2) + "\n").encode(), mtime=0))
    if error is not None:
        raise paired.InvalidRun(report["failure"]) from error
    return report


def replay_report(output, repo):
    """Recheck transport, source/protocol binding and every comparison.

    The matrix auditor is used solely for its source/path/proof checks, on an
    explicit local copy of the diagnostic metadata. No timing decisions are
    made or written, and the archived suite remains inadmissible for timing.
    """
    from copy import deepcopy
    from audit_evidence import audit
    raw_report = gzip.decompress((output / "report.json.gz").read_bytes())
    report = json.loads(raw_report)
    require(report["schema"] == SCHEMA and report["success"],
            "incomplete diagnostic collection")
    path = output / "paired/manifest.json"
    require(paired.fingerprint(path) == report["paired_manifest"],
            "diagnostic manifest changed")
    manifest = json.loads(path.read_text())
    require(manifest["success"] and manifest["evidence_id"] == SCHEMA and
            manifest["performance"]["suite"] == "caller-codegen-diagnostic",
            "not a complete diagnostic manifest")
    require(manifest["diagnostic_inputs"] == report["inputs"],
            "diagnostic input binding mismatch")
    recorded_repo = Path(manifest["repo"])
    for raw, seal in report["inputs"].items():
        path = Path(raw)
        require(path.is_relative_to(recorded_repo),
                "diagnostic input outside repository")
        live = repo / path.relative_to(recorded_repo)
        require(paired.fingerprint(live) == seal, "diagnostic input changed")
    for selected in manifest["selections"].values():
        for source in selected["sources"]:
            raw = paired.git(repo, "show", selected["revision"] + ":" +
                             source["git_path"])
            require(dict(sha256=paired.digest(raw), bytes=len(raw)) ==
                    {k: source[k] for k in ("sha256", "bytes")},
                    "selected source differs from Git")
        tests = repo / "src/simp/tests"
        helper = (tests / "performance/CallerCodegen.sml").read_text()
        original = (tests / "compatibility/paired/runner.sml").read_text()
        raw = instrument_runner(original, helper).encode()
        require(selected["fixture_products"]["runner.sml"] ==
                dict(sha256=paired.digest(raw), bytes=len(raw)),
                "wrong diagnostic loader binding")
    checked = deepcopy(manifest)
    checked["performance"]["suite"] = "matrix"
    require(set(report["stdout"]) == {"pair-00-baseline", "pair-00-candidate"},
            "incomplete compiler process inventory")
    collected = {}
    for label, info in report["stdout"].items():
        require(info["process_accepted"] and info["diagnostic_accepted"],
                "rejected compiler process")
        require(info["file"] == label + ".stdout.txt.gz",
                "wrong compiler output name")
        path = output / info["file"]
        require(paired.fingerprint(path) == {k: info[k] for k in
                ("sha256", "bytes")}, "compiler output changed")
        raw = gzip.decompress(path.read_bytes())
        require(paired.digest(raw) == info["uncompressed_sha256"] and
                len(raw) == info["uncompressed_bytes"],
                "compiler output transport mismatch")
        text = raw.decode()
        receipt_path = output / "paired" / (label + ".json.gz")
        receipt = json.loads(gzip.decompress(receipt_path.read_bytes()))
        require(paired.digest(raw) == receipt["stdout_sha256"] and
                len(raw) == receipt["stdout_bytes"] and
                receipt["compiler_stdout"] == {k: v for k, v in info.items()
                    if k not in ("process_accepted", "diagnostic_accepted",
                                 "extents")},
                "compiler output/receipt binding mismatch")
        require(paired.parse_events(text) == receipt["result"]["events"],
                "compiler output/proof trace mismatch")
        audit(checked, receipt)
        selected = manifest["selections"][receipt["selection"]]
        names = {Path(s["git_path"]).name for s in selected["sources"]}
        spans = extents(text, Path(selected["private"]),
                        [n for n in OPTIONAL if n in names])
        require(info["extents"] == {name: {k: v for k, v in span.items()
                if k != "text"} for name, span in spans.items()},
                "compiler extent offsets changed")
        collected[receipt["selection"]] = {
            name: records(span, require_optimized=name not in OPTIONAL)
            for name, span in spans.items()}
    comparison = {name: compare(collected["baseline"].get(name, []),
        collected["candidate"].get(name, [])) for name in dict.fromkeys(
            [*collected["baseline"], *collected["candidate"]])}
    require(comparison == report["comparison"], "compiler comparison changed")
    return {name: dict(records=len(rows),
        exact_equal=sum(r["exact_printed_text_equal"] for r in rows),
        native_bodies=sum(r["kind"] == "assembly" for r in rows),
        native_equal_after_pool_relocation=sum(
            r.get("instruction_text_equal_after_pool_relocation", False)
            for r in rows))
        for name, rows in comparison.items()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--candidate", default="HEAD")
    parser.add_argument("--case", choices=("frag_record", "compile_collector"),
                        default="frag_record")
    parser.add_argument("--size", choices=(0, 1, 10, 100, 1000, 10000),
                        type=int, default=0)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--batch-iterations", type=int,
        help="common predeclared calibration history and sample count")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--replay", type=Path)
    parser.add_argument("--authorize-diagnostic", action="store_true")
    args = parser.parse_args(argv)
    if args.replay is not None:
        for label in ("baseline-control", "baseline-candidate"):
            summary = replay_report(args.replay.resolve() / label,
                                    args.repo.resolve())
            print(json.dumps({label: summary}, sort_keys=True))
        return
    require(args.authorize_diagnostic, "exclusive diagnostic window required")
    require(args.timeout > 0, "timeout must be positive")
    if args.batch_iterations is not None:
        from performance_schema import batch_iterations
        batch_iterations(args.batch_iterations)
    require(platform.machine() == "aarch64", "unsupported machine")

    def interrupted(signum, _frame):
        # Unwind the paired runner's temporary trees and child-process guard.
        raise KeyboardInterrupt("signal " + str(signum))

    for signum in (signal.SIGHUP, signal.SIGTERM):
        signal.signal(signum, interrupted)
    args.repo = args.repo.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    with serial_lock(args.repo) as fds:
        old_fds = paired.PERFORMANCE_LOCK_FDS
        paired.PERFORMANCE_LOCK_FDS = fds
        try:
            for label, control in (("baseline-control", True),
                                   ("baseline-candidate", False)):
                dst = output / label
                dst.mkdir()
                collect(args, dst, control)
        finally:
            paired.PERFORMANCE_LOCK_FDS = old_fds


if __name__ == "__main__":
    main()
