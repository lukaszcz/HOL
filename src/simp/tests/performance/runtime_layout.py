#!/usr/bin/env python3
"""Post-workload actual object/code/pool diagnostic; NEVER timing acceptance.

The private runner loads a sealed postlude only after Performance returns.
Original workloads and their loader prefix are unchanged. showSize's raw dump
is retained, with addresses, before parsing. No unsafe runtime APIs are used.
"""
import argparse
from collections import Counter, deque
from contextlib import contextmanager
from copy import deepcopy
import gzip
import json
from pathlib import Path
import platform
import re
import signal
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "compatibility"))
import run_paired as paired
from acceptance import serial_lock
from audit_evidence import audit

require = paired.require
SCHEMA = "task29-runtime-layout-v1"
SUITE = "runtime-layout-diagnostic"
MARKER = "@@RUNTIME_LAYOUT\t"
ROOTS = ["run", "step", "measured", "experiment"]
HEADER = re.compile(r"(MUTABLE )?(BYTES|WORDS|CLOSURE|CODE):"
                    r"(0x[0-9a-f]+):(\d+)(?: (.*))?")
TOKEN = re.compile(r"0x[0-9a-f]+|\(nil\)|[0-9]+")
LIMITS = [
    "Post-workload reachable graph, NOT a measurement-boundary snapshot.",
    "Postlude compilation and traversal may change heap/layout after timing.",
    "Split constant pools are scanned but showSize omits their pool slots.",
    "Unresolved pointers and omitted slots are explicit, not equality.",
    "Available closure targets are not an execution trace of indirect calls.",
    "Native words retain relocation bits; differences need not mean extra work.",
    "ADRP/LDR patterns can occur in non-address data, not just instructions.",
    "One B/B and B/C structural pair is NOT timing/allocation acceptance.",
]


def seal(path):
    return paired.fingerprint(path)


def save(path, value):
    raw = (json.dumps(value, indent=2, allow_nan=False) + "\n").encode()
    with path.open("xb") as stream:
        stream.write(gzip.compress(raw, mtime=0))


def load(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def instrument_runner(original):
    anchor = "val _ = files ()\n"
    require(original.count(anchor) == 1, "unexpected paired runner footer")
    # A separate top-level declaration: not compiled before target execution.
    postlude = ('val _ = if result = "pass" andalso\n'
                '           Paired.env "PAIR_TARGET" = "Performance" then\n'
                '          tracedUse (OS.Path.concat\n'
                '            (Paired.env "PAIR_PRIVATE",\n'
                '             "RuntimeLayout.sml"))\n'
                '        else ()\n')
    return original.replace(anchor, postlude + anchor)


def value(token):
    require(TOKEN.fullmatch(token) is not None, "invalid object word")
    if token == "(nil)":
        return 0
    return int(token, 16 if token.startswith("0x") else 10)


def bind_extent(text, private):
    """Bind the dump to the traced postlude after target completion."""
    lines = text.splitlines()

    def event(stage, name):
        matches = [i for i, line in enumerate(lines) if re.fullmatch(
            r"@@PAIR\t\d+\t" + stage + "\t" +
            re.escape(str(private / name)), line)]
        require(len(matches) == 1, "missing/duplicate layout source trace")
        return matches[0]

    start = [i for i, line in enumerate(lines) if
             line.startswith(MARKER + "begin\t")]
    end = [i for i, line in enumerate(lines) if
           line.startswith(MARKER + "end\t")]
    require(len(start) == len(end) == 1 and
            event("used", "Performance.sml") <
            event("use", "RuntimeLayout.sml") < start[0] < end[0] <
            event("used", "RuntimeLayout.sml"),
            "layout dump outside post-workload source extent")


def parse(text):
    """Decode the documented full-64 Arm64 showSize format, fail closed.

    Instructions are NEVER treated as object pointers. Only word objects,
    closure slots and an in-object code constant segment supply graph edges.
    Raw code and addresses remain in stdout. Split-pool omissions stay blocked.
    """
    lines = text.splitlines()
    begin = MARKER + "begin\tArm64\t" + ",".join(ROOTS)
    starts = [i for i, line in enumerate(lines) if line == begin]
    ends = [i for i, line in enumerate(lines) if
            line.startswith(MARKER + "end\t")]
    require(len(starts) == len(ends) == 1 and starts[0] < ends[0],
            "missing/duplicate/aborted runtime layout extent")
    first, last = starts[0], ends[0]
    require(all(not line.startswith(MARKER) or i in (first, last)
                for i, line in enumerate(lines)), "unknown layout marker")
    require(lines[last].removeprefix(MARKER + "end\t").isdigit(),
            "invalid layout size footer")
    total = int(lines[last].split("\t")[-1])
    nodes, bad, pending, data = [], [], None, []

    def finish():
        if pending is None:
            return
        mutable, kind, address, length, name = pending
        n = int(length)
        require((n > 0 or kind in ("BYTES", "WORDS")) and
                (name is not None) == (kind == "CODE"),
                "invalid object header")
        if kind == "BYTES":
            require(all(re.fullmatch(r"[0-9a-f]{2}", t) for t in data) and
                    len(data) == n and n % 8 == 0,
                    "invalid/truncated byte object")
            fields = []
            payload = bytes.fromhex("".join(data)).hex()
        else:
            require(len(data) == n, "invalid/truncated word object")
            words = [value(t) for t in data]
            require(all(0 <= w < 2**64 for w in words), "word overflow")
            payload, fields = None, words
        row = dict(address=int(address, 16), kind=kind, mutable=bool(mutable),
                   words=n // 8 if kind == "BYTES" else n,
                   name=name, fields=fields, bytes=payload)
        if kind == "CODE":
            offset = words[-1]
            if offset >> 56 == 255:
                offset -= 2**64
                require(offset % 8 == 0, "unaligned code pool offset")
                start = n + offset // 8
                require(1 <= start < n, "invalid code pool offset")
                count = words[start - 1]
                require(count >= 2 and start + count == n - 1,
                        "invalid code pool count")
                row.update(pool_status="inline", pool_start_word=start,
                           native_words=words[:start-1],
                           fields=words[start:start+count])
            else:
                # Arm64's final dummy ADRP/LDR encodes a separate pool.
                # Do not invent its slot values from the traversal inventory.
                low, high = offset & 0xffffffff, offset >> 32
                require(low & 0x9f00001f == 0x90000000 and
                        high & 0xffc003ff == 0xf9400000,
                        "unrecognized split code pool trailer")
                row.update(pool_status="split; slots unavailable",
                           native_words=words, fields=[])
        nodes.append(row)

    for line in lines[first+1:last]:
        if not line.strip():
            continue
        header = HEADER.fullmatch(line)
        if header:
            finish()
            pending, data = header.groups(), []
        elif line.startswith("Bad address "):
            require(re.fullmatch(r"Bad address (?:0x)?0x[0-9a-f]+ found", line)
                    is not None, "invalid unresolved address")
            bad.append(line)
        else:
            require(pending is not None, "object data without header")
            data.extend(line.split())
    finish()
    require(nodes and len({n["address"] for n in nodes}) == len(nodes),
            "missing/duplicate runtime objects")
    require(sum(n["words"] + 1 for n in nodes) == total,
            "runtime layout word accounting mismatch")
    require(nodes[0]["kind"] == "WORDS" and len(nodes[0]["fields"]) == 4,
            "wrong runtime root tuple")
    known = {n["address"] for n in nodes}
    require(all(p in known for p in nodes[0]["fields"]),
            "unresolved runtime root")
    return dict(total_words=total, nodes=nodes, bad_addresses=bad)


def target(word, graph):
    if word == 0 or word & 1:
        return dict(immediate=word)
    node = graph.get(word)
    if not node:
        return dict(unresolved_address=word)
    result = dict(address=word, kind=node["kind"], name=node["name"])
    if node["kind"] in ("WORDS", "CLOSURE") and node["fields"]:
        entry = graph.get(node["fields"][0])
        if entry and entry["kind"] == "CODE":
            result.update(entry_code_address=entry["address"],
                          entry_code_name=entry["name"],
                          capture_words=node["words"] - 1)
    if node["kind"] == "BYTES":
        result["bytes_sha256"] = paired.digest(bytes.fromhex(node["bytes"]))
    return result


def code_references(node, graph):
    """Decode adjacent ADRP/LDR64 from actual little-endian Arm64 words.

    Resolve each operand against this CODE object's inline constant slots,
    not a same-named compiler listing. Other ADRP uses and split pools retain
    their raw operands and remain unresolved. No process memory is read.
    """
    instructions = [i for word in node["native_words"]
                    for i in (word & 0xffffffff, word >> 32)]
    normalized = instructions.copy()
    refs = []
    for index, instruction in enumerate(instructions):
        if instruction & 0x9f000000 != 0x90000000:
            continue
        imm = ((instruction >> 5) & 0x7ffff) * 4 + ((instruction >> 29) & 3)
        if imm & (1 << 20):
            imm -= 1 << 21
        pc = node["address"] + index * 4
        page = (pc & ~4095) + imm * 4096
        row = dict(instruction_offset=index * 4, adrp=instruction,
                   page_address=page, status="unresolved ADRP use")
        if index + 1 < len(instructions):
            following = instructions[index+1]
            row["following_instruction"] = following
            if following & 0xffc00000 == 0xf9400000 and (
                    (following >> 5) & 31) == (instruction & 31):
                address = page + ((following >> 10) & 4095) * 8
                row["load_address"] = address
                if node["pool_status"] == "inline":
                    offset = address - node["address"]
                    slot = offset // 8 - node["pool_start_word"]
                    if offset % 8 == 0 and 0 <= slot < len(node["fields"]):
                        row.update(status="resolved inline pool load",
                                   pool_slot=slot,
                                   target=target(node["fields"][slot], graph))
                        # Clear ONLY address immediate bits; preserve opcode,
                        # both registers, and the resolved target.
                        normalized[index] &= ~0x60ffffe0
                        normalized[index+1] &= ~0x003ffc00
        refs.append(row)
    return dict(references=refs,
                unresolved_references=sum(
                    not ref["status"].startswith("resolved") for ref in refs),
                normalized_instructions=normalized)


def inventory(graph):
    nodes = graph["nodes"]
    by_address = {n["address"]: n for n in nodes}
    roots = {label: by_address[p] for label, p in
             zip(ROOTS, nodes[0]["fields"])}
    return dict(total_words=graph["total_words"], objects=len(nodes),
        kinds=dict(Counter(n["kind"] for n in nodes)),
        split_pools=sum(n.get("pool_status", "").startswith("split")
                        for n in nodes),
        bad_addresses=graph["bad_addresses"],
        unresolved_slots=sum("unresolved_address" in target(p, by_address)
                             for n in nodes for p in n["fields"]),
        roots={label: dict(address=n["address"], kind=n["kind"],
            words=n["words"], fields=[target(p, by_address)
                                     for p in n["fields"]])
               for label, n in roots.items()},
        code=[dict(address=n["address"], name=n["name"], words=n["words"],
            pool_status=n["pool_status"],
            pool=[target(p, by_address) for p in n["fields"]],
            code_references=code_references(n, by_address),
            native_words_sha256=paired.digest(b"".join(
                w.to_bytes(8, "little") for w in n["native_words"])))
              for n in nodes if n["kind"] == "CODE"])


def compare(left, right):
    """Root/slot anchored correspondence, preserving aliasing and all faults.

    This is not address stripping or graph equality inferred from code names.
    Native-byte differences and missing pools remain separate from data edges.
    """
    aa = {n["address"]: n for n in left["nodes"]}
    bb = {n["address"]: n for n in right["nodes"]}
    queue = deque([(left["nodes"][0]["address"],
                    right["nodes"][0]["address"])])
    ab, ba, differences, native = {}, {}, [], []
    while queue:
        x, y = queue.popleft()
        if x in ab or y in ba:
            if ab.get(x) != y or ba.get(y) != x:
                differences.append(dict(baseline=x, candidate=y,
                                        reason="alias correspondence differs"))
            continue
        ab[x], ba[y] = y, x
        a, b = aa[x], bb[y]
        context = dict(baseline=x, candidate=y, baseline_name=a["name"],
                       candidate_name=b["name"])
        for key in ("kind", "mutable", "words", "name", "bytes",
                    "pool_status"):
            if a.get(key) != b.get(key):
                differences.append(dict(**context, field=key,
                    baseline_value=a.get(key), candidate_value=b.get(key)))
        if a["kind"] != b["kind"]:
            continue
        if a["kind"] == "CODE" and a["native_words"] != b["native_words"]:
            native.append(context)
        if len(a["fields"]) != len(b["fields"]):
            differences.append(dict(**context, reason="slot count differs",
                baseline_slots=len(a["fields"]),
                candidate_slots=len(b["fields"])))
        for slot, (p, q) in enumerate(zip(a["fields"], b["fields"])):
            # Tagged integers can numerically coincide with an object address
            # only in malformed data; never infer pointers from instructions.
            lp, rp = target(p, aa), target(q, bb)
            if "address" in lp and "address" in rp:
                queue.append((p, q))
            elif "immediate" in lp and lp == rp:
                continue
            else:
                differences.append(dict(**context, slot=slot,
                    baseline_target=lp, candidate_target=rp,
                    reason="different or unresolved slot"))
    return dict(scope="diagnostic correspondence; NOT runtime parity",
        matched_objects=len(ab), baseline_unmatched=len(aa)-len(ab),
        candidate_unmatched=len(bb)-len(ba), differences=differences,
        native_word_differences=native,
        baseline=inventory(left), candidate=inventory(right))


def inputs():
    return {str(p): seal(p) for p in (Path(__file__),
        HERE / "RuntimeLayout.sml", HERE / "test_runtime_layout.py",
        Path(paired.__file__), HERE / "audit_evidence.py",
        HERE / "acceptance.py")}


@contextmanager
def diagnostic_loader(output, report):
    original_install = paired.install_fixtures
    original_compact = paired.compact
    graphs = {}

    def install(dst, *args, **kwargs):
        original_install(dst, *args, **kwargs)
        (dst / "RuntimeLayout.sml").write_bytes(
            (HERE / "RuntimeLayout.sml").read_bytes())
        runner = dst / "runner.sml"
        runner.write_text(instrument_runner(runner.read_text()))

    def compact(receipt, dst, label):
        if receipt.get("fixture") == "performance":
            text = receipt["stdout"]
            path = output / (label + ".stdout.txt.gz")
            with path.open("xb") as stream:
                stream.write(gzip.compress(text.encode(), mtime=0))
            info = dict(file=path.name, **seal(path),
                uncompressed_sha256=paired.digest(text.encode()),
                uncompressed_bytes=len(text.encode()))
            report["stdout"][label] = dict(**info,
                process_accepted=receipt.get("accepted", False),
                diagnostic_accepted=False)
            if receipt.get("accepted"):
                bind_extent(text, Path(receipt["environment"]["PAIR_PRIVATE"]))
                graphs[receipt["selection"]] = parse(text)
                report["stdout"][label]["diagnostic_accepted"] = True
                receipt["layout_stdout"] = info
                receipt["stdout"] = "".join(line for line in
                    text.splitlines(keepends=True) if
                    line.startswith((paired.PREFIX, "@@MATRIX_")))
        original_compact(receipt, dst, label)

    paired.install_fixtures, paired.compact = install, compact
    try:
        yield graphs
    finally:
        paired.install_fixtures = original_install
        paired.compact = original_compact


def collect(args, output, control):
    report = dict(schema=SCHEMA, success=False, limits=LIMITS,
                  baseline_control=control,
                  candidate=paired.BASE if control else args.candidate,
                  inputs=inputs(), stdout={})
    old_argv, error = sys.argv, None
    try:
        with diagnostic_loader(output, report) as graphs:
            sys.argv = [str(Path(paired.__file__)), "--repo", str(args.repo),
                "--candidate", paired.BASE if control else args.candidate,
                "--candidate-signature", "pass", "--candidate-behavior",
                "baseline", "--matrix-performance", "--performance-case",
                args.case, "--performance-size", str(args.size),
                "--performance-pairs", "1", "--samples", "3",
                "--batch-seconds", "0.1", "--batch-iterations",
                str(args.batch_iterations), "--timeout", str(args.timeout),
                "--output", str(output / "paired")]
            paired.main()
            require(set(graphs) == {"baseline", "candidate"},
                    "missing runtime layout process")
            report["comparison"] = compare(graphs["baseline"],
                                           graphs["candidate"])
            require(inputs() == report["inputs"], "layout inputs changed")
            report["success"] = True
    except (Exception, SystemExit, KeyboardInterrupt) as exc:
        report["failure"], error = str(exc), exc
    finally:
        sys.argv = old_argv
        path = output / "paired/manifest.json"
        if path.exists():
            manifest = json.loads(path.read_text())
            manifest["evidence_id"] = SCHEMA
            manifest["performance"]["suite"] = SUITE
            manifest["layout_inputs"] = report["inputs"]
            path.write_text(json.dumps(manifest, indent=2) + "\n")
            report["paired_manifest"] = seal(path)
        save(output / "report.json.gz", report)
    if error is not None:
        raise paired.InvalidRun(report["failure"]) from error
    return report


def replay(output, repo, *, control=False):
    report = load(output / "report.json.gz")
    require(report["schema"] == SCHEMA and report["success"] and
            report["limits"] == LIMITS, "incomplete/wrong layout diagnostic")
    path = output / "paired/manifest.json"
    require(seal(path) == report["paired_manifest"], "layout manifest changed")
    manifest = json.loads(path.read_text())
    require(manifest["success"] and manifest["evidence_id"] == SCHEMA and
            manifest["performance"]["suite"] == SUITE and
            manifest["layout_inputs"] == report["inputs"],
            "wrong layout manifest")
    require(type(report["baseline_control"]) is bool and
            report["baseline_control"] is control and
            manifest["selections"]["baseline"]["revision"] == paired.BASE and
            manifest["selections"]["candidate"]["revision"] ==
            report["candidate"] and
            (not control or report["candidate"] == paired.BASE),
            "wrong layout control/source role")
    options = manifest["performance"]
    require(options["pairs"] == 1 and options["samples"] == 3 and
            options["batch_seconds"] == 0.1 and
            options["case"] in ("frag_record", "compile_collector"),
            "wrong layout workload options")
    recorded_repo = Path(manifest["repo"])
    require(set(report["inputs"]) ==
            {str(recorded_repo / Path(p).relative_to(HERE.parents[3]))
             for p in inputs()}, "wrong layout input inventory")
    for raw, fingerprint in report["inputs"].items():
        path = Path(raw)
        require(path.is_relative_to(recorded_repo),
                "layout input escapes repo")
        require(seal(repo / path.relative_to(recorded_repo)) == fingerprint,
                "layout diagnostic input changed")
    for selection in manifest["selections"].values():
        for source in selection["sources"]:
            raw = paired.git(repo, "show", selection["revision"] + ":" +
                             source["git_path"])
            require(dict(sha256=paired.digest(raw), bytes=len(raw)) ==
                    {k: source[k] for k in ("sha256", "bytes")},
                    "selected source differs from Git")
        fixture = selection["fixture_products"]
        runner = repo / "src/simp/tests/compatibility/paired/runner.sml"
        raw = instrument_runner(runner.read_text()).encode()
        require(fixture["runner.sml"] ==
                dict(sha256=paired.digest(raw), bytes=len(raw)),
                "wrong post-workload loader")
        require(fixture["RuntimeLayout.sml"] ==
                seal(repo / "src/simp/tests/performance/RuntimeLayout.sml"),
                "wrong layout postlude")
    require(set(report["stdout"]) == {"pair-00-baseline", "pair-00-candidate"},
            "incomplete layout process inventory")
    checked, graphs = deepcopy(manifest), {}
    checked["performance"]["suite"] = "matrix"
    for label, info in report["stdout"].items():
        require(info["process_accepted"] and info["diagnostic_accepted"],
                "rejected layout process")
        require(info["file"] == label + ".stdout.txt.gz", "wrong stdout name")
        path = output / info["file"]
        require(seal(path) == {k: info[k] for k in ("sha256", "bytes")},
                "layout stdout changed")
        raw = gzip.decompress(path.read_bytes())
        require(paired.digest(raw) == info["uncompressed_sha256"] and
                len(raw) == info["uncompressed_bytes"],
                "layout transport changed")
        receipt = load(output / "paired" / (label + ".json.gz"))
        require(receipt["selection"] == label.removeprefix("pair-00-") and
                type(receipt["pair"]) is int and receipt["pair"] == 0 and
                receipt["fixture"] == "performance",
                "wrong layout process selection/pair")
        require(receipt["stdout_sha256"] == paired.digest(raw) and
                receipt["stdout_bytes"] == len(raw) and
                receipt["layout_stdout"] == {k: v for k, v in info.items()
                    if k not in ("process_accepted", "diagnostic_accepted")},
                "layout stdout/receipt binding mismatch")
        text = raw.decode()
        require(paired.parse_events(text) == receipt["result"]["events"],
                "layout proof trace mismatch")
        audit(checked, receipt)
        bind_extent(text, Path(receipt["environment"]["PAIR_PRIVATE"]))
        graphs[receipt["selection"]] = parse(text)
    result = compare(graphs["baseline"], graphs["candidate"])
    require(result == report["comparison"], "layout comparison changed")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--candidate", default="HEAD")
    parser.add_argument("--case", choices=("frag_record", "compile_collector"),
                        default="frag_record")
    parser.add_argument("--size", type=int,
                        choices=(0, 1, 10, 100, 1000, 10000), default=0)
    parser.add_argument("--batch-iterations", type=int)
    parser.add_argument("--timeout", type=int, default=1800)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--replay", type=Path)
    parser.add_argument("--authorize-diagnostic", action="store_true")
    args = parser.parse_args(argv)
    if args.replay:
        def options(label):
            path = args.replay / label / "paired/manifest.json"
            return json.loads(path.read_text())["performance"]
        require(options("baseline-control") == options("baseline-candidate"),
                "different B/B and B/C workload options")
        for label in ("baseline-control", "baseline-candidate"):
            result = replay(args.replay.resolve() / label, args.repo.resolve(),
                            control=label == "baseline-control")
            print(json.dumps(dict(selection=label,
                matched_objects=result["matched_objects"],
                differences=len(result["differences"]),
                native_word_differences=len(
                    result["native_word_differences"]))))
        return
    require(args.authorize_diagnostic,
            "explicit diagnostic authorization required")
    require(platform.machine() == "aarch64", "unsupported layout platform")
    from performance_schema import batch_iterations
    batch_iterations(args.batch_iterations)
    require(args.batch_iterations is not None and args.timeout > 0,
            "predeclared count and positive timeout required")

    def interrupted(signum, _frame):
        raise KeyboardInterrupt("signal " + str(signum))

    for signum in (signal.SIGHUP, signal.SIGTERM):
        signal.signal(signum, interrupted)
    args.repo = args.repo.resolve()
    args.candidate = paired.git(args.repo, "rev-parse", args.candidate +
                                "^{commit}").decode().strip()
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
