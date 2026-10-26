#!/usr/bin/env python3
"""Actual full Arm64 code pools; diagnostic only, NEVER timing acceptance.

Keeps the sealed v1 runtime_layout tool and archives unchanged. A native
interposer supplies the pool slots omitted by showSize. It is preloaded only
into diagnostic workload processes and activated by a post-workload postlude.
"""
import argparse
from collections import Counter, deque
from contextlib import contextmanager
from copy import deepcopy
import gzip
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import sys

sys.dont_write_bytecode = True
import runtime_layout as old

HERE = old.HERE
paired = old.paired
require = old.require
seal, save, load = old.seal, old.save, old.load
SCHEMA = "task29-runtime-pools-v1"
SUITE = "runtime-pools-diagnostic"
POOL = "@@RUNTIME_POOL\t"
HANDSHAKE = POOL + "loaded\tarm64-full64-v1"
BEGIN = re.compile(re.escape(POOL) +
    r"begin\t(0x[0-9a-f]+)\t(0x[0-9a-f]+)\t([0-9]+)\t(inline|split)")
RAW = re.compile(r"0x[0-9a-f]{16}")
LIMITS = [
    "Post-workload graph, NOT a measurement-boundary snapshot.",
    "Native preload and postlude/FFI can change heap/code/layout.",
    "Every code pool is supplied; unresolved referents remain explicit.",
    "Split-pool storage is separate from showSize's word accounting.",
    "Available instruction-bound targets are NOT executed-target traces.",
    "ADRP/LDR patterns can occur in non-address data, not just instructions.",
    "Raw-slot correspondence preserves mismatches, NOT pool permutation.",
    "One B/B and B/C structural pair is NOT timing/allocation acceptance.",
]


def instrument_runner(original):
    return old.instrument_runner(original).replace('"RuntimeLayout.sml"',
                                                    '"RuntimePools.sml"')


def bind_extent(text, private):
    # Reuse the original source-trace guards, with this distinct postlude.
    old.bind_extent(text.replace(str(private / "RuntimePools.sml"),
                                str(private / "RuntimeLayout.sml")), private)


def decode_pair(word, pc):
    """Dummy Arm64 ADRP x0/LDR x0 trailer, NOT executed instructions."""
    adrp, ldr = word & 0xffffffff, word >> 32
    require(adrp & 0x9f00001f == 0x90000000 and
            ldr & 0xffc003ff == 0xf9400000,
            "invalid split-pool trailer")
    imm = ((adrp >> 5) & 0x7ffff) * 4 + ((adrp >> 29) & 3)
    if imm & (1 << 20):
        imm -= 1 << 21
    return (pc & ~4095) + imm * 4096 + ((ldr >> 10) & 4095) * 8


def parse(text):
    """Validate every hook record against the independently printed objects.

    Do not read process memory. Keep owner/pool aliases, raw slots and the
    runtime's original word total. In split code the final dummy instruction
    pair is metadata and must not be decoded as executable references.
    """
    filtered, pools, active, slots = [], {}, None, []
    inside, loaded, last_owner, remaining = False, 0, None, 0
    for line in text.splitlines():
        if line.startswith(old.MARKER + "begin\t"):
            require(not inside, "nested layout extent")
            inside = True
        elif line.startswith(old.MARKER + "end\t"):
            require(active is None, "aborted pool record")
            inside = False
        if line == HANDSHAKE:
            require(inside and active is None and last_owner is not None and
                    loaded == 0 and remaining == 0,
                    "duplicate/outside/early pool handshake")
            loaded += 1
            continue
        match = BEGIN.fullmatch(line)
        if match:
            require(inside and loaded == 1 and active is None,
                    "unadmitted/nested pool record")
            owner, address, count, kind = match.groups()
            owner, address, count = (int(owner, 16), int(address, 16),
                                     int(count))
            require(owner == last_owner and owner not in pools and
                    remaining == 0, "duplicate/wrong/early pool owner")
            require(0 < address < 2**64 and address % 8 == 0 and
                    2 <= count < 2**61 and address + count * 8 < 2**64,
                    "invalid pool address/count")
            active, slots = (owner, address, count, kind), []
            continue
        if line.startswith(POOL + "end\t"):
            require(active is not None and line == POOL + "end\t" +
                    hex(active[0]), "wrong pool end owner")
            owner, address, count, kind = active
            require(len(slots) == count, "pool slot count mismatch")
            pools[owner] = dict(address=address, count=count, kind=kind,
                                slots=slots)
            active = None
            continue
        require(not line.startswith(POOL), "unknown pool marker")
        if active is not None:
            words = line.split()
            require(1 <= len(words) <= 4 and all(RAW.fullmatch(w)
                    for w in words), "invalid pool words")
            slots.extend(int(w, 16) for w in words)
            require(len(slots) <= active[2], "excess pool slots")
        else:
            header = old.HEADER.fullmatch(line)
            if header:
                last_owner = (int(header.group(3), 16)
                              if header.group(2) == "CODE" else None)
                remaining = int(header.group(4)) if last_owner else 0
            elif last_owner and line.strip():
                remaining -= len(line.split())
            filtered.append(line)
    require(active is None and loaded == 1, "missing/aborted pool admission")
    graph = old.parse("\n".join(filtered) + "\n")
    codes = [n for n in graph["nodes"] if n["kind"] == "CODE"]
    require(set(pools) == {n["address"] for n in codes},
            "missing/extra code pool records")
    shared = {}
    objects = {n["address"]: n for n in graph["nodes"]}
    for node in codes:
        pool = pools[node["address"]]
        if node["pool_status"] == "inline":
            require(pool["kind"] == "inline" and
                    pool["address"] == node["address"] +
                    node["pool_start_word"] * 8 and
                    pool["slots"] == node["fields"],
                    "inline pool disagrees with original CODE")
        else:
            require(pool["kind"] == "split" and
                    pool["address"] == decode_pair(node["native_words"][-1],
                        node["address"] + (node["words"] - 1) * 8),
                    "split pool disagrees with trailer")
            require(not node["address"] <= pool["address"] <
                    node["address"] + node["words"] * 8,
                    "split pool lies inside owner")
            previous = shared.setdefault(pool["address"], pool["slots"])
            require(previous == pool["slots"], "inconsistent shared pool")
            present = objects.get(pool["address"])
            if present:
                require(present["kind"] == "WORDS" and
                        present["fields"] == pool["slots"],
                        "split pool disagrees with traversed object")
            node["native_words"] = node["native_words"][:-1]
            node["fields"] = pool["slots"]
            node["pool_status"] = "split; supplied"
        node["pool_address"] = pool["address"]
    graph["pools"] = pools
    return graph


def code_references(node, graph):
    instructions = [i for word in node["native_words"]
                    for i in (word & 0xffffffff, word >> 32)]
    normalized, refs = instructions.copy(), []
    for index, instruction in enumerate(instructions):
        if instruction & 0x9f000000 != 0x90000000:
            continue
        imm = ((instruction >> 5) & 0x7ffff) * 4 + ((instruction >> 29) & 3)
        if imm & (1 << 20):
            imm -= 1 << 21
        page = ((node["address"] + index * 4) & ~4095) + imm * 4096
        row = dict(instruction_offset=index * 4, adrp=instruction,
                   page_address=page, status="unresolved ADRP use")
        if index + 1 < len(instructions):
            following = instructions[index + 1]
            row["following_instruction"] = following
            # Register 31 is XZR for ADRP, but SP for the LDR base. Equal
            # register numbers there do NOT establish a produced address.
            if instruction & 31 == 31:
                row["status"] = "unresolved ADRP XZR (not SP)"
            elif following & 0xffc00000 == 0xf9400000 and (
                    (following >> 5) & 31) == (instruction & 31):
                address = page + ((following >> 10) & 4095) * 8
                row["load_address"] = address
                offset = address - node["pool_address"]
                slot = offset // 8
                if offset % 8 == 0 and 0 <= slot < len(node["fields"]):
                    kind = ("split" if node["pool_status"].startswith("split")
                            else "inline")
                    row.update(status="resolved " + kind + " pool load",
                        pool_slot=slot,
                        target=old.target(node["fields"][slot], graph))
                    normalized[index] &= ~0x60ffffe0
                    normalized[index + 1] &= ~0x003ffc00
        refs.append(row)
    return dict(references=refs, unresolved_references=sum(
        not ref["status"].startswith("resolved") for ref in refs),
        normalized_instructions=normalized)


def inventory(graph):
    result = old.inventory(graph)
    by_address = {n["address"]: n for n in graph["nodes"]}
    for row in result["code"]:
        node = by_address[row["address"]]
        row["pool_address"] = node["pool_address"]
        row["code_references"] = code_references(node, by_address)
    split = {p["address"]: p for p in graph["pools"].values()
             if p["kind"] == "split"}
    result.update(pool_records=len(graph["pools"]),
        omitted_pools=0, unique_split_pools=len(split),
        split_pool_words_with_headers=sum(p["count"] + 1
                                         for p in split.values()),
        split_pool_words_already_in_showSize=sum(p["count"] + 1
            for a, p in split.items() if a in by_address),
        split_pool_owners=dict(Counter(str(p["address"])
            for p in graph["pools"].values() if p["kind"] == "split")))
    return result


def compare(left, right):
    """Root/slot paths and bijections for BOTH objects and pool ownership.

    Matching names never create correspondence; raw pool slot order and every
    mismatch remain. This is not instruction-target/pool-permutation equality.
    """
    aa = {n["address"]: n for n in left["nodes"]}
    bb = {n["address"]: n for n in right["nodes"]}
    queue = deque([(left["nodes"][0]["address"],
                    right["nodes"][0]["address"], "roots")])
    ab, ba, pool_ab, pool_ba, differences, native = {}, {}, {}, {}, [], []
    while queue:
        x, y, path = queue.popleft()
        if x in ab or y in ba:
            if ab.get(x) != y or ba.get(y) != x:
                differences.append(dict(baseline=x, candidate=y, path=path,
                                        reason="alias correspondence differs"))
            continue
        ab[x], ba[y] = y, x
        a, b = aa[x], bb[y]
        context = dict(baseline=x, candidate=y, path=path,
                       baseline_name=a["name"], candidate_name=b["name"])
        for key in ("kind", "mutable", "words", "name", "bytes",
                    "pool_status"):
            if a.get(key) != b.get(key):
                differences.append(dict(**context, field=key,
                    baseline_value=a.get(key), candidate_value=b.get(key)))
        if a["kind"] != b["kind"]:
            continue
        if a["kind"] == "CODE":
            if a["native_words"] != b["native_words"]:
                native.append(context)
            p, q = a["pool_address"], b["pool_address"]
            if (p in pool_ab or q in pool_ba) and (
                    pool_ab.get(p) != q or pool_ba.get(q) != p):
                differences.append(dict(**context, baseline_pool=p,
                    candidate_pool=q, reason="pool alias correspondence "
                    "differs"))
            else:
                pool_ab[p], pool_ba[q] = q, p
        if len(a["fields"]) != len(b["fields"]):
            differences.append(dict(**context, reason="slot count differs",
                baseline_slots=len(a["fields"]),
                candidate_slots=len(b["fields"])))
        for slot, (p, q) in enumerate(zip(a["fields"], b["fields"])):
            lp, rp = old.target(p, aa), old.target(q, bb)
            edge = ("." + old.ROOTS[slot] if path == "roots" else
                    ".pool[" + str(slot) + "]" if a["kind"] == "CODE" else
                    ".slot[" + str(slot) + "]")
            if "address" in lp and "address" in rp:
                queue.append((p, q, path + edge))
            elif "immediate" in lp and lp == rp:
                continue
            else:
                differences.append(dict(**context, slot=slot,
                    edge_path=path + edge,
                    baseline_target=lp, candidate_target=rp,
                    reason="different or unresolved slot"))
    return dict(scope="diagnostic correspondence; NOT runtime parity",
        matched_objects=len(ab), baseline_unmatched=len(aa)-len(ab),
        candidate_unmatched=len(bb)-len(ba), differences=differences,
        native_word_differences=native, matched_pools=len(pool_ab),
        baseline=inventory(left), candidate=inventory(right))


def inputs():
    return {str(p): seal(p) for p in (Path(__file__),
        HERE / "RuntimePools.sml", HERE / "test_runtime_pools.py",
        HERE / "runtime-pools/runtime_pools.cpp",
        Path(old.__file__), HERE / "RuntimeLayout.sml",
        Path(paired.__file__), HERE / "audit_evidence.py",
        HERE / "acceptance.py")}


def build(output, timeout):
    compiler = shutil.which("c++")
    require(compiler is not None, "C++ compiler missing")
    dst = output / "runtime-pools.so"
    command = [compiler, "-std=c++17", "-O2", "-fPIC", "-shared",
        "-Wall", "-Wextra", "-Werror",
        str(HERE / "runtime-pools/runtime_pools.cpp"), "-o", str(dst), "-ldl"]
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("LD_", "RUNTIME_POOLS_"))}
    receipt = paired.execute(command, HERE, env, timeout)
    (output / "native-build.json").write_text(json.dumps(receipt, indent=2)
                                              + "\n")
    require(receipt["exit"] == 0 and not receipt["timed_out"],
            "native pool interposer build failed")
    return dict(file=dst.name, **seal(dst), compiler=dict(
        path=compiler, **seal(Path(compiler).resolve())),
        build_receipt=seal(output / "native-build.json"))


@contextmanager
def diagnostic_loader(output, report):
    original_install, original_compact, original_execute = (
        paired.install_fixtures, paired.compact, paired.execute)
    graphs = {}

    def install(dst, *args, **kwargs):
        original_install(dst, *args, **kwargs)
        shutil.copyfile(HERE / "RuntimePools.sml", dst / "RuntimePools.sml")
        shutil.copyfile(output / "runtime-pools.so", dst / "runtime-pools.so")
        runner = dst / "runner.sml"
        runner.write_text(instrument_runner(runner.read_text()))

    def execute(command, cwd, env, timeout):
        if env.get("PAIR_FIXTURE") != "performance":
            return original_execute(command, cwd, env, timeout)
        private = Path(env["PAIR_PRIVATE"])
        require(list(map(str, command)) == [str(private / "paired.exe")],
                "unexpected native diagnostic command")
        library = private / "runtime-pools.so"
        require(seal(library) == {k: report["native"][k]
                                 for k in ("sha256", "bytes")},
                "private pool interposer differs")
        additions = dict(LD_PRELOAD=str(library),
                         RUNTIME_POOLS_LIBRARY=str(library))
        receipt = original_execute(command, cwd, dict(env, **additions),
                                   timeout)
        receipt["pool_environment"] = additions
        receipt["pool_interposer"] = seal(library)
        return receipt

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
            receipt["diagnostic_accepted"] = False
            try:
                if receipt.get("accepted"):
                    bind_extent(text, Path(
                        receipt["environment"]["PAIR_PRIVATE"]))
                    graphs[receipt["selection"]] = parse(text)
                    report["stdout"][label]["diagnostic_accepted"] = True
                    receipt["diagnostic_accepted"] = True
                    receipt["pool_stdout"] = info
                    receipt["stdout"] = "".join(line for line in
                        text.splitlines(keepends=True) if
                        line.startswith((paired.PREFIX, "@@MATRIX_")))
            except BaseException as exc:
                receipt["pool_rejection"] = str(exc)
                raise
            finally:
                # A rejected diagnostic must retain its process provenance,
                # not just stdout and a dangling manifest receipt reference.
                original_compact(receipt, dst, label)
        else:
            original_compact(receipt, dst, label)

    paired.install_fixtures, paired.compact, paired.execute = (
        install, compact, execute)
    try:
        yield graphs
    finally:
        paired.install_fixtures, paired.compact, paired.execute = (
            original_install, original_compact, original_execute)


def collect(args, output, control):
    report = dict(schema=SCHEMA, success=False, limits=LIMITS,
        baseline_control=control,
        candidate=paired.BASE if control else args.candidate,
        inputs=inputs(), stdout={})
    old_argv, error = sys.argv, None
    try:
        report["native"] = build(output, args.timeout)
        with diagnostic_loader(output, report) as graphs:
            sys.argv = [str(Path(paired.__file__)), "--repo", str(args.repo),
                "--candidate", report["candidate"], "--candidate-signature",
                "pass", "--candidate-behavior", "baseline",
                "--matrix-performance", "--performance-case", args.case,
                "--performance-size", str(args.size), "--performance-pairs",
                "1", "--samples", "3", "--batch-seconds", "0.1",
                "--batch-iterations", str(args.batch_iterations),
                "--timeout", str(args.timeout), "--output",
                str(output / "paired")]
            paired.main()
            require(set(graphs) == {"baseline", "candidate"},
                    "missing runtime pool process")
            report["comparison"] = compare(graphs["baseline"],
                                           graphs["candidate"])
            require(inputs() == report["inputs"], "pool inputs changed")
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
            manifest["pool_inputs"] = report["inputs"]
            path.write_text(json.dumps(manifest, indent=2) + "\n")
            report["paired_manifest"] = seal(path)
        save(output / "report.json.gz", report)
    if error is not None:
        raise paired.InvalidRun(report["failure"]) from error
    return report


def replay(output, repo, *, control=False):
    report = load(output / "report.json.gz")
    require(report["schema"] == SCHEMA and report["success"] and
            report["limits"] == LIMITS, "incomplete/wrong pool diagnostic")
    path = output / "paired/manifest.json"
    require(seal(path) == report["paired_manifest"], "pool manifest changed")
    manifest = json.loads(path.read_text())
    require(manifest["success"] and manifest["evidence_id"] == SCHEMA and
            manifest["performance"]["suite"] == SUITE and
            manifest["pool_inputs"] == report["inputs"], "wrong pool manifest")
    require(type(report["baseline_control"]) is bool and
            report["baseline_control"] is control and
            manifest["selections"]["baseline"]["revision"] == paired.BASE and
            manifest["selections"]["candidate"]["revision"] ==
            report["candidate"] and
            (not control or report["candidate"] == paired.BASE),
            "wrong pool control/source role")
    options = manifest["performance"]
    require(options["pairs"] == 1 and options["samples"] == 3 and
            options["batch_seconds"] == 0.1 and
            options["case"] in ("frag_record", "compile_collector"),
            "wrong pool workload options")
    recorded_repo = Path(manifest["repo"])
    require(set(report["inputs"]) == {
        str(recorded_repo / Path(p).relative_to(HERE.parents[3]))
        for p in inputs()}, "wrong pool input inventory")
    for raw, fingerprint in report["inputs"].items():
        path = Path(raw)
        require(path.is_relative_to(recorded_repo), "pool input escapes repo")
        require(seal(repo / path.relative_to(recorded_repo)) == fingerprint,
                "pool diagnostic input changed")
    native = report["native"]
    require(native["file"] == "runtime-pools.so" and
            seal(output / native["file"]) ==
            {k: native[k] for k in ("sha256", "bytes")} and
            seal(output / "native-build.json") == native["build_receipt"],
            "native interposer/build changed")
    build_receipt = json.loads((output / "native-build.json").read_text())
    compiler = native["compiler"]
    require(Path(compiler["path"]).is_absolute() and
            compiler["bytes"] > 0 and
            re.fullmatch(r"[0-9a-f]{64}", compiler["sha256"]) is not None,
            "invalid native compiler identity")
    command = build_receipt["command"]
    require(len(command) == 12 and command == [compiler["path"],
        "-std=c++17", "-O2", "-fPIC", "-shared", "-Wall", "-Wextra",
        "-Werror", str(recorded_repo /
            "src/simp/tests/performance/runtime-pools/runtime_pools.cpp"),
        "-o", str(Path(manifest["command"][-1]).parent /
                  "runtime-pools.so"), "-ldl"],
        "wrong native build command")
    from audit_evidence import command_record
    command_record(build_receipt, command, recorded_repo /
                   "src/simp/tests/performance")
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
        require(fixture["RuntimePools.sml"] == seal(HERE / "RuntimePools.sml"),
                "wrong pool postlude")
        require(fixture["runtime-pools.so"] ==
                {k: native[k] for k in ("sha256", "bytes")},
                "wrong fixture interposer")
    require(set(report["stdout"]) == {"pair-00-baseline", "pair-00-candidate"},
            "incomplete pool process inventory")
    checked, graphs = deepcopy(manifest), {}
    checked["performance"]["suite"] = "matrix"
    for label, info in report["stdout"].items():
        require(info["process_accepted"] and info["diagnostic_accepted"],
                "rejected pool process")
        require(info["file"] == label + ".stdout.txt.gz", "wrong stdout name")
        path = output / info["file"]
        require(seal(path) == {k: info[k] for k in ("sha256", "bytes")},
                "pool stdout changed")
        raw = gzip.decompress(path.read_bytes())
        require(paired.digest(raw) == info["uncompressed_sha256"] and
                len(raw) == info["uncompressed_bytes"],
                "pool transport changed")
        receipt = load(output / "paired" / (label + ".json.gz"))
        require(receipt["selection"] == label.removeprefix("pair-00-") and
                type(receipt["pair"]) is int and receipt["pair"] == 0 and
                receipt["fixture"] == "performance", "wrong pool selection")
        require(receipt["stdout_sha256"] == paired.digest(raw) and
                receipt["stdout_bytes"] == len(raw) and
                receipt["pool_stdout"] == {k: v for k, v in info.items()
                    if k not in ("process_accepted", "diagnostic_accepted")},
                "pool stdout/receipt mismatch")
        library = str(Path(receipt["environment"]["PAIR_PRIVATE"]) /
                      "runtime-pools.so")
        require(receipt["diagnostic_accepted"] is True and
            receipt["pool_environment"] == dict(
            LD_PRELOAD=library, RUNTIME_POOLS_LIBRARY=library) and
            receipt["pool_interposer"] ==
            {k: native[k] for k in ("sha256", "bytes")},
            "wrong native preload admission")
        text = raw.decode()
        require(paired.parse_events(text) == receipt["result"]["events"],
                "pool proof trace mismatch")
        old.audit(checked, receipt)
        bind_extent(text, Path(receipt["environment"]["PAIR_PRIVATE"]))
        graphs[receipt["selection"]] = parse(text)
    result = compare(graphs["baseline"], graphs["candidate"])
    require(result == report["comparison"], "pool comparison changed")
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
        results = []
        for label in ("baseline-control", "baseline-candidate"):
            dst = args.replay.resolve() / label
            results.append(json.loads((dst / "paired/manifest.json")
                                      .read_text())["performance"])
            result = replay(dst, args.repo.resolve(),
                            control=label == "baseline-control")
            print(json.dumps(dict(selection=label,
                matched_objects=result["matched_objects"],
                differences=len(result["differences"]))))
        require(results[0] == results[1], "different B/B and B/C schedules")
        return
    require(args.authorize_diagnostic, "explicit diagnostic authorization "
            "required")
    require(platform.machine() == "aarch64", "unsupported pool platform")
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
    with old.serial_lock(args.repo) as fds:
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
