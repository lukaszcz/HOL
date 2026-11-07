#!/usr/bin/env python3
"""Compiler-emitted AArch64 bodies, not closure introspection or timing."""
import argparse
from collections import Counter
import difflib
import gzip
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import run_fragments as fragments
paired = fragments.paired
require = paired.require
ROOTS = ("ac_ss", "SSFRAG", "ssf_upd_rewrs", "name_ss", "rewrites",
         "merge_ss")
HELPERS = ("frag_name", "frag_rewrites", "rewrites_with_names", "merge_names",
           "named_rewrites", "named_rewrites_with_names", "named_merge_ss",
           "add_named_rwt", "D")
CHECKS = ("assembly reset", "rewrites/name_ss", "SSFRAG", "ssf_upd_rewrs",
          "merge_ss", "ac_ss", "persistent original")
OBS = [["check", name, "pass"] for name in CHECKS] + [
    ["observation", "complete", "fragment-assembly-v1"]]
ENTRY = re.compile(r"^([0-9A-F]{6})  ([0-9A-F]{8})\s+(.+?)\s*$")
HEADER = re.compile(r"^(simpLib\.[^\s:]+):\s*$")


def simp_extent(text, private):
    """Exact lines and stdout offset for the private source use."""
    lines = text.splitlines(keepends=True)
    start = [i for i, line in enumerate(lines) if re.fullmatch(
        r"@@PAIR\t\d+\tuse\t" + re.escape(str(private / "simpLib.sml")) +
        r"\n", line)]
    end = [i for i, line in enumerate(lines) if re.fullmatch(
        r"@@PAIR\t\d+\tused\t" + re.escape(str(private / "simpLib.sml")) +
        r"\n", line)]
    require(len(start) == len(end) == 1 and start[0] < end[0],
            "missing/duplicate simpLib emission extent")
    return lines[start[0] + 1:end[0]], start[0] + 1


def extract(text, private):
    """Only bodies emitted between the traced simpLib use/used markers."""
    lines, _ = simp_extent(text, private)
    bodies, name, raw = {}, None, []

    def save():
        if name is not None and any(re.match(
                r"simpLib\." + re.escape(root) + r"(?:\(|$)", name)
                for root in ROOTS + HELPERS):
            require(raw and any(ENTRY.match(line) for line in raw),
                    "empty body")
            # Poly/ML can emit multiple specializations under the same name.
            # Retain every occurrence in emission order, never deduplicate.
            occurrence = 1
            key = name
            while key in bodies:
                occurrence += 1
                key = name + "@" + str(occurrence)
            bodies[key] = "".join(raw)

    for line in lines:
        header = HEADER.fullmatch(line.rstrip("\n"))
        if header:
            save()
            name, raw = header[1], [line]
        elif name is not None:
            if ENTRY.match(line) or not line.strip():
                raw.append(line)
            else:
                require(not re.match(r"^[0-9A-F]{6}\s", line),
                        "unrecognized compiler listing entry: " + line)
                save()
                name, raw = None, []
    save()
    require(bodies, "compiler emitted no named simpLib bodies")
    return {name: body for name, body in bodies.items()
            if any(re.match(r"simpLib\." + re.escape(root) + r"(?:\(|$)", name)
                   for root in ROOTS + HELPERS)}


def extract_compiler(text, private):
    """Exact optimized lambdas + ICode passes for the merge call chain only.

    Poly/ML 5.9.2 prints a top-level optimized lambda at column zero,
    followed by backend trees, named ICode passes and assembly. Nested
    lambdas are indented. Keep all selected passes, including concrete
    registers, and foldr native bodies when their ICode names merge_names.
    Never normalize tree operands or assume same-name constants identical.
    """
    lines, offset = simp_extent(text, private)
    boundaries = [i for i, line in enumerate(lines) if
                  line.startswith("fn(") or re.fullmatch(
                      r"(?:[^\s:]+|<top level>):?[ \t]*\n", line)]
    result, previous = [], None
    for start, end in zip(boundaries, boundaries[1:] + [len(lines)]):
        raw = "".join(lines[start:end])
        if lines[start].startswith("fn("):
            # The name comment can wrap across lines in a long lambda header.
            name = re.search(r'\(\*\s*"([^"]+)"', raw)
            require(name is not None, "optimized lambda has no name")
            name, kind = name[1], "optimized-tree"
        else:
            name = lines[start].strip()
            kind = "assembly" if name.endswith(":") else "icode"
            name = name.removesuffix(":")
        direct = bool(re.match(
            r"simpLib\.(?:merge_ss|merge_names)(?:\(|$)", name))
        fold = name == "List.foldr(3)()" and (
            '"simpLib.merge_names(' in raw or
            (kind == "assembly" and previous == (name, "icode", True)))
        selected = (direct and kind != "assembly") or fold
        previous = name, kind, selected
        if selected:
            result.append(dict(kind=kind, name=name, text=raw,
                stdout_start_line=offset + start + 1,
                stdout_end_line=offset + end,
                sha256=paired.digest(raw.encode())))
    require(any(r["kind"] == "optimized-tree" and
                r["name"] == "simpLib.merge_ss(1)" for r in result),
            "missing optimized merge_ss tree")
    require(any(r["kind"] == "icode" and
                r["name"] == "simpLib.merge_ss(1)" and
                "FunctionCall" in r["text"] for r in result),
            "missing merge_ss ICode calls")
    return result


def entries(body):
    result = []
    for line in body.splitlines()[1:]:
        if not line.strip():
            continue
        match = ENTRY.fullmatch(line)
        require(match is not None, "unrecognized assembly entry: " + line)
        offset, word, asm = match.groups()
        asm = re.sub(r"\s+", " ", asm)
        result.append((offset, word, asm))
    require(result and [int(e[0], 16) for e in result] ==
            list(range(0, 4 * len(result), 4)), "noncontiguous body")
    return result


def normalized(body):
    """Preserve offsets, control targets and all non-pool operands exactly.

    Only adjacent adrp R,page; ldr X,[R,#offset] is a relocatable pool
    materialization. Both entries remain; field/stack loads never match.
    Machine words are excluded from comparison but retained in exact bodies.
    """
    rows = entries(body)
    result = [f"{offset} {asm}" for offset, _, asm in rows]
    for i, (offset, _, asm) in enumerate(rows):
        page = re.fullmatch(r"adrp (x\d+),0x[0-9A-Fa-f]+", asm)
        if not page:
            continue
        require(i + 1 < len(rows), "truncated adrp pool pair")
        load = re.fullmatch(r"ldr (x\d+),\[" + page[1] + r",#(\d+)\]",
                            rows[i + 1][2])
        require(load is not None, "unsupported adrp (not adjacent pool load)")
        result[i] = f"{offset} adrp {page[1]},POOL_PAGE"
        result[i + 1] = (f"{rows[i + 1][0]} ldr {load[1]},"
                         f"[{page[1]},#POOL_OFFSET]")
    return result


def counts(body):
    rows = entries(body)
    instructions = [asm for _, _, asm in rows
                    if asm != "?" and not asm.startswith("[")]
    mnemonics = Counter(asm.split()[0] for asm in instructions)
    # Static reservations only: loops/callees/slow paths are not executions.
    reserves = [asm for asm in instructions
                if re.fullmatch(r"sub x\d+,x27,#\d+", asm)]
    return dict(instructions=len(instructions), entries=len(rows),
                gc_maps=sum(asm.startswith("[") for _, _, asm in rows),
                padding=sum(asm == "?" for _, _, asm in rows),
                mnemonics=dict(sorted(mnemonics.items())),
                calls=sum(mnemonics[k] for k in ("bl", "blr")),
                allocation_reservations=reserves)


def compare(baseline, candidate):
    result = {}
    for name in dict.fromkeys([*baseline, *candidate]):
        a, b = baseline.get(name), candidate.get(name)
        na, nb = normalized(a) if a else [], normalized(b) if b else []
        result[name] = dict(baseline=counts(a) if a else None,
            candidate=counts(b) if b else None,
            identical_after_pool_relocation=bool(a and b and na == nb),
            support="paired" if a and b else
                    "not emitted by " + ("candidate" if a else "baseline") +
                    "; possibly inlined, not assumed zero work",
            diff=(list(difflib.unified_diff(na, nb, fromfile="baseline",
                                           tofile="candidate", lineterm=""))
                  if a and b else []))
    for side, bodies in (("baseline", baseline), ("candidate", candidate)):
        for root in ROOTS:
            require(any(n.startswith("simpLib." + root + "(") for n in bodies),
                    side + " required function not emitted "
                    "(possibly inlined): " + root)
    return result


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[4])
    parser.add_argument("--candidate", default="worktree")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--optimized-tree", action="store_true",
        help="print optimized codetree and ICode only for private simpLib; "
             "retain exact merge caller/helper evidence (no introspection)")
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    return args


def main():
    args = parse_args()

    def interrupted(signum, _frame):
        # Unwind TemporaryDirectory and execute()'s child-process cleanup.
        raise KeyboardInterrupt("signal " + str(signum))

    for signum in (signal.SIGHUP, signal.SIGTERM):
        signal.signal(signum, interrupted)
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    manifest = dict(schema_version=1, success=False,
        evidence_id="fragment-assembly-v1", repo=str(repo),
        scope="compiler-generated static native bodies; isolated simplifier "
              "sources and shared dependencies; NOT timing, dynamic "
              "instruction counts, or cumulative allocation",
        command=[sys.executable, *sys.argv], machine=platform.machine(),
        optimized_tree=args.optimized_tree,
        selections={}, runs=[], inputs={}, tools={}, shared_products={})
    try:
        require(platform.machine() == "aarch64", "unsupported machine")
        manifest["git_status"] = paired.git(
            repo, "status", "--porcelain=v1").decode()
        inputs = [HERE / n for n in ("selftest.sml", "runner.sml",
            "run_assembly.py", "test_assembly.py", "README.md", "Holmakefile")]
        abi = paired.HERE.parent / "performance/review-20261021/abicheck.sml"
        inputs += [Path(fragments.__file__), Path(paired.__file__), abi,
                   *sorted((paired.HERE / "paired").glob("*.sml")),
                   paired.HERE / "paired/Holmakefile"]
        manifest["inputs"] = {str(f.relative_to(repo)): paired.fingerprint(f)
                              for f in inputs}
        manifest["tools"] = {name: paired.fingerprint(repo / name) for name in
            ("bin/hol", "bin/Holmake", "bin/hol.state0", "holproject.toml")}
        poly = shutil.which("poly", path=env["PATH"])
        require(poly is not None, "poly not found")
        manifest["tools"][str(Path(poly).resolve())] = paired.fingerprint(
            Path(poly).resolve())
        version = paired.execute([poly, "-v"], repo, env, args.timeout)
        manifest["poly_version"] = version
        require(version["exit"] == 0 and not version["timed_out"] and
                version["stdout"].strip() == "Poly/ML 5.9.2 Release",
                "unsupported compiler version")
        linked = paired.execute(["ldd", str(repo / "bin/hol")], repo, env,
                                args.timeout)
        require(linked["exit"] == 0 and not linked["timed_out"],
                "runtime library discovery failed")
        manifest["dynamic_libraries"] = linked
        for name in re.findall(r"(/[^\s()]+)", linked["stdout"]):
            manifest["tools"][name] = paired.fingerprint(Path(name).resolve())
        with tempfile.TemporaryDirectory(prefix="fragment-assembly-") as temp:
            root, inventories, seals = Path(temp), {}, {}
            for side, ref in (("baseline", paired.BASE),
                              ("candidate", args.candidate)):
                dst = root / side
                dst.mkdir()
                rev, inventory = fragments.snapshot(repo, ref, dst)
                inventories[side] = inventory
                paired.install_fixtures(dst)
                for name in ("selftest.sml", "runner.sml"):
                    shutil.copyfile(HERE / name, dst / name)
                (dst / "Holmakefile").write_text(
                    "HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
                    "paired.exe: runner.uo CheckSupport.uo selftest.uo\n"
                    "\t$(HOLMOSMLC) -o $@ $<\n")
                seals.update({str(f): paired.fingerprint(f)
                              for f in dst.iterdir() if f.is_file()})
                selected = dict(reference=ref, revision=rev, sources=inventory,
                    private=str(dst), fixture_products={
                        f.name: paired.fingerprint(f) for f in dst.iterdir()
                        if f.is_file() and f.name not in
                        {Path(i["git_path"]).name for i in inventory}})
                manifest["selections"][side] = selected
                build = paired.execute([str(repo / "bin/Holmake"),
                    "--no-project", "--no-cache", "--no_prereqs",
                    "--holstate=" + str(repo / "bin/hol.state0"),
                    "-C", str(dst), "-j1", "paired.exe"],
                    root, env, args.timeout)
                paired.compact(dict(build), output, side + "-build")
                require(build["exit"] == 0 and not build["timed_out"],
                        side + " private launcher build failed")
                launcher = (dst / "paired.exe").read_text()
                runtime = str(repo / "bin/hol") + " --gcthreads=1 run "
                require(runtime in launcher and
                        "--holstate=" + str(repo / "bin/hol.state0") in launcher,
                        "wrong launcher runtime/heap/options")
                selected["launcher"] = launcher
                for pattern in ("*.exe", ".hol/objs/*", ".hol/make-deps/*"):
                    seals.update({str(f.resolve()): paired.fingerprint(f)
                                  for f in dst.glob(pattern) if f.is_file()})
            private_names = {Path(s["git_path"]).stem
                             for inv in inventories.values() for s in inv}
            bodies = {}
            for side in ("baseline", "candidate"):
                dst = root / side
                runenv = dict(env, PAIR_SELECTION=side,
                    PAIR_FIXTURE="assembly", PAIR_CONTROL="none",
                    PAIR_PRIVATE=str(dst), PAIR_TARGET="selftest",
                    PAIR_OPTIMIZED_TREE=str(args.optimized_tree).lower())
                receipt = paired.execute([str(dst / "paired.exe")], dst,
                                         runenv, args.timeout)
                receipt.update(selection=side, fixture="assembly",
                    accepted=False,
                    environment={k: v for k, v in runenv.items()
                                 if k.startswith("PAIR_")})
                label = side + "-assembly"
                manifest["runs"].append(dict(receipt=label + ".json.gz",
                                            accepted=False))
                try:
                    receipt["result"] = paired.validate(receipt,
                        selection=side, fixture="assembly", control="none",
                        private=dst, repo=repo, private_names=private_names,
                        flavor="baseline", signature="pass",
                        source_hashes=seals,
                        contract=dict(target="selftest", observations=OBS,
                            red=False, modules=["simpLib", "Traverse"],
                            signatures=[]))
                    bodies[side] = extract(receipt["stdout"], dst)
                    exact = output / (side + ".sml-assembly.txt.gz")
                    code = "".join(bodies[side].values()).encode()
                    exact.write_bytes(gzip.compress(code, mtime=0))
                    manifest["selections"][side]["exact_assembly"] = dict(
                        file=exact.name, **paired.fingerprint(exact),
                        uncompressed_sha256=paired.digest(code),
                        uncompressed_bytes=len(code))
                    receipt["emitted_function_names"] = list(bodies[side])
                    if args.optimized_tree:
                        selected_code = extract_compiler(
                            receipt["stdout"], dst)
                        code = (json.dumps(selected_code, indent=2) +
                                "\n").encode()
                        exact = output / (side + ".optimized-tree.json.gz")
                        exact.write_bytes(gzip.compress(code, mtime=0))
                        selected = manifest["selections"][side]
                        selected["optimized_compiler"] = dict(
                            file=exact.name, **paired.fingerprint(exact),
                            uncompressed_sha256=paired.digest(code),
                            uncompressed_bytes=len(code))
                        receipt["selected_compiler_records"] = len(
                            selected_code)
                    for info in receipt["result"]["paths"].values():
                        path = Path(info["physical"])
                        if not path.is_relative_to(root):
                            manifest["shared_products"].setdefault(str(path),
                                {k: info[k] for k in ("sha256", "bytes")})
                            for name, seal in info["related_products"].items():
                                manifest["shared_products"].setdefault(
                                    name, seal)
                    receipt["accepted"] = True
                    manifest["runs"][-1]["accepted"] = True
                    # Keep exact selected bodies once, not the entire simpLib
                    # dump. The full output's byte count/hash remains sealed.
                    receipt["stdout"] = "\n".join(
                        line for line in receipt["stdout"].splitlines()
                        if line.startswith(paired.PREFIX)) + "\n"
                except Exception as exc:
                    receipt["rejection"] = str(exc)
                    raise
                finally:
                    paired.compact(receipt, output, label)
            comparison = compare(bodies["baseline"], bodies["candidate"])
            manifest["comparison"] = comparison
            manifest["unsupported_optional"] = {side: [root for root in HELPERS
                if not any(n.startswith("simpLib." + root + "(")
                           for n in selected)]
                for side, selected in bodies.items()}
            for side, inv in inventories.items():
                if manifest["selections"][side]["reference"] == "worktree":
                    require({str(f.relative_to(repo)) for f in
                             fragments.worktree_sources(repo)} ==
                            {s["git_path"] for s in inv},
                            "worktree source inventory changed during pair")
                    for source in inv:
                        path = repo / source["git_path"]
                        require(paired.fingerprint(path) ==
                                {k: source[k] for k in ("sha256", "bytes")},
                                "worktree source changed during pair")
            for name, seal in seals.items():
                require(paired.fingerprint(Path(name)) == seal,
                        "private input/product changed during pair: " + name)
            for group in ("inputs", "tools", "shared_products"):
                for name, seal in manifest[group].items():
                    require(paired.fingerprint(repo / name) == seal,
                            "input/tool/shared product changed: " + name)
            manifest["collection_validated"] = True
            manifest["strict_equality_accepted"] = all(
                c["identical_after_pool_relocation"]
                for c in comparison.values())
            require(manifest["strict_equality_accepted"],
                    "strict equality rejected: nonrelocation code or "
                    "emission-inventory differences (see comparison)")
        manifest["success"] = True
    except Exception as exc:
        manifest["failure"] = str(exc)
    finally:
        manifest["artifacts"] = {f.name: paired.fingerprint(f)
            for f in sorted(output.iterdir()) if f.is_file() and
            f.name != "manifest.json"}
        (output / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")
    if not manifest["success"]:
        raise SystemExit(manifest["failure"])


if __name__ == "__main__":
    main()
