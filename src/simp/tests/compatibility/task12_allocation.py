#!/usr/bin/env python3
"""Isolated TASK12 graph/assembly inspection, not a timing benchmark."""
import argparse
import gzip
import json
import os
from pathlib import Path
import platform
import re
import shutil
import tempfile

import run_paired as paired

HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "allocation"
CANDIDATE = "HEAD"
SIZES = [0, 1, 8, 64, 256, 1024]
KINDS = ["unconditional", "conditional", "ac"]
STAGES = ["constructor", "solver_bound", "stack_bound", "proof"]


def measurements(text):
    events = paired.parse_events(text)
    observations, graphs = [], {}
    for kind in KINDS + ["cells"]:
        rows = []
        for n in SIZES:
            key = "control.cells" if kind == "cells" else "graph." + kind
            matching = [e for e in events if e[:2] == ["observation", key]
                        and e[2].split(",")[0] == str(n)]
            paired.require(len(matching) == 1, "missing/duplicate graph row")
            row = list(map(int, matching[0][2].split(",")))
            paired.require(len(row) == (2 if kind == "cells" else 5),
                           "wrong graph row arity")
            rows.append(row)
            observations += [matching[0],
                             ["check", kind + " " + str(n), "pass"]]
        # Report all adjacent finite differences, not a fitted slope that
        # could hide a small/nonlinear increase. Fixed intercept is separate.
        slopes = [[(b[j] - a[j]) / (b[0] - a[0])
                   for j in range(1, len(a))]
                  for a, b in zip(rows, rows[1:])]
        graphs[kind] = dict(rows=rows, adjacent_words_per_rule=slopes)
    return observations, graphs


def assembly(text):
    """Read compiler-disassembled AArch64 instructions, not ML object layouts.

    Preserve every function's ordered reservation sites, including cold error
    and tracking paths. This is not a dynamic sum: some sites are exclusive.
    """
    chunks = re.split(r"^([^\n]+):[ \t]*\n", text, flags=re.MULTILINE)
    functions = {}
    for name, body in zip(chunks[1::2], chunks[2::2]):
        if not name.startswith(("Cond_rewr.COND_REWR_CONV(",
                                "SimpTracking.note_rewrite(")):
            continue
        instructions, encodings, sites = [], [], []
        for line in body.splitlines():
            m = re.fullmatch(
                r"([0-9A-F]{6})  ([0-9A-F]{8})[ \t]+(.+?)\s*", line)
            if not m:
                continue
            offset, encoding, instruction = m.groups()
            instructions.append(instruction)
            encodings.append(encoding)
            site = re.fullmatch(r"sub\s+x\d+,x27,#(\d+)", instruction)
            if site:
                sites.append(dict(offset=offset, bytes=int(site[1])))
        paired.require(instructions and any(i.startswith("ldr ")
                       for i in instructions), "missing AArch64 disassembly")
        paired.require(name not in functions, "duplicate assembly function")
        functions[name] = dict(listing_words=len(instructions),
                               encoding_sha256=paired.digest(
                                   "".join(encodings).encode()),
                               reservation_sites=sites,
                               indirect_calls=sum(i.startswith("blr ")
                                                  for i in instructions))
    expected = ["Cond_rewr.COND_REWR_CONV" + s for s in
                ("(3)(1)(1)(1)solver'(1)", "(3)(1)(1)(1)", "(3)(1)(1)",
                 "(3)(1)", "(3)", "(1)(1)", "(1)")]
    paired.require(set(expected) <= set(functions),
                   "missing constructor assembly")
    return functions


def compare(selections):
    a, b = (selections[s]["graphs"] for s in ("baseline", "candidate"))
    deltas = {}
    for kind in KINDS:
        aa, bb = (x[kind]["adjacent_words_per_rule"] for x in (a, b))
        paired.require(all(row == aa[0] for row in aa) and
                       all(row == bb[0] for row in bb), "nonlinear graph slope")
        delta = [y - x for x, y in zip(aa[0], bb[0])]
        paired.require(all(d <= 0 for d in delta), "increased per-rule graph")
        paired.require(delta[-1] == 0, "proof graph changed")
        deltas[kind] = delta
    for g in (a, b):
        paired.require(all(row[1] == 5 * row[0] for row in g["cells"]["rows"]),
                       "positive allocation control failed")
    asm_a, asm_b = (selections[s]["assembly"]
                    for s in ("baseline", "candidate"))
    for name, info in asm_a.items():
        aa = [site["bytes"] for site in info["reservation_sites"]]
        bb = [site["bytes"] for site in asm_b[name]["reservation_sites"]]
        paired.require(len(aa) == len(bb) and
                       all(y <= x for x, y in zip(aa, bb)),
                       "increased generated allocation site: " + name)
        paired.require(info["indirect_calls"] == asm_b[name]["indirect_calls"],
                       "generated call count differs: " + name)
    application = "Cond_rewr.COND_REWR_CONV(3)(1)(1)(1)"
    paired.require(
        [s["bytes"] for s in asm_a[application]["reservation_sites"]] ==
        [s["bytes"] for s in asm_b[application]["reservation_sites"]],
        "application allocation sites differ")
    return dict(candidate_minus_baseline_words_per_rule=deltas,
                no_extra_retained_words_per_rule=True,
                no_extra_native_heap_reservation_sites=True,
                application_reservation_sizes_identical=True,
                byte_identical_machine_code=all(
                    info["encoding_sha256"] == asm_b[n]["encoding_sha256"]
                    for n, info in asm_a.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--baseline", default=paired.BASE)
    parser.add_argument("--candidate", default=CANDIDATE)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    inputs = [Path(__file__), HERE / "run_paired.py", HERE / "audit_task12.py",
              HERE / "test_task12_allocation.py",
              *sorted(FIXTURES.iterdir()),
              *sorted((HERE / "paired").glob("*.sml"))]
    manifest = dict(schema_version=1, success=False,
                    scope="isolated-source retained graph words; not timing, "
                          "RSS, or cumulative allocation",
                    stages=STAGES, selections={}, machine=platform.machine(),
                    inputs={str(p.relative_to(repo)): paired.fingerprint(p)
                            for p in inputs if p.is_file()},
                    tools={n: paired.fingerprint(repo / n) for n in
                           ("bin/hol", "bin/Holmake", "bin/hol.state0")})
    try:
        paired.require(platform.machine() == "aarch64",
                       "native allocation-site parser requires AArch64")
        import audit_task12
        manifest["source_correspondence"] = audit_task12.structural()
        poly = Path(shutil.which("poly")).resolve()
        manifest["poly"] = dict(path=str(poly), **paired.fingerprint(poly))
        manifest["poly_version"] = paired.execute(
            [str(poly), "-v"], repo, env, args.timeout)
        with tempfile.TemporaryDirectory(prefix="task12-allocation-") as tmp:
            root = Path(tmp)
            for side, ref in (("baseline", args.baseline),
                              ("candidate", args.candidate)):
                dst = root / side
                dst.mkdir()
                rev = paired.git(repo, "rev-parse",
                                 ref + "^{commit}").decode().strip()
                inventory = paired.extract(repo, rev, dst)
                if side == "candidate":
                    for source in inventory:
                        path = repo / source["git_path"]
                        paired.require(
                            paired.fingerprint(path) ==
                            {k: source[k] for k in ("sha256", "bytes")},
                            "candidate snapshot/worktree drift: " + str(path))
                paired.install_fixtures(dst)
                for p in FIXTURES.iterdir():
                    if p.is_file():
                        shutil.copyfile(p, dst / p.name)
                sources = {str(p): paired.fingerprint(p) for p in dst.iterdir()
                           if p.is_file()}
                selected = dict(revision=rev, sources=inventory)
                manifest["selections"][side] = selected
                build = paired.execute([
                    str(repo / "bin/Holmake"), "--no-project", "--no-cache",
                    "--no_prereqs",
                    "--holstate=" + str(repo / "bin/hol.state0"),
                    "-C", str(dst), "-j1", "allocation.exe"],
                    root, env, args.timeout)
                paired.compact(dict(build), output, side + "-build")
                paired.require(build["exit"] == 0 and not build["timed_out"],
                               side + " build failed")
                launcher = (dst / "allocation.exe").read_text()
                paired.require(str(repo / "bin/hol") + " --gcthreads=1 run " in
                               launcher and "--holstate=" +
                               str(repo / "bin/hol.state0") in launcher,
                               "wrong launcher/heap/options")
                selected["launcher"] = launcher
                runenv = dict(env, PAIR_SELECTION=side,
                              PAIR_FIXTURE="allocation",
                              PAIR_CONTROL="none", PAIR_PRIVATE=str(dst),
                              PAIR_TARGET="Task12Allocation")
                receipt = paired.execute([str(dst / "allocation.exe")], dst,
                                         runenv, args.timeout)
                # Keep one full log, including raw assembly. Protocol receipts
                # below retain its original stdout hash/size, not a second copy.
                log = output / (side + "-assembly.log.gz")
                log.write_bytes(gzip.compress(
                    receipt["stdout"].encode(), mtime=0))
                selected["full_log"] = dict(name=log.name,
                                            **paired.fingerprint(log))
                expected, graphs = measurements(receipt["stdout"])
                names = {Path(s["git_path"]).stem for s in inventory}
                receipt["result"] = paired.validate(
                    receipt, selection=side, fixture="allocation",
                    control="none", private=dst, repo=repo,
                    private_names=names, flavor="baseline",
                    signature="pass", source_hashes=sources,
                    contract=dict(target="Task12Allocation",
                                  observations=expected,
                                  red=False, modules=["Cond_rewr"],
                                  signatures=["Cond_rewr"]))
                forbidden = {"Traverse", "simpLib"}
                loaded = {Path(p).stem for p in receipt["result"]["paths"]}
                paired.require(
                    not (forbidden & loaded) and
                    not any(n.endswith(("Ext", "ExtLib")) for n in loaded),
                    "non-direct engine dependency")
                for info in receipt["result"]["paths"].values():
                    paired.require(paired.fingerprint(Path(info["physical"])) ==
                                   {k: info[k] for k in ("sha256", "bytes")},
                                   "loaded source changed")
                selected["graphs"] = graphs
                selected["assembly"] = assembly(receipt["stdout"])
                # Assembly already retained once in the full compressed log.
                # Avoid duplicating it as diagnostics in the protocol receipt.
                receipt["stdout"] = "\n".join(
                    line for line in receipt["stdout"].splitlines()
                    if line.startswith(paired.PREFIX)) + "\n"
                paired.compact(receipt, output, side + "-run")
            manifest["comparison"] = compare(manifest["selections"])
            for name, expected in manifest["inputs"].items():
                paired.require(paired.fingerprint(repo / name) == expected,
                               "harness input changed: " + name)
            for name, expected in manifest["tools"].items():
                paired.require(paired.fingerprint(repo / name) == expected,
                               "tool changed: " + name)
        manifest["success"] = True
    except Exception as e:
        manifest["failure"] = str(e)
    finally:
        (output / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")
    if not manifest["success"]:
        raise SystemExit(manifest["failure"])


if __name__ == "__main__":
    main()
