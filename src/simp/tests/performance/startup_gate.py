#!/usr/bin/env python3
"""TASK31 ordinary-startup allocation gate (exact words, TASK29B counter).

Compares ordinary HOL startup, fresh `load "simpLib"` / `load "congLib"`
from hol.state0 and the first simplifier calls of a baseline HOL build and a
candidate HOL build in every counter field. The measuring instrument is the
TASK29B private patched runtime, bracket shim and controls receipt; the
trees are built here by the procedure of `allocator-counter/bootstrap_probe`
(`build_native_hol`), once per tree, never in place.

  build    one native Poly/ML, the private runtime and shim, and any number
           of clean HOL trees (label=rev[+patch]); writes lineage.json
  measure  paired fresh processes, AB/BA, plus a baseline/baseline control
  replay   recomputes every decision from the archive alone

Decision rule (no tolerance, no subtraction, no outlier removal): the gate
passes only if every field of every candidate-minus-baseline pair is exactly
0, the control (an independent clean build of the baseline) is exactly 0 in
every field of every pair, every side is deterministic across its repeats and
no extension module is loaded in any ordinary process. Otherwise it fails and
the delta is published.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
for sub in ("allocator-counter", "../compatibility"):
    sys.path.insert(0, str((HERE / sub).resolve()))
import acceptance as a
import allocation_schema as sc
import loading
import private_runtime as pr
import run_paired as rp
from prepare_patch import DEFAULT_SOURCE

SCHEMA = "task31-startup-gate-v1"
LINEAGE_SCHEMA = "task31-startup-toolchain-v1"
MKTOOL_PATCH = HERE / "startup_gate_mktool.patch"
CLIENT = HERE / "StartupGate.sml"
SNAPSHOT_ABI = 1  # first field of the counter snapshot
PAIRS = 10  # acceptance minimum; fewer pairs is a smoke only
CONFIGURE = ("--without-x", "--disable-compact32bit", "--enable-shared")
# Ordinary clients: process kind -> (heap, what the script brackets).
KINDS = {
    "hol-startup": ("hol.state", ()),
    "hol-first-use": ("hol.state", ("SIMP_CONV", "SIMP_TAC")),
    "load-simpLib": ("hol.state0", ("simpLib", "SIMP_CONV", "SIMP_TAC")),
    "load-congLib": ("hol.state0", ("congLib",)),
}
# Modules and caches that exist only in the extension, and so must be absent
# from every ordinary process (patterns on Meta.loaded module names).
EXTENSION_SUFFIX = "Ext"
EXTENSION_NAMES = ("simpExtLib", "congExtLib", "SimpTracking",
                   "TraverseExt", "Cond_rewrExt", "OpeningExt",
                   "TravrulesExt", "boolSimpsExt", "combinSimpsExt",
                   "pureSimpsExt", "splitLib", "splitPersistLib",
                   "SplitData", "simpMarkerLib", "simpMarkerScript",
                   "trackedSimpDefaults")


def require(ok, message):
    sc.require(ok, message)


def is_extension(module, allowed=()):
    """A module of the extension, unless the baseline has it too."""
    if module in allowed:
        return False
    return module.endswith(EXTENSION_SUFFIX) or module in EXTENSION_NAMES


# ---------------------------------------------------------------- building

def tool_env(tmpdir):
    """The environment of every build command: that of the toolchain
    (`allocation_matrix.toolchain`), HOLDIR added per tree."""
    env = dict(PATH=pr.PATH, HOME="/nonexistent", TMPDIR=str(tmpdir),
               TERM="dumb", LC_ALL="C", TZ="UTC", CONFIG_SITE="/dev/null")
    for key, name in (("CC", "gcc"), ("CXX", "g++")):
        env[key] = shutil.which(name, path=env["PATH"]) or ""
        require(bool(env[key]), "missing compiler: " + name)
    return env


def build_native(pristine, root, run, report):
    """Native Poly/ML from the sealed source (as build_native_hol)."""
    source, prefix = root / "native-source", root / "native-install"
    shutil.copytree(pristine, source)
    pr.verify_source(source)
    run([str(source / "configure"), *CONFIGURE, "--prefix=" + str(prefix)],
        source)
    report["native_configuration"] = (source / "config.h").read_text()
    pr.reject_compact32(report["native_configuration"])
    result = run(["make", "-j2"], source)
    report["native_stages"] = len(result["stdout"].splitlines())
    run(["make", "install"], source)
    report["native_products"] = {
        str(p): a.seal(p) for p in prefix.rglob("*") if p.is_file()}
    return prefix


def build_hol(repo, rev, hol, prefix, env, run, report, patch=None):
    """A fresh HOL tree: shared clone at rev (plus a recorded patch file),
    the configuration override, smart-configure and a no-cache build
    (the commands of build_native_hol; HOME, include override included)."""
    head = a.git(repo, "rev-parse", rev + "^{commit}")
    run(["git", "clone", "--shared", "--no-checkout", str(repo), str(hol)],
        repo)
    run(["git", "checkout", "--detach", head], hol)
    if patch is not None:
        run(["git", "apply", "--check", str(patch)], hol)
        run(["git", "apply", str(patch)], hol)
    require(not (hol / "bin/hol.state0").exists(), "prebuilt HOL image")
    env = dict(env, HOLDIR=str(hol))
    report.update(hol_snapshot=head,
                  hol_patch=None if patch is None else a.seal(patch),
                  hol_tree=a.git(hol, "rev-parse", "HEAD^{tree}"))
    overrides = hol / "tools-poly/poly-includes.ML"
    overrides.write_text(
        'val poly = ' + json.dumps(str(prefix / "bin/poly")) + ';\n' +
        'val polymllibdir = ' + json.dumps(str(prefix / "lib")) + ';\n')
    report["hol_configuration_override"] = overrides.read_text()
    run([str(prefix / "bin/poly"), "--error-exit", "--use",
         "tools/smart-configure.sml"], hol, env)
    run([str(hol / "bin/build"), "--no-cache", "-j2",
         "--seq=" + pr.HOL_SEQUENCE], hol, env)
    report["hol_products"] = {str(hol / n): a.seal(hol / n) for n in (
        "bin/hol", "bin/hol.state0", "bin/hol.state", "bin/Holmake")}
    report["hol_state_bytes"] = (hol / "bin/hol.state").stat().st_size
    return head


def split_tree(spec):
    """label=rev[+patchfile] -> (label, rev, patch or None)."""
    label, _, rest = spec.partition("=")
    rev, _, patch = rest.partition("+")
    require(label.isalnum() and rev, "bad tree spec: " + spec)
    return label, rev, (Path(patch).resolve(strict=True) if patch else None)


def build(args):
    pr.use_fixed_path()
    repo = args.repo.resolve(strict=True)
    root = args.toolchain.resolve()
    env = tool_env(args.tmpdir)
    require(platform.machine() == "aarch64", "unsupported host")
    report = dict(schema=LINEAGE_SCHEMA, environment=env, commands=[],
                  trees={}, success=False)
    with a.serial_lock(repo) as fds:
        def run(command, cwd=None, runtime_env=None):
            command_env, cwd = runtime_env, cwd or root
            started = time.time()
            receipt = loading.execute(command, cwd, command_env or env,
                                      args.timeout, fds)
            row = dict(command=receipt["command"], cwd=str(cwd),
                       exit=receipt["exit"],
                       wall=round(time.time() - started, 1),
                       tail=receipt["stdout"][-400:])
            if command_env:
                row["HOLDIR"] = command_env.get("HOLDIR")
            report["commands"].append(row)
            print("RUN", row["exit"], row["wall"], " ".join(row["command"]),
                  flush=True)
            require(receipt["exit"] == 0 and not receipt["timed_out"],
                    "failed command: " + str(command))
            return receipt
        root.mkdir(parents=True, exist_ok=False)
        try:
            if args.reuse:
                # More trees under another root (HOLDIR length sweeps) on
                # the native compiler, runtime and shim of a toolchain.
                old = a.load(args.reuse.resolve(strict=True) /
                             "lineage.json")
                require(old["success"] is True, "reused toolchain failed")
                prefix = args.reuse.resolve() / "native-install"
                lib = Path(old["library"])
                loading.check_seals({old["library"]: old["runtime"],
                                     old["shim"]: old["shim_seal"]})
                for key in ("runtime", "native_configuration", "library",
                            "shim", "shim_seal", "shim_libraries"):
                    report[key] = old[key]
                report["reused"] = str(args.reuse)
                run_env = dict(env, LD_LIBRARY_PATH=str(lib.parent))
            else:
                patched = pr.verify_source(args.source)
                prefix = build_native(args.source, root, run, report)
                lib, _, _ = pr.build_runtime(args.source, root, run, report,
                                             patched)
                fixture = root / "fixture"
                fixture.mkdir()
                run_env = dict(env, LD_LIBRARY_PATH=str(lib.parent))
                shim, report["shim_libraries"] = pr.build_shim(
                    env, run, fixture, lib, run_env, report)
                report.update(library=str(lib.resolve()), shim=str(shim),
                              shim_seal=a.seal(shim))
            for spec in args.tree:
                label, rev, patch = split_tree(spec)
                hol = root / label / "hol-source"
                hol.parent.mkdir()
                tree = report["trees"][label] = dict(rev=rev, hol=str(hol))
                tree["head"] = build_hol(repo, rev, hol, prefix, env, run,
                                         tree, patch)
                tree["libraries"] = pr.bind_runtime(
                    run, hol, lib.resolve(), run_env,
                    dict(runtime=report["runtime"]))
            report["success"] = True
        finally:
            name = "lineage.json" if report["success"] else \
                "lineage-failed.json"
            (root / name).write_text(json.dumps(report, indent=1))
    return 0



# --------------------------------------------------------------- measuring

OUT_FIELDS = sc.COUNTS + ("heap",)
ATTRIBUTION = ("files-simpLib",)
KINDS["files-simpLib"] = ("hol.state0", ("simpLib",))
USES_SIMP = ("hol-first-use", "load-simpLib")
EXPERIMENTS = (("candidate", "base", "candidate"),
               ("control", "base", "control"),
               ("repeat", "candidate", "repeat"))


def holstate_args(hol, kind):
    heap = KINDS[kind][0]
    return [] if heap == "hol.state" else \
        ["--holstate=" + str(Path(hol) / "bin" / heap)]


def command(hol, kind, client):
    return [str(Path(hol) / "bin/hol"), "--gcthreads=1", "run",
            *holstate_args(hol, kind), str(client)]


def numbers(text, count):
    parts = text.split(",")
    require(len(parts) == count and all(
        p.isdigit() and (p == "0" or not p.startswith("0")) for p in parts),
        "malformed counter fields: " + text)
    return [int(p) for p in parts]


def parse_process(stdout, kind, holdir, library, aliases):
    """The record of one client process, strictly; no value is repaired."""
    require(stdout.endswith("@@GATE\tend\n"), "client did not finish")
    rows = [l.split("\t") for l in stdout.splitlines()
            if l.startswith("@@GATE\t")]
    record = dict(kind=kind, brackets=[], loaded=None, files=None)
    for row in rows[:-1]:
        require(len(row) == 5 and row[1] == kind, "malformed row: %r" % row)
        _, _, event, name, payload = row
        if event == "alloc":
            start, end = payload.split(";")
            record["brackets"].append(dict(
                name=name.replace(holdir, "$HOLDIR"),
                start=numbers(start, 8), end=numbers(end, 8)))
        elif event == "foreign":
            require(payload == sc.FOREIGN, "foreign-thread entries")
        elif event == "holdir":
            require(payload == holdir, "wrong HOLDIR: " + payload)
        elif event == "result":
            record["result"] = payload
        elif event in ("loaded", "files", "structures"):
            if name == "count":
                record[event + "_count"] = int(payload)
            else:
                names = payload.split(",") if payload else []
                require(len(names) == record[event + "_count"],
                        event + " count mismatch")
                record[event] = names
        else:
            require(False, "unknown event " + event)
    for key in ("loaded", "files", "structures", "result"):
        require(record.get(key) is not None, "missing " + key)
    require(record["brackets"][0]["name"] == "startup" and
            record["brackets"][1]["name"] == "empty",
            "first brackets are not startup and empty")
    for b in record["brackets"]:
        for snap in (b["start"], b["end"]):
            require(snap[:3] == [SNAPSHOT_ABI, sc.WORD_BYTES, 0],
                    "counter ABI, word size or overflow: %r" % snap[:3])
    sc.check_runtime(stdout, str(library), aliases)
    record["files_sha"] = sha(record["files"])
    return record


def bracket_fields(bracket):
    """The words of one bracket in every counter field (startup: absolute
    at the first probe, as TASK29B), as a dict."""
    return sc.deltas(dict(
        name="startup" if bracket["name"] == "startup" else bracket["name"],
        start=dict(zip(sc.FIELDS, bracket["start"])),
        end=dict(zip(sc.FIELDS, bracket["end"]))))


def signature(record):
    return tuple((b["name"], tuple(bracket_fields(b)[k] for k in OUT_FIELDS))
                 for b in record["brackets"])


def sha(names):
    return hashlib.sha256("\n".join(names).encode()).hexdigest()


def compare(left, right):
    """right minus left, by bracket name in the union (a bracket missing on
    a side has no value there): {name: {field: delta or None}}."""
    a_sig, b_sig = dict(signature(left)), dict(signature(right))
    out = {}
    for name in list(a_sig) + [n for n in b_sig if n not in a_sig]:
        l, r = a_sig.get(name), b_sig.get(name)
        out[name] = {k: (None if l is None or r is None else r[i] - l[i])
                     for i, k in enumerate(OUT_FIELDS)}
    return out


def nonzero(table):
    return {n: {k: v for k, v in row.items() if v != 0}
            for n, row in table.items()
            if any(v != 0 for v in row.values())}


def setdiff(left, right):
    return dict(only_left=sorted(set(left) - set(right)),
                only_right=sorted(set(right) - set(left)))


def analyse(records, pairs):
    """Every decision of one run from its process records alone.

    records: dicts with kind, side (base/candidate/control/repeat), pair,
    plus the parsed fields. Exact: pass needs every field of every pair of
    every gated kind to be 0, the control to be 0, every side to be
    deterministic and no extension module or structure in any process."""
    reasons, report = [], {}
    kinds = sorted({r["kind"] for r in records})
    by = {}
    for r in records:
        by.setdefault((r["kind"], r["side"]), []).append(r)
    determinism = {}
    for (kind, side), rs in sorted(by.items()):
        sigs = {signature(r) for r in rs}
        loaded = {(tuple(r["loaded"]), r["files_sha"]) for r in rs}
        determinism["%s/%s" % (kind, side)] = dict(
            runs=len(rs), distinct=len(sigs))
        if len(sigs) != 1 or len(loaded) != 1:
            reasons.append("nondeterministic: %s %s (%d distinct)" % (
                kind, side, len(sigs)))
    report["determinism"] = determinism
    experiments = {}
    for name, left, right in EXPERIMENTS:
        exp = experiments[name] = dict(left=left, right=right, kinds={})
        for kind in kinds:
            ls = sorted(by.get((kind, left), []), key=lambda r: r["pair"])
            rs = sorted(by.get((kind, right), []), key=lambda r: r["pair"])
            if not ls and not rs:
                continue
            ok = [l["pair"] for l in ls] == [r["pair"] for r in rs]
            require(ok, "unpaired processes: %s %s" % (name, kind))
            tables = [compare(l, r) for l, r in zip(ls, rs)]
            bad = [nonzero(t) for t in tables]
            row = dict(pairs=len(ls), nonzero_pairs=sum(map(bool, bad)),
                       first=tables[0], first_nonzero=next(
                           (b for b in bad if b), {}))
            row["distinct_tables"] = len({json.dumps(t, sort_keys=True)
                                          for t in tables})
            exp["kinds"][kind] = row
            if kind in ATTRIBUTION:
                continue
            if any(b for b in bad):
                reasons.append("%s %s: non-zero delta in %d of %d pairs"
                               % (name, kind, sum(map(bool, bad)), len(ls)))
            if any(any(v is None for v in t_row.values())
                   for t in tables for t_row in t.values()):
                reasons.append("%s %s: brackets differ" % (name, kind))
    report["experiments"] = experiments
    # Extension modules, structures and caches must be absent everywhere.
    extension = {}
    for kind in kinds:
        base = by.get((kind, "base"), [])
        allowed_m = set(base[0]["loaded"]) if base else set()
        allowed_s = set(base[0]["structures"]) if base else set()
        for side in ("base", "candidate", "control", "repeat"):
            for r in by.get((kind, side), [])[:1]:
                found = sorted(
                    [m for m in r["loaded"] if is_extension(m, allowed_m)] +
                    [s for s in r["structures"]
                     if is_extension(s, allowed_s)])
                extension["%s/%s" % (kind, side)] = found
                if found:
                    reasons.append("extension in ordinary process %s %s: %s"
                                   % (kind, side, ", ".join(found)))
    report["extension"] = extension
    diffs = {}
    for kind in kinds:
        base, cand = by.get((kind, "base"), []), by.get((kind, "candidate"),
                                                       [])
        if base and cand:
            diffs[kind] = dict(
                modules=setdiff(base[0]["loaded"], cand[0]["loaded"]),
                files=setdiff(base[0]["files"], cand[0]["files"]),
                structures=setdiff(base[0]["structures"],
                                   cand[0]["structures"]))
    report["loaded_diff"] = diffs
    for r in records:
        want = "true" if r["kind"] in USES_SIMP else "none"
        if r["kind"] not in ATTRIBUTION and r["result"] != want:
            reasons.append("wrong simplifier result: %s %s" % (
                r["kind"], r["side"]))
    counts = {len({r["pair"] for r in rs}) for rs in by.values()}
    report["acceptance_pairs"] = min(counts) >= PAIRS
    report["decision"] = "pass" if not reasons else "fail"
    if not reasons and not report["acceptance_pairs"]:
        report["decision"] = "smoke"
    report["reasons"] = sorted(set(reasons))
    return report


def render(report, header):
    """RESULTS.md: the figures of every bracket, base/candidate/control."""
    lines = ["# TASK31 ordinary-startup allocation gate", "",
             "Decision: **%s**" % report["decision"], ""]
    for reason in report["reasons"]:
        lines.append("- " + reason)
    lines += ["", "Words, first pair (candidate - base; control = base "
              "copy - base):", "",
              "| process | bracket | field | cand-base | control-base |",
              "|---|---|---|---:|---:|"]
    exp = report["experiments"]
    for kind, row in exp["candidate"]["kinds"].items():
        control = exp["control"]["kinds"].get(kind, {}).get("first", {})
        for name, fields in row["first"].items():
            if kind in ATTRIBUTION and not any(fields.values()):
                continue
            for k, v in fields.items():
                lines.append("| %s | %s | %s | %s | %s |" % (
                    kind, name, k, v, control.get(name, {}).get(k)))
    lines += ["", "Determinism (distinct signatures over the runs of a "
              "side): " + json.dumps(report["determinism"], sort_keys=True)]
    return "\n".join(lines) + "\n"


def harness_state(root):
    """The harness checkout: clean and committed, with the blob of every
    file of the gate and of the instrument it uses."""
    root = Path(root).resolve(strict=True)
    head = a.git(root, "rev-parse", "HEAD")
    identity = pr.harness_identity(root, head)
    files = sorted(set(pr.harness_inputs()) | {
        HERE / n for n in ("startup_gate.py", "StartupGate.sml",
                           "StartupGateUse.sml", "startup_gate_mktool.patch",
                           "allocation_matrix.py")})
    blobs = {}
    for path in files:
        rel = Path(path).resolve(strict=True).relative_to(root).as_posix()
        blobs[rel] = a.git(root, "hash-object", rel)
        require(a.git(root, "rev-parse", "HEAD:" + rel) == blobs[rel],
                "harness file differs from its commit: " + rel)
    return dict(identity, blobs=blobs)


def process_env(base, hol, lib, shim, tmpdir, kind):
    return dict(base, HOLDIR=str(hol), LD_LIBRARY_PATH=str(lib.parent),
                TASK29_ALLOC_SHIM=str(shim), GATE_KIND=kind,
                GATE_USE=str(HERE / "StartupGateUse.sml"), TMPDIR=str(tmpdir))


def measure(args):
    import allocation_matrix as am
    pr.use_fixed_path()
    repo = args.repo.resolve(strict=True)
    root = args.toolchain.resolve(strict=True)
    lineage = a.load(root / "lineage.json")
    require(lineage.get("schema") == LINEAGE_SCHEMA and
            lineage.get("success") is True, "toolchain not built")
    labels = dict(base=args.base, candidate=args.candidate,
                  control=args.control, repeat=args.repeat)
    trees = {side: lineage["trees"][label] for side, label in labels.items()}
    require(len({len(t["hol"]) for t in trees.values()}) == 1,
            "HOLDIR lengths differ between sides")
    lib, shim = Path(lineage["library"]), Path(lineage["shim"])
    aliases = sorted(str(p) for p in lib.parent.iterdir()
                     if p.name.startswith("libpolyml.so") and
                     p.resolve(strict=True) == lib and p != lib)
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    env = tool_env(args.tmpdir)
    harness = harness_state(HERE.parents[3])
    seals = {str(lib): lineage["runtime"], str(shim): lineage["shim_seal"]}
    for tree in trees.values():
        seals.update(tree["hol_products"])
    records, started = [], time.time()
    with a.serial_lock(repo) as fds:
        loading.check_seals(seals)
        tree_hash = pr.tree_outside_performance(
            HERE.parents[3], harness["head"])
        any_tree = next(iter(trees.values()))
        controls = am.controls_receipt(
            args.controls_receipt, lineage["runtime"], tree_hash,
            any_tree["libraries"], lineage["native_configuration"])
        work = args.work
        work.mkdir(parents=True, exist_ok=True)
        position = 0
        for kind in args.kinds:
            for pair in range(args.pairs):
                for name, left, right in EXPERIMENTS:
                    order = (left, right) if pair % 2 == 0 else (right, left)
                    for side in order:
                        position += 1
                        tree = trees[side]
                        penv = process_env(env, tree["hol"], lib, shim,
                                           args.tmpdir, kind)
                        receipt = loading.execute(
                            command(tree["hol"], kind, CLIENT),
                            work, penv, args.timeout, fds)
                        require(receipt["exit"] == 0 and
                                not receipt["timed_out"],
                                "client failed: %s %s\n%s" % (
                                    kind, side, receipt["stdout"][-600:]))
                        rec = parse_process(receipt["stdout"], kind,
                                            tree["hol"], lib, aliases)
                        rec.update(side=side, pair=pair, experiment=name,
                                   position=position, label=labels[side],
                                   wall=round(receipt["process_wall"], 2),
                                   stdout_sha256=receipt["stdout_sha256"])
                        if pair:
                            rec["files"] = None
                        records.append(rec)
                        print(kind, pair, side, rec["brackets"][0]["end"][3],
                              flush=True)
        loading.check_seals(seals)
    header = dict(
        schema=SCHEMA, labels=labels, hol={s: t["hol"] for s, t in
                                           trees.items()},
        trees={s: dict(rev=t["rev"], head=t["head"], tree=t["hol_tree"],
                       patch=t["hol_patch"]) for s, t in trees.items()},
        tmpdir=str(args.tmpdir), tmpdir_length=len(str(args.tmpdir)),
        holdir_length=len(next(iter(trees.values()))["hol"]),
        library=str(lib), runtime=lineage["runtime"],
        shim=lineage["shim_seal"],
        controls=controls, harness=harness, pairs=args.pairs,
        kinds=list(args.kinds), environment={k: v for k, v in env.items()},
        seconds=round(time.time() - started, 1))
    report = analyse(records, args.pairs)
    (out / "records.json.gz").write_bytes(am.compact(records))
    (out / "header.json").write_text(json.dumps(header, indent=1))
    (out / "decisions.json").write_text(json.dumps(report, indent=1))
    (out / "RESULTS.md").write_text(render(report, header))
    print("DECISION", report["decision"], *report["reasons"], sep="\n  ")
    return 0 if report["decision"] == "pass" else 1


def replay(args):
    import allocation_matrix as am
    records = a.load(args.output / "records.json.gz")
    header = a.load(args.output / "header.json")
    report = analyse(records, header["pairs"])
    stored = a.load(args.output / "decisions.json")
    require(json.loads(json.dumps(report)) == stored,
            "stored decisions differ from a replay")
    require((args.output / "RESULTS.md").read_text() ==
            render(report, header), "RESULTS.md differs from a replay")
    print("replayed", report["decision"])
    return 0


# ----------------------------------------------------- TASK29B cell replica

def cell_startup(args):
    """The TASK29B startup bracket of `base` and `candidate` revisions as
    the matrix measures it (sources compiled by `use` in a fresh process
    over one hol.state0, equal-length selection directories), repeated
    under chosen path lengths: the delta and the absolute words as a
    function of TMPDIR, HOLDIR, runtime and shim path lengths. Prints one
    JSON line per measurement."""
    import allocation_matrix as am
    import shutil
    import tempfile
    pr.use_fixed_path()
    repo = args.repo.resolve(strict=True)
    lineage = a.load(args.toolchain.resolve(strict=True) / "lineage.json")
    hol = Path(lineage["trees"][args.tree]["hol"])
    lib = Path(lineage["library"])
    env = tool_env(args.tmpdir)
    env["HOLDIR"] = str(hol)
    lib_dir = Path(args.lib_alias) if args.lib_alias else lib.parent
    shim = Path(args.shim_copy) if args.shim_copy else Path(lineage["shim"])
    if args.shim_copy:
        shutil.copyfile(lineage["shim"], shim)
    run_env = dict(env, LD_LIBRARY_PATH=str(lib_dir))
    revs = {"base": args.baseline, "cand": args.candidate}
    out = []
    with a.serial_lock(repo) as fds:
        scratch = Path(tempfile.mkdtemp(prefix="task29b-",
                                        dir=args.tmpdir)).resolve()
        job = scratch / "j00"
        job.mkdir()
        dirs = {}
        try:
            for side, name in (("base", "sel-b0"), ("cand", "sel-c0")):
                d = job / name
                d.mkdir()
                rp.extract(repo, revs[side], d)
                rp.install_fixtures(d)
                for fx in am.FIXTURES:
                    target = "Performance.sml" if fx == am.FIXTURES[0] \
                        else fx
                    shutil.copyfile(am.HERE / fx, d / target)
                with (d / "Holmakefile").open("a") as f:
                    f.write("\npaired.exe: Performance.uo\n")
                receipt = loading.execute(
                    [str(hol / "bin/Holmake"), "--no-project", "--no-cache",
                     "--no_prereqs", "--holstate=" +
                     str(hol / "bin/hol.state0"), "-C", str(d), "-j1",
                     "paired.exe"], job, env, args.timeout, fds)
                require(receipt["exit"] == 0, "Holmake failed: " +
                        receipt["stdout"][-500:])
                dirs[side] = (d, name)
            for rep in range(args.n):
                for side in (("base", "cand") if rep % 2 == 0
                             else ("cand", "base")):
                    d, name = dirs[side]
                    penv = dict(run_env, PAIR_SELECTION=name,
                                PAIR_FIXTURE="performance",
                                PAIR_CONTROL="none", PAIR_PRIVATE=str(d),
                                PAIR_TARGET="Performance",
                                PERF_CASE="exclude_empty", PERF_SIZE="1000",
                                ALLOC_STEADY="16", ALLOC_REPEATS="4",
                                TASK29_ALLOC_SHIM=str(shim))
                    r = loading.execute([str(d / "paired.exe")], d, penv,
                                        args.timeout, fds)
                    require(r["exit"] == 0, "cell failed: " +
                            r["stdout"][-500:])
                    start = [l.split("\t") for l in r["stdout"].splitlines()
                             if l.startswith("@@PAIR\t")]
                    row = [f for f in start if len(f) > 4 and
                           f[2] == "observation" and f[3] == "alloc.startup"]
                    require(len(row) == 1, "no startup observation")
                    words = [int(x) for x in row[0][4].split(";")[1]
                             .split(",")]
                    out.append(dict(side=side, rep=rep, startup=words[3:]))
        finally:
            shutil.rmtree(scratch, ignore_errors=True)
    base = {tuple(o["startup"]) for o in out if o["side"] == "base"}
    cand = {tuple(o["startup"]) for o in out if o["side"] == "cand"}
    require(len(base) == 1 and len(cand) == 1, "nondeterministic startup")
    b, c = base.pop(), cand.pop()
    result = dict(
        lengths=dict(tmpdir=len(str(args.tmpdir)), holdir=len(str(hol)),
                     library=len(str(lib_dir)) +
                     len("/libpolyml.so.16.0.0"), shim=len(str(shim)),
                     private=len(str(dirs["cand"][0]))),
        base=list(b), cand=list(c), delta=[y - x for x, y in zip(b, c)],
        revs=revs, runs=len(out))
    print(json.dumps(result))
    return 0


def main(argv=None):
    pr.use_fixed_path()
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    b = sub.add_parser("build")
    b.add_argument("--toolchain", type=Path, required=True)
    b.add_argument("--repo", type=Path, default=HERE.parents[3])
    b.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    b.add_argument("--tmpdir", type=Path, required=True)
    b.add_argument("--reuse", type=Path, default=None,
                   help="existing toolchain: build only the trees")
    b.add_argument("--timeout", type=int, default=3600)
    b.add_argument("--tree", action="append", default=[],
                   help="label=rev[+patch]; one clean build each")
    m = sub.add_parser("measure")
    m.add_argument("--toolchain", type=Path, required=True)
    m.add_argument("--repo", type=Path, default=HERE.parents[3])
    m.add_argument("--output", type=Path, required=True)
    m.add_argument("--work", type=Path, required=True)
    m.add_argument("--tmpdir", type=Path, required=True)
    m.add_argument("--controls-receipt", type=Path, required=True)
    m.add_argument("--base", required=True, help="label of the baseline")
    m.add_argument("--candidate", required=True)
    m.add_argument("--control", required=True,
                   help="independent clean build of the baseline")
    m.add_argument("--repeat", required=True,
                   help="independent clean build of the candidate")
    m.add_argument("--pairs", type=int, default=PAIRS)
    m.add_argument("--kinds", nargs="+", default=list(KINDS),
                   choices=list(KINDS))
    m.add_argument("--timeout", type=int, default=1800)
    c = sub.add_parser("cell")
    c.add_argument("--toolchain", type=Path, required=True)
    c.add_argument("--tree", required=True, help="label of the HOL tree")
    c.add_argument("--repo", type=Path, default=HERE.parents[3])
    c.add_argument("--tmpdir", type=Path, required=True)
    c.add_argument("--baseline", default=a.BASE)
    c.add_argument("--candidate", required=True)
    c.add_argument("--lib-alias", default=None,
                   help="symlink to the runtime directory (path length)")
    c.add_argument("--shim-copy", default=None,
                   help="copy of the shim at this path (path length)")
    c.add_argument("-n", type=int, default=2)
    c.add_argument("--timeout", type=int, default=3600)
    r = sub.add_parser("replay")
    r.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    return {"build": build, "measure": measure, "replay": replay,
            "cell": cell_startup}[args.action](args)


if __name__ == "__main__":
    sys.exit(main())
