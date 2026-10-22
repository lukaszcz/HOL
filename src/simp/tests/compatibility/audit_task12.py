#!/usr/bin/env python3
"""Offline TASK_12 source correspondence; never build or rerun timings."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SRC = "src/simp/src/"
BASE = "cccaa27d7099cbadc886983020cbe745db7793f3"
START = "640f5a1cbcb6d38ee08093cf2d007e14f0fb923a"
SNAPSHOT = "06927a63d9796d33d6cc98f936c2cab27f3b66a5"
NAMES = ("Cond_rewr", "SimpTracking", "Cond_rewrExt")
ALIASES = """\
(* Both engines report to the same thread-local tracking extent. *)
val note_rewrite = SimpTracking.note_rewrite
val with_tracking = SimpTracking.with_tracking
"""
EXT_PREFIX = """\
(* Explicit paired compilation. Public mutable controls and exception
   identities belong to the existing shared modules, never copies here. *)
structure Cond_rewrExt :> Cond_rewrExt =
struct
open HolKernel boolLib liteLib Trace

(* Preserve the observable diagnostic origin of the conditional engine. *)
fun WRAP_ERR x = STRUCT_WRAP "Cond_rewr" x
fun ERR x = STRUCT_ERR "Cond_rewr" x
val is_var_perm = Cond_rewr.is_var_perm

type config =
  {solver : term list -> term -> thm, stack : term list,
   cond_depth : int option, term_ord : term * term -> order}
type runners =
  {legacy : (term list -> term -> thm) -> term list -> conv,
   configured : config -> conv}

"""
EXT_SUFFIX = """

(* Binding happens at tracked construction, not at projection. No shadow
   allowance: aliases/conjuncts may deliberately supply the same reference.
   As in the baseline bound wrapper, failures do not spend an allowance. *)
datatype prepared = Prepared of runners
fun prepare nmth control =
  let
    val pair = COND_REWR_CONVS nmth
                 (case control of BoundedRewrites.UNBOUNDED => false
                                | BoundedRewrites.BOUNDED _ => true)
  in
    Prepared
      (case control of
           BoundedRewrites.UNBOUNDED => pair
         | BoundedRewrites.BOUNDED r =>
             {legacy = fn solver => fn stack => fn tm =>
                if !r = 0 then failwith "exceeded rewrite bound"
                else #legacy pair solver stack tm before Portable.dec r,
              configured = fn ctxt => fn tm =>
                if !r = 0 then failwith "exceeded rewrite bound"
                else #configured pair ctxt tm before Portable.dec r})
  end
fun runners (Prepared pair) = pair
end
"""


def require(ok, message):
    if not ok:
        raise ValueError(message)


def git_source(revision, path):
    return subprocess.check_output(
        ["git", "-C", str(REPO), "show", revision + ":" + path])


def seal(data):
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def load(path):
    data = path.read_bytes()
    return json.loads(gzip.decompress(data) if path.suffix == ".gz" else data)


def between(text, start, stop):
    require(text.count(start) == 1 and text.count(stop) == 1,
            "missing/ambiguous source anchors: " + start)
    a, b = text.index(start), text.index(stop)
    require(a < b, "reversed source anchors")
    return text[a:b]


def structural(sources=None):
    if sources is None:
        sources = {n + ext: (REPO / SRC / (n + ext)).read_bytes().decode()
                   for n in NAMES for ext in (".sig", ".sml")}
    original = git_source(BASE, SRC + "Cond_rewr.sml").decode()
    before = git_source(START, SRC + "Cond_rewr.sml").decode()
    tracking = between(original, "(* Which rewrites fired,",
                       "\n(* --------------------------------")
    cond = sources["Cond_rewr.sml"]
    require(cond == original.replace(tracking, ALIASES, 1),
            "Cond_rewr differs beyond the exact tracking-to-alias move")
    require(sources["SimpTracking.sml"] ==
            "structure SimpTracking :> SimpTracking =\nstruct\n"
            "open HolKernel\n\n" + tracking + "end\n",
            "SimpTracking is not the exact original tracking block")
    constructor = "   fun COND_REWR_CONV (nm,th) bounded ="
    stop = "\n\nval BOUNDED_t"
    require(between(cond, constructor, stop) ==
            between(original, constructor, stop),
            "direct constructor/stages/callback bodies changed")

    # The entire old paired implementation, not a list of selected tokens.
    paired = between(before, "   (* Prepare once;", stop)
    adapter = """   fun COND_REWR_CONV nmth bounded =
      #legacy (COND_REWR_CONVS nmth bounded);

"""
    require(paired.count(adapter) == 1, "old direct adapter missing")
    paired = paired.replace(adapter, "", 1)
    for old, new in (("is_var_perm (", "Cond_rewr.is_var_perm ("),
                     ("!stack_limit", "!Cond_rewr.stack_limit"),
                     ("ac_term_ord(", "Cond_rewr.ac_term_ord("),
                     ("then note_rewrite th",
                      "then SimpTracking.note_rewrite th")):
        require(old in paired, "qualification anchor missing: " + old)
        paired = paired.replace(old, new)
    ext = sources["Cond_rewrExt.sml"]
    require(ext == EXT_PREFIX + paired + EXT_SUFFIX,
            "extension bodies/imports/bound wrappers/projection changed")
    require(ext.count("HO_PART_MATCH") == 1 and
            ext.count("val instth =") == 1 and
            ext.count("val conditional_eqn = instth tm") == 2,
            "paired runners must share one lexical instth/matcher")
    require(EXT_SUFFIX.count("COND_REWR_CONVS nmth") == 1 and
            ext.count("fun runners (Prepared pair) = pair") == 1,
            "bind control wrappers once; runners must only project")

    combined = "\n".join(sources[n + ".sml"] for n in NAMES)
    require(len(re.findall(r"\bref\b", combined)) == 1 and
            combined.count("val stack_limit = ref 4;") == 1,
            "stack_limit must be the only ref allocation")
    require(combined.count("ThreadLocal.new") == 1 and
            "ThreadLocal.new ()" in sources["SimpTracking.sml"],
            "tracking slot must have one production owner")
    for name in ("Cond_rewr", "SimpTracking"):
        for suffix in (".sig", ".sml"):
            require(not re.search(r"\b\w*Ext\w*\b", sources[name + suffix]),
                    "extension dependency in " + name + suffix)
    require("val is_var_perm" in sources["Cond_rewr.sig"],
            "legacy public is_var_perm helper removed")

    tracked = (REPO / SRC / "simpExtLib.sml").read_text()
    ordinary = (REPO / SRC / "simpLib.sml").read_text()
    binding = """    val prepared = Cond_rewrExt.prepare (nm,th) tag
    val {legacy,configured} = Cond_rewrExt.runners prepared"""
    require(tracked.count(binding) == 1 and "appconvs" not in tracked,
            "tracked compiler must bind prepared controls once")
    require(ordinary.count(
        "appconvs (Cond_rewrExt.COND_REWR_CONVS (nm,th), tag)") == 1,
        "temporary ordinary mixed compiler import changed")
    return {SRC + name: seal(text.encode())
            for name, text in sources.items()}


def inputs(manifest):
    require(manifest["inputs"], "missing source input seals")
    for path, expected in manifest["inputs"].items():
        require(seal((REPO / path).read_bytes()) == expected,
                "input drift: " + path)


def selections(manifest, control=False):
    require(set(manifest["selections"]) == {"baseline", "candidate"},
            "missing source selection")
    for side, selected in manifest["selections"].items():
        baseline = side == "baseline" or control
        require(selected["revision"] == (BASE if baseline else SNAPSHOT),
                "wrong selected revision: " + side)
        seen = set()
        for source in selected["sources"]:
            path = source["git_path"]
            require(path not in seen, "duplicate selected source")
            seen.add(path)
            data = (git_source(BASE, path) if baseline else
                    (REPO / path).read_bytes())
            require(seal(data) == {k: source[k] for k in ("sha256", "bytes")},
                    "selected source drift: " + side + ":" + path)
        required = {SRC + "Cond_rewr" + s for s in (".sig", ".sml")}
        if not baseline:
            required.update(SRC + n + s for n in NAMES
                            for s in (".sig", ".sml"))
        require(required <= seen, "missing conditional source seals")


def paired_receipts(folder):
    import prior_contracts as prior
    import public_contracts as public

    manifest = load(folder / "manifest.json")
    require(manifest["success"], "paired run failed")
    inputs(manifest)
    selections(manifest)
    reference = manifest["public_contracts"]["references"]["Cond_rewr"]
    require(reference["revision"] == BASE and
            {k: reference[k] for k in ("sha256", "bytes")} ==
            seal(git_source(BASE, SRC + "Cond_rewr.sig")),
            "public signature oracle changed")
    counts = {"PriorOriginal": 73, "PriorTraversal": 47,
              "PriorExclusion": 929, "PriorLimits": 6}
    targets = ("signature", *public.CONTRACTS, *counts)
    for side in ("baseline", "candidate"):
        for target in targets:
            r = load(folder / (side + "-" + target + "-none.json.gz"))
            require(r["selection"] == side and r["fixture"] == target and
                    r["control"] == "none" and r["exit"] == 0 and
                    not r["timed_out"] and r["accepted"] and
                    r["result"]["outcome"] == "pass",
                    "missing/failed executed contract: " + target)
            if target in counts:
                require(r["prior"]["checks"] == counts[target],
                        "wrong prior assertion count: " + target)
                if target != "PriorLimits":
                    require(r["prior"]["stream"] ==
                            prior.historical(HERE, target),
                            "frozen prior observations changed: " + target)
    return dict(original_signature="pass", prior_counts=counts)


def native_receipts(folder):
    import coverage_ledger as coverage
    import task10_relocation as relocation

    manifest = load(folder / "manifest.json")
    require(manifest["success"] and manifest["coverage"] == {
        "frozen_native_checks": 630, "current_native_checks": 642,
        "additional_registry_checks": 12}, "native coverage incomplete")
    inputs(manifest)
    ledger = coverage.receipt(HERE / "coverage-ledger.json.gz")
    supplement = relocation.load()
    coverage.verify(ledger, supplement)
    labels = set()
    for run in manifest["runs"]:
        r = load(folder / run["receipt"])
        label = run["label"]
        require(label not in labels and run["exit"] == r["exit"] == 0 and
                not r["timed_out"] and "FAILED!" not in r["stdout"],
                "failed/duplicate native run: " + label)
        labels.add(label)
        require(seal(r["stdout"].encode()) == {
            "sha256": r["stdout_sha256"], "bytes": r["stdout_bytes"]},
            "native stdout seal mismatch: " + label)
        if "stream" in r:
            relocation.validate_stream(ledger, label, r["stream"], supplement)
    require(labels == {"build-focused", "native", "traversal", "exclusion",
                       "markers", "replay-order", "split-registration",
                       "persistence", *["fresh-" + s for s in
                       ("control", "attribute-first", "set-first",
                        "attribute-after", "set-after", "syntax-first")]},
            "native run inventory incomplete")
    return dict(current_native_checks=642, runs=len(labels))


def performance_receipts(folder, control=False):
    sys.path.insert(0, str(HERE.parent / "performance"))
    from audit_evidence import audit as performance_audit
    from summarize import summarize

    manifest = load(folder / "manifest.json")
    require(manifest["success"] and
            manifest["performance"]["suite"] == "conditional" and
            manifest["performance"]["pairs"] >= 10,
            "conditional timing evidence incomplete")
    inputs(manifest)
    selections(manifest, control)
    count = 0
    for run in manifest["runs"]:
        r = load(folder / run["receipt"])
        if r.get("fixture") == "performance":
            require(run["accepted"], "manifest rejected timing receipt")
            performance_audit(manifest, r)
            count += 1
    require(count == 2 * manifest["performance"]["pairs"],
            "missing conditional timing processes")
    summary = summarize(folder)
    require(summary == load(folder / "summary.json"), "timing summary drift")
    return dict(receipts=count, workloads=list(summary["workloads"]))


def audit(folder=None):
    result = dict(structural="pass", sources=structural(),
                  evidence="not requested; no timing rerun")
    if folder is not None:
        result["evidence"] = {
            "paired": paired_receipts(folder / "paired"),
            "native": native_receipts(folder / "native"),
            "conditional-control": performance_receipts(
                folder / "conditional-control", control=True),
            "conditional-candidate": performance_receipts(
                folder / "conditional-candidate")}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("folder", nargs="?", type=Path)
    parser.add_argument("--evidence", type=Path)
    args = parser.parse_args()
    if args.folder is not None and args.evidence is not None:
        parser.error("choose positional folder or --evidence, not both")
    try:
        print(json.dumps(audit(args.evidence or args.folder), indent=2))
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as e:
        parser.exit(1, "TASK_12 audit failed: " + str(e) + "\n")


if __name__ == "__main__":
    main()
