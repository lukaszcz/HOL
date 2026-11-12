#!/usr/bin/env python3
"""TASK33 storage and release driver (slice S4): the stages that measure
what a fresh process holds (cases L1, L3, S1, S2, S3, R1, E1, E2) with the
probes of task33/ on the two TASK32 snapshots, and the commands around them.

  smoke      every unit once per side (`ext`: candidate only), at small
             sizes and M: the harness works (digests, reporter registered,
             heap facts); information run
  pilot      base only: 3 `graph` and 3 `release` processes at the decision
             sizes and a pilot M0: repeatability and the noise that sizes M
             (required M, clamped to M_CAP, `required`/`capped`);
             information run
  control    the negative controls at the decision configuration (sizes and
             M of the pilot): T33_GRAPH_EXTRA, T33_LEAK and T33_HOOK, each
             against its plain unit on the base snapshot, must fail S1, R1
             and L3; an extension-loading "ordinary" process must be
             refused; information run
  run        the decision stage: `registry` of the five kinds, `graph` and
             `release` (k = 3 processes per side, order B C C B B C), `ext`
             (3, candidate only); L1, L3, S1, S2, R1, E1 and E2 decided,
             S3 reported, S4 reported unsupported
  extend     the contingency: 10 aligned pairs (`paired_statistics` at zero
             margin) for the units a `run` owes (a value not repeatable
             within a side)
  followup   the contingency: R1 / E2 (b) at a larger M, for the units a
             stage owes (resolution not reached), counts committed alone
  audit      `src/simp/tests/api-audit/run.py` in the candidate snapshot:
             8 PASS, its receipt sealed under the stage's output
  predeclare task33_storage_counts.json (or, with --followup, the
             follow-up's) from the replayed smoke, pilot and control, bound
             to the committed timing counts
  replay     recompute every decision of finished runs from their archives
             (no process runs)
  dispose    one disposition.json: the timing disposition, the offline
             reports and these stages' decisions, one per case and kind
  dispose-snapshots
             remove the snapshots after the last use (design section 5)

The processes, locking, ledger, receipts and their checks are the timing
driver's (task32_downstream.py, the `task33` table of it; its `run_stage`,
`launch_probe`, `check_info_run`, `check_ledger`, ...): this file adds the
units, plans, rules (task33_rules.py) and replay of the storage stages; its
ledger table is `task33-storage` (same attempts.jsonl as the loading
driver). Exit status as the timing driver's: 0 pass, 1 fail, 2
inconclusive or blocked, 3 refused or a usage error, 4 a signal.
"""
import argparse
import contextlib
import json
import math
import os
from pathlib import Path
import shlex
import statistics
import sys
from fractions import Fraction

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import loading
import task32_downstream as d
import task33_cases as cases33
import task33_offline as offline
import task33_records as records
import task33_rules as rules

SCHEMA = "task33-storage-v1"
COUNTS_SCHEMA = "task33-storage-counts-v1"
TABLE = "task33"  # the table of the driver this file drives
LEDGER_TABLE = "task33-storage"
STORAGE_COUNTS = HERE / "task33_storage_counts.json"
FOLLOWUP_COUNTS = HERE / "task33_storage_followup_counts.json"
SEED = "task33-s4"
DECISIVE = ("run", "extend", "followup", "audit")
INFO = d.INFO_MODES
K = 3  # fresh processes per side of an exact kind
EXTEND_PAIRS = rules.EXTEND_PAIRS
SMOKE_SIZES = (0, 1, 10)
SMOKE_M = 50
M0 = 200  # the pilot's release size
M_CAP = 5000  # the most objects per release cycle of the decision runs
M_CAP_FOLLOWUP = 40000
FOLLOWUP_FACTOR = 4
MAX_REDRAWS = 3
SCRATCH_ROOT = Path("/dev/shm/t33")
AUDIT_CASES = 8

REGISTRY = tuple("registry-" + k for k in records.LOAD_KINDS)
TRIVIAL = tuple("trivial-" + k for k in records.STARTUP_KINDS)
GRAPH, RELEASE, EXT = "graph", "release", "ext"
UNITS = REGISTRY + TRIVIAL + (GRAPH, RELEASE, EXT)
CAND_ONLY = (EXT,)
# (switch, the plain unit it is a control of)
CONTROLS = (("graph_extra", GRAPH), ("leak", RELEASE),
            ("hook", "registry-state-empty"))
ORDINARY = "ext+ordinary"  # the extension probe, not declared as such
PILOT_UNITS = (GRAPH, RELEASE)
SEEDS = {s: "%s-%s" % (SEED, s) for s in (
    "smoke", "pilot", "control", "run", "extend", "followup", "audit")}
RESOLVED = frozenset((rules.PASS, rules.FAIL))


def require(ok, message):
    d.require(ok, message)


# ------------------------------------------------------------------ units

def sizes_text(sizes):
    return ",".join(str(n) for n in sizes)


def unit_of(name, params):
    """The unit (the dict `task32_downstream.launch_probe` takes) of a
    storage unit name, for the parameters `params` (`sizes`, `m`)."""
    sizes, m = list(params["sizes"]), params["m"]
    if name in REGISTRY:
        kind = name[len("registry-"):]
        return dict(cases33.BY_NAME[kind], name=name, probe="T33Registry")
    if name in TRIVIAL:
        kind = name[len("trivial-"):]
        return dict(cases33.BY_NAME[kind], name=name, probe="T33Trivial",
                    loads=(), min_checks=0)
    heap = cases33.STATE
    base = dict(kind="probe", dir=None, theory=None, heap=heap, serial=1.0,
                area="storage", loads=None)
    if name == GRAPH:
        return dict(base, name=name, probe="T33Graph", min_checks=len(
            records.GRAPH_CHECKS) * len(sizes),
            env=dict(T33_KIND="graph", T33_SIZES=sizes_text(sizes)))
    if name == RELEASE:
        return dict(base, name=name, probe="T33Release", min_checks=0,
                    env=dict(T33_KIND="release", T33_M=str(m)))
    if name in (EXT, ORDINARY):
        return dict(base, name=name, probe="T33Ext", extension=name == EXT,
                    min_checks=len(records.EXT_CHECKS) + len(
                        records.GRAPH_CHECKS) * len(sizes),
                    env=dict(T33_KIND="ext", T33_M=str(m),
                             T33_SIZES=sizes_text(sizes)))
    if "+" in name:
        plain, switch = name.split("+")
        return cases33.control_unit(unit_of(plain, params), switch)
    raise d.Refusal("unknown storage unit " + name)


def control_names():
    return [n for sw, u in CONTROLS for n in (u, u + "+" + sw)] + [ORDINARY]


def probe_modules(report, side):
    """The probe modules a side's processes of the report need. A side
    with no process (the pilot and the follow-ups measure the baseline
    alone) still builds the probes of the plain units: the build is part
    of the process's environment and is checked on both sides."""
    items = [i for i in report["plan"] if i["side"] == side] or [
        i for i in report["plan"] if i["unit"] not in CAND_ONLY]
    return sorted({report["units"][i["unit"]]["probe"] for i in items})


# ------------------------------------------------------------------ plans

def item(unit, side, pair, selection, expect=None):
    return dict(unit=unit, side=side, pair=pair, selection=selection,
                expect=expect)


def side_of(selection):
    return "cand" if selection == "candidate" else "base"


def paired_plan(names, pairs):
    """Round-robin over the units inside each position of
    `loading.schedule` (B C C B B C for k = 3, AB/BA pairs for more); a
    candidate-only unit runs its candidate positions only."""
    plan = []
    for i, selection, _ in loading.schedule(pairs, 1):
        for n in names:
            if selection == "candidate" or n not in CAND_ONLY:
                plan.append(item(n, side_of(selection), i, selection))
    return plan


def control_plan(k):
    plan = []
    for i, selection, _ in loading.schedule(k, 1):
        for switch, plain in CONTROLS:
            plan.append(item(plain if selection == "baseline" else
                             plain + "+" + switch, "base", i, selection))
    return plan + [item(ORDINARY, "cand", 0, "candidate", "reject")]


def plan_for(stage, names, params):
    if stage == "smoke":
        return paired_plan(names, 1)
    if stage == "pilot":
        return [item(u, "base", i, "baseline") for i in range(params["k"])
                for u in names]
    if stage == "control":
        return control_plan(params["k"])
    if stage == "extend":
        return paired_plan(names, params["pairs"])
    if stage in ("run", "followup"):
        return paired_plan(names, params["k"])
    return []


def label_of(entry):
    return "%s-%02d-%s%s" % (
        entry["workload"], entry["pair"], entry["selection"],
        "" if not entry["redraw"] else "-r%d" % entry["redraw"])


def row_unit(r):
    """The unit a decision row is measured by."""
    case, kind = r["case"], r["kind"]
    return {"S1": GRAPH, "R1": RELEASE, "E2": EXT, "E1": EXT}.get(
        case, "registry-" + kind)


# ----------------------------------------------------------- the processes

def mask_function():
    return getattr(d, "mask_path", None) or records.mask_path


def mask_text_function():
    return getattr(d, "mask_text", None) or records.mask_text


def check_lengths(report):
    """Path strings reach `objSize` through structure values: both roots
    and both probe directories have equal lengths (design 8.1), asserted
    before any structure comparison."""
    roots = [len(str(r)) for r in report["roots"].values()]
    probes = [len(v["dir"]) for v in report["reporter"].values()]
    require(len(set(roots)) == 1, "the two snapshot roots differ in length "
            "(%s)" % roots)
    require(len(set(probes)) == 1, "the two probe directories differ in "
            "length (%s)" % probes)


def not_comparable(receipt, unit, root, probe_dir):
    """The rejected process's output is well-formed but its readings cannot
    be compared (records.NotComparable): a redraw, not a failure."""
    try:
        masked = mask_text_function()(receipt["stdout"], root, probe_dir)
        records.validate(masked, controls=cases33.controls_of(unit),
                         root=records.ROOT_MASK)
    except records.NotComparable:
        return True
    except ValueError:
        return False
    return False


def heap_bytes(report, sides):
    out = {}
    for side in ("base", "cand"):
        heaps = sorted({u["heap"] for u in report["units"].values()})
        out[side] = {h: (Path(report["roots"][side]) / h).stat().st_size
                     for h in heaps}
    return out


def run_item(ctx, report, entry_item, unit, redraw, references):
    """One process of the plan (the label of redraw number `redraw`):
    launched, admitted, archived. Returns (entry, receipt)."""
    side = entry_item["side"]
    entry = dict(workload=unit["name"], phase="candidate",
                 pair=entry_item["pair"], selection=entry_item["selection"],
                 rep=0, side=side, redraw=redraw,
                 expect=entry_item["expect"])
    label = label_of(entry)
    layout = d.layout_for(report["layout_seed"], entry["pair"],
                          entry["selection"], 0)
    expected = None if entry["expect"] or "+" in unit["name"] else (
        references or {}).get(unit["name"])
    receipt = d.launch_probe(ctx, side, unit, label, layout, expected)
    receipt.update(phase="candidate", pair=entry["pair"],
                   selection=entry["selection"], rep=0)
    entry.update(d.archive(Path(report["output"]), label, receipt),
                 accepted=receipt["accepted"])
    return entry, receipt


def body(args, spec, report, sides, scratch, fds, verify, journal):
    """The processes of a stage, in the plan's order (`d.run_stage`'s
    `body_fn`)."""
    ctx = d.prepare(args, report, sides, scratch, fds, verify, journal,
                    modules=lambda side: probe_modules(report, side))
    check_lengths(report)
    report["heap_bytes"] = heap_bytes(report, sides)
    loaded = []
    for planned in report["plan"]:
        unit = report["units"][planned["unit"]]
        for redraw in range(MAX_REDRAWS + 1):
            entry, receipt = run_item(ctx, report, planned, unit, redraw,
                                      report["references"])
            report["runs"].append(entry)
            if planned["expect"] == "reject":
                loaded.append((entry, receipt))
                break
            if receipt["accepted"]:
                loaded.append((entry, receipt))
                break
            root = report["roots"][planned["side"]]
            if redraw < MAX_REDRAWS and not_comparable(
                    receipt, unit, root,
                    report["reporter"][planned["side"]]["dir"]):
                continue  # an R-1 redraw: the receipt stays, flagged
            if receipt.get("blocked"):
                report["blocked"] = receipt["rejection"]
            raise d.Refusal("process rejected: %s: %s" % (
                label_of(entry), receipt["rejection"]))
    if verify is not None:
        report["verify"]["after"] = d.run_verify(verify, report["repo"],
                                                 fds)
    report["outcome"] = outcome(report, loaded)


def audit_body(args, spec, report, sides, scratch, fds, verify, journal):
    """The api-audit stage: run.py of the candidate snapshot, its receipt
    (and logs) under the stage's output, sealed in the report."""
    scratch.mkdir(parents=True, exist_ok=False)
    if verify is not None:
        report["verify"] = {"before": d.run_verify(verify, report["repo"],
                                                   fds)}
    root = Path(report["roots"]["cand"])
    script = root / "src/simp/tests/api-audit/run.py"
    require(script.is_file(), "no %s" % script)
    out = Path(report["output"]) / "api-audit"
    env = d.process_env(scratch, {})
    done = loading.execute([sys.executable, "-B", str(script), "--output",
                            str(out)], script.parent, env, args.timeout,
                           fds)
    report["audit"] = dict(command=done["command"], exit=done["exit"],
                           stdout_sha256=done["stdout_sha256"],
                           output="api-audit")
    receipts = sorted(out.glob("*/receipt.json")) if out.is_dir() else []
    require(len(receipts) == 1, "the audit left %d receipts, not one" %
            len(receipts))
    report["audit"]["receipt"] = str(receipts[0].relative_to(
        report["output"]))
    report["audit"]["receipt_seal"] = a.seal(receipts[0])
    if verify is not None:
        report["verify"]["after"] = d.run_verify(verify, report["repo"],
                                                 fds)
    report["outcome"] = outcome(report, [])


# ------------------------------------------------------- reading receipts

def summarize(receipt, unit, root):
    """The validated records of an accepted process (unmasked: the root is
    the side's own)."""
    return records.validate(receipt["stdout"],
                            controls=cases33.controls_of(unit),
                            root=str(root))


def grouped(report, loaded):
    """{unit: {side: [summary]}} of the accepted processes, in the plan's
    order; an anchor moved on a baseline process is a refusal (a harness
    fault, design 8.5)."""
    groups = {}
    for entry, receipt in loaded:
        if not receipt["accepted"]:
            continue
        unit = report["units"][entry["workload"]]
        side = entry["side"]
        summary = summarize(receipt, unit, report["roots"][side])
        if side == "base" and entry["selection"] == "baseline" and \
                summary.get("anchor_moved"):
            raise d.Refusal("an anchor moved on a baseline process of %s: "
                            "%s" % (unit["name"], summary["anchor_moved"]))
        summary["usage"] = receipt["usage"]
        groups.setdefault(entry["workload"], {}).setdefault(
            side, []).append(summary)
    return groups


def digests_of(loaded):
    found = {}
    for entry, receipt in loaded:
        if receipt["accepted"] and not entry["expect"]:
            found.setdefault(entry["workload"], set()).add(receipt["digest"])
    odd = sorted(u for u, v in found.items() if len(v) != 1)
    require(not odd, "outputs differ between processes (or sides) of: " +
            ", ".join(odd))
    return {u: next(iter(v)) for u, v in sorted(found.items())}


def cpu_of(procs):
    return [p["usage"]["utime"] + p["usage"]["stime"] for p in procs]


def times_of(groups):
    """The whole-process CPU (reported: the cost of a probe against the
    trivial probe's), median per unit and side."""
    return {u: {s: dict(cpu=statistics.median(cpu_of(p)), n=len(p))
                for s, p in sides.items()} for u, sides in groups.items()}


# ---------------------------------------------------------------- outcomes

def outcome(report, loaded, folder=None):
    """The numbers and decisions of a stage, from its archived processes
    alone (`loaded`: [(entry, receipt)], the stage's `folder` for the
    audit's files, default its output): the one function a run and its
    replay share, so that they agree byte for byte."""
    stage = report["stage"] or report["mode"]
    if stage == "audit":
        return audit_outcome(report, folder)
    check_lengths(report)
    out = dict(digests=digests_of(loaded))
    refs = report.get("references")
    if refs:
        bad = sorted(u for u, h in out["digests"].items()
                     if u in refs and refs[u] != h)
        require(not bad, "outputs differ from the references: " +
                ", ".join(bad))
    groups = grouped(report, loaded)
    if stage == "smoke":
        out["facts"] = smoke_facts(report, loaded)
        out["times"] = times_of(groups)
        return out
    if stage == "pilot":
        out.update(pilot_outcome(report, groups))
        return out
    if stage == "control":
        out.update(control_outcome(report, loaded, groups))
        return out
    out["results"], out["reported"] = decide(report, groups,
                                             stage == "extend")
    out["reported"]["s3"] = rules.s3_report(groups)
    out["reported"]["times"] = times_of(groups)
    out["owed"] = [list(x) for x in sorted({
        (r["owed"], row_unit(r)) for r in out["results"].values()
        if r["owed"]})]
    return out


def smoke_facts(report, loaded):
    """What a smoke run shows about the harness: per unit and side the
    reporter in fileDirMap, the unit's loads, the heap fingerprint."""
    facts, ok = {}, True
    for entry, receipt in loaded:
        unit = report["units"][entry["workload"]]
        stats = receipt["stats"]
        folder = Path(report["reporter"][entry["side"]]["dir"])
        here = dict(
            reporter_in_files=any(Path(x) == folder for _, x in
                                  stats["files"]),
            loads_ok=d.loads_problem(unit, stats) is None,
            heap_fingerprint=d.sha("\n".join(sorted(
                stats["loaded_before"])).encode()),
            new_modules=len(stats["loaded"]))
        ok = ok and here["reporter_in_files"] and here["loads_ok"]
        facts.setdefault(entry["workload"], {})[entry["side"]] = here
    return dict(units=facts, ok=ok)


def pilot_outcome(report, groups):
    """Graph repeatability, the release noise and the M it needs."""
    graph, release = groups[GRAPH]["base"], groups[RELEASE]["base"]
    repeat = {g: all(rules.constant([p["graph"][g][n]["canon_words"]
                                     for p in graph])
                     for n in graph[0]["graph"][g]) for g in
              rules.GRAPH_GATED}
    noise = {}
    for kind in records.RELEASE_KINDS:
        raw = [p["release"][kind]["after"] - p["release"][kind]["before"]
               for p in release]
        noise[kind] = max(raw) - min(raw)
    worst = max(noise.values())
    m0 = report["params"]["m"]
    required = max(m0, math.ceil(Fraction(worst) / rules.RESOLUTION))
    held = {k: rules.num(min(p["held"][k] for p in release))
            for k in rules.ORDINARY_RELEASE}
    return dict(
        graph_repeatable=repeat, noise_words=noise, m0=m0,
        required_m=required, m=min(M_CAP, required), m_cap=M_CAP,
        capped=required > M_CAP, covered=required <= M_CAP,
        held_per_object=held, resolution=rules.num(rules.RESOLUTION),
        median_wall={u: statistics.median(p["usage"]["wall"] for p in g)
                     for u, g in ((GRAPH, graph), (RELEASE, release))})


def control_outcome(report, loaded, groups):
    """Each control must be detected (fail S1, R1 or L3, or be refused) at
    the decision configuration; `negative_control` is the aggregate the
    ledger reads."""
    found = {}
    for switch, plain in CONTROLS:
        base, cand = groups[plain]["base"], groups[plain + "+" +
                                                  switch]["base"]
        if switch == "graph_extra":
            rows = [rules.s1_kind(base, cand, g) for g in rules.GRAPH_GATED]
        elif switch == "leak":
            rows = rules.r1_rows(base, cand)
        else:
            rows = [rules.l3_kind(base, cand, plain[len("registry-"):])]
        decisions = {r["kind"]: r["decision"] for r in rows}
        found[switch] = dict(unit=plain, expected="fail",
                             decisions=decisions,
                             detected=rules.FAIL in decisions.values())
    ordinary = [(e, r) for e, r in loaded if e["workload"] == ORDINARY]
    refused = bool(ordinary) and all(
        not r["accepted"] and r.get("blocked") and
        "extension module" in r["rejection"] for _, r in ordinary)
    found["ext_ordinary"] = dict(unit=ORDINARY, expected="refused",
                                 detected=refused)
    detected = all(c["detected"] for c in found.values())
    return dict(controls=found, negative_control=dict(
        decision=rules.FAIL if detected else rules.PASS, detected=detected,
        expected=rules.FAIL))


def decide(report, groups, paired):
    """({key: row} of the gated decisions, {key: row} of the reported
    ones) of a decision stage. The stage's units decide their own cases;
    E2 (a) and (c) need the ordinary candidate's `graph` and
    `registry-state-empty` and are decided where both ran."""
    names = report["workloads"]
    declared = offline.load_declared()
    deltas = rules.total_deltas(declared)
    extension_text = json.dumps(declared.get("e2c", {}))
    mask = mask_function()

    def masked(side, path):
        return mask(path, report["roots"][side],
                    report["reporter"][side]["dir"])

    found = []
    for name in names:
        g = groups.get(name, {})
        base, cand = g.get("base", []), g.get("cand", [])
        if name in REGISTRY:
            kind = name[len("registry-"):]
            heap = report["units"][name]["heap"]
            found.append(rules.l1_kind(base, cand, kind, masked))
            found.append(rules.l3_kind(base, cand, kind))
            try:
                delta = rules.declared_delta(deltas, heap, kind) if \
                    all(rules.applicable(base + cand)) else None
                found.append(rules.s2_kind(base, cand, kind, delta,
                                           paired))
            except ValueError as error:
                raise d.Refusal(str(error))
        elif name == GRAPH:
            found += [rules.s1_kind(base, cand, g, paired)
                      for g in rules.GRAPH_GATED]
        elif name == RELEASE:
            found += rules.r1_rows(base, cand)
        elif name == EXT:
            found.append(rules.e1_ext(cand))
            found.append(rules.e2b(cand))
            ordinary = groups.get(GRAPH, {}).get("cand")
            if ordinary:
                found.append(rules.e2a(cand, ordinary))
            plain = groups.get("registry-state-empty", {}).get("cand")
            if plain:
                found.append(rules.e2c(cand, plain, extension_text))
    found.append(rules.s4_row())
    gated, reported = {}, {}
    for r in found:
        key = rules.key_of(r["case"], r["kind"])
        (gated if r["decision"] in rules.GATES else reported)[key] = r
    return gated, reported


def audit_outcome(report, folder=None):
    """E1/L3 api-audit from the sealed receipt: 8 cases, every one PASS,
    for the candidate's head."""
    audit = report["audit"]
    top = Path(folder or report["output"])
    path = a.safe_child(top, audit["receipt"])
    require(a.seal(path) == audit["receipt_seal"], "the audit receipt "
            "changed")
    data = a.load(path)
    folder = Path(path).parent
    cases = data.get("cases") or []
    problems = []
    if audit["exit"] != 0:
        problems.append("run.py exited %s" % audit["exit"])
    if len(cases) != AUDIT_CASES:
        problems.append("%d cases, not %d" % (len(cases), AUDIT_CASES))
    problems += ["%s/%s/%s not PASS" % (c["order"], c["foreign_kind"],
                                        c["foreign_owner"])
                 for c in cases if c.get("pass") is not True]
    if data.get("pass") is not True:
        problems.append("the receipt is not a pass")
    if data.get("head") != report["cand"]:
        problems.append("the audit ran at %s, not the candidate" %
                        data.get("head"))
    for c in cases:
        log = folder / c["log"]
        if not log.is_file() or a.seal(log) != c["log_seal"]:
            problems.append("the log of %s is missing or changed" %
                            c["log"])
    ok = not problems
    detail = dict(cases=len(cases), receipt=audit["receipt"],
                  seal=audit["receipt_seal"])
    results = {}
    for case in ("E1", "L3"):
        results["%s:api-audit" % case] = rules.row(
            case, "api-audit", rules.PASS if ok else rules.FAIL,
            "8 PASS with a sealed receipt" if ok else "; ".join(problems),
            **detail)
    return dict(results=results, reported={}, owed=[])


# ------------------------------------------------------------------ report

def jsonable(value):
    return json.loads(json.dumps(value))


def new_report(mode, stage, spec, repo, sides, mseal, output):
    names = spec["names"]
    params = spec["params"]
    units = {n: jsonable(unit_of(n, params)) for n in names}
    return {
        "schema": SCHEMA, "success": False, "mode": mode, "stage": stage,
        "table": LEDGER_TABLE, "claims": d.ACTIVE.claims,
        "repo": str(repo), "output": str(output), "key": spec["key"],
        "base": sides["base"]["pin"], "cand": sides["cand"]["pin"],
        "roots": {k: str(v["root"]) for k, v in sides.items()},
        "manifest": mseal, "layout_seed": spec["seed"],
        "workloads": names, "params": params, "units": units,
        "plan": plan_for(stage or mode, names, params),
        "references": spec.get("references"), "counts": spec.get("counts"),
        "first_stage": spec.get("first"), "replaces": spec.get("replaces"),
        "pilot": spec.get("pilot"), "declared": a.seal(offline.DECLARED),
        "runs": [], "argv": sys.argv, "reporter_seal": d.REPORTER_SEAL,
        "code": d.code_seals()}


def run(args, spec):
    """One stage of the storage driver (a `d.run_stage`)."""
    stage = spec["mode"]
    return d.run_stage(
        args, spec, body_fn=audit_body if stage == "audit" else body,
        report_fn=new_report, decisive_stages=DECISIVE,
        table=LEDGER_TABLE)


# ------------------------------------------------------------------ replay

def check_run(folder, report, entry):
    """One archived process, as `d.check_receipt` checks the timing
    driver's: seal, label, fields, command, layout, environment, and every
    per-process validation and the digest again from the stored data.
    Returns the receipt."""
    path = a.safe_child(folder, entry["receipt"])
    require(a.seal(path) == entry["seal"], "changed process receipt")
    require(entry["receipt"] == label_of(entry) + ".json.gz",
            "relabelled process: " + entry["receipt"])
    receipt = a.load(path)
    require(all(receipt[k] == entry[k] for k in (
        "workload", "phase", "pair", "selection", "rep", "side")) and
        receipt["accepted"] is entry["accepted"],
        "process receipt disagrees with the report: " + entry["receipt"])
    unit = report["units"][entry["workload"]]
    require(unit == jsonable(unit_of(entry["workload"],
                                     report["params"])),
            "the unit is not the one its parameters give: " +
            entry["workload"])
    d.check_unit_env(unit)
    side = entry["side"]
    root = Path(report["roots"][side])
    reporter = report["reporter"][side]
    require(d.unit_argv_shape(unit, root, reporter["uo"], receipt["argv"]),
            "unexpected command: " + entry["receipt"])
    layout = d.layout_for(report["layout_seed"], entry["pair"],
                          entry["selection"], 0)
    require(receipt["layout"] == layout and
            receipt["env"].get("T32_LAYOUT") == str(layout) and
            not receipt["busy"] and "T32_BUSY" not in receipt["env"],
            "wrong layout or busy setting: " + entry["receipt"])
    require({k: v for k, v in receipt["env"].items()
             if k.startswith(d.ACTIVE.env_prefix)} == unit["env"],
            "wrong probe environment: " + entry["receipt"])
    expected = None if entry["expect"] or "+" in unit["name"] else (
        report["references"] or {}).get(unit["name"])
    if receipt["accepted"]:
        d.validate(receipt, unit, root, reporter["dir"], expected,
                   side == "cand")
        require(d.probe_digest(receipt["stdout"], root, reporter["dir"],
                               unit) == receipt["digest"],
                "the stored output does not give the digest: " +
                entry["receipt"])
        require(d.same(d.measure(receipt), receipt["measurement"]["raw"]),
                "changed measurement: " + entry["receipt"])
    elif entry["expect"] == "reject":
        try:
            d.validate(receipt, unit, root, reporter["dir"], None,
                       side == "cand")
        except d.Blocked as error:
            require(str(error) == receipt["rejection"],
                    "the rejection is not the recomputed one")
        else:
            raise d.Refusal("a process that was refused validates: " +
                            entry["receipt"])
    else:
        require(not_comparable(receipt, unit, root, reporter["dir"]),
                "a rejected process that is not a redraw: " +
                entry["receipt"])
    return receipt


def check_plan(report):
    """The runs are the plan's, in order, each followed by its redraws
    (a rejected try of the same position), and the plan is the stage's
    own for the units and parameters."""
    stage = report["stage"] or report["mode"]
    require(report["plan"] == plan_for(stage, report["workloads"],
                                       report["params"]),
            "the plan is not the stage's")
    found, at = [], -1
    for e in report["runs"]:
        if e["redraw"] == 0:
            at += 1
            found.append(e)
        else:
            require(at >= 0 and not report["runs"][report["runs"].index(
                e) - 1]["accepted"] and e["redraw"] <= MAX_REDRAWS,
                "a redraw that follows no rejected process")
    require(len(found) == len(report["plan"]) and all(
        (e["workload"], e["side"], e["pair"], e["selection"],
         e["expect"]) == (p["unit"], p["side"], p["pair"], p["selection"],
                          p["expect"])
        for e, p in zip(found, report["plan"])),
        "missing, extra or reordered processes")


def decision_params(pilot):
    """The configuration of the decision runs (and of the controls): the
    pilot's sizes and its M, clamped."""
    out = pilot["outcome"]
    return dict(sizes=pilot["params"]["sizes"], m=out["m"], k=K)


def replay_one(folder, ledger=None, repo=None, counts=None):
    """Recompute every observation, check and decision of one finished
    storage stage from its archived receipts (no process runs). Returns
    (info, report)."""
    folder = Path(folder).resolve(strict=True)
    seal = a.seal(folder / "downstream.json")
    report = a.load(folder / "downstream.json")
    require(report.get("schema") == SCHEMA and report["success"] is True,
            "not a successful " + SCHEMA + " run")
    require(report["table"] == LEDGER_TABLE, "malformed run")
    mode, stage = report["mode"], report["stage"]
    require(stage == (None if mode in INFO else mode) and
            mode in INFO + DECISIVE, "malformed run")
    require(report["reporter_seal"] == d.REPORTER_SEAL and
            report["layout_seed"] == SEEDS[mode],
            "the reporter or seed changed")
    d.check_code(report["code"])
    require(report["declared"] == a.seal(offline.DECLARED),
            "the declaration changed since the run")
    if mode in DECISIVE:
        require(all(report["verify"][k]["exit"] == 0
                    for k in ("before", "after")),
                "a decision stage ran without the snapshot verification")
    if mode != "audit":
        d.check_probe_sources(report)
        check_plan(report)
        loaded = [(e, check_run(folder, report, e)) for e in report["runs"]]
    else:
        loaded = []
    require(d.same(outcome(report, loaded, folder), report["outcome"]),
            "recomputed outcome differs from the report")
    info = dict(replayed=len(loaded), mode=mode, stage=stage, seal=seal)
    if mode in DECISIVE:
        info["exit"] = d.stage_status(report["outcome"]["results"])
        info["attempts"] = d.check_ledger(
            ledger or d.ledger_path(report["repo"]), report, seal,
            info["exit"], LEDGER_TABLE)
        check_counts_use(report, counts, repo)
    return info, report


def check_counts_use(report, path, repo):
    """The stage used this counts file: its seal, the values it declares
    (the parameters and the references) and the commit rule where the
    repository is at hand."""
    used = report["counts"]
    stage = report["stage"]
    file = Path(path or (FOLLOWUP_COUNTS if stage == "followup" else
                         STORAGE_COUNTS))
    require(used is not None and file.is_file() and
            a.seal(file) == used["seal"],
            "the counts file is not the one the stage used: %s" % file)
    data = a.load(file)
    d.check_code(data["code"])
    if stage != "audit":
        require(data["references"] == report["references"],
                "changed references")
        want = data["followup" if stage == "followup" else "decision"]
        require(all(report["params"][k] == want[k]
                    for k in ("sizes", "m", "k")), "changed parameters")
    repo = repo or report["repo"]
    if Path(repo).is_dir():
        require(d.check_counts_commit(repo, file, report["cand"]) ==
                used["commit"], "changed counts commit")


def parents(report):
    return report.get("first_stage") or report.get("replaces")


def replay_chain(folder, ledger=None, repo=None, counts=None,
                 followup_counts=None):
    """The stage chain ending in `folder`: [{stage, report, info, folder}].
    A contingency stage (extend, followup) names its parent run, which is
    replayed and tied to it (same gate, manifest, units owed)."""
    folder = Path(folder).resolve(strict=True)
    stage = a.load(folder / "downstream.json")["stage"]
    info, report = replay_one(folder, ledger, repo, followup_counts if
                              stage == "followup" else counts)
    here = dict(stage=report["stage"], report=report, info=info,
                folder=folder)
    link = parents(report)
    if link is None:
        return [here]
    parent = replay_chain(link["run"], ledger, repo, counts,
                          followup_counts)
    last = parent[-1]
    require(a.seal(Path(link["run"]) / "downstream.json") == link["seal"]
            and link["attempt"] == last["report"]["attempt"],
            "the stage names another parent")
    for key in ("base", "cand", "key", "roots", "manifest"):
        require(report[key] == last["report"][key],
                "the stage changes " + key)
    require(report["references"] == last["report"]["references"],
            "the stage changes the references")
    kind = "extend" if report["stage"] == "extend" else "followup"
    owed = owed_units(parent, kind)
    require(owed and report["workloads"] == owed, "the %s stage is not of "
            "the units owed: %s" % (report["stage"], owed))
    return parent + [here]


def final_rows(chain):
    """{key: row} the last stage that decided each case and kind decides
    (stages are never combined); with the stage name."""
    found = {}
    for entry in chain:
        for key, r in entry["report"]["outcome"]["results"].items():
            found[key] = dict(r, stage=entry["stage"],
                              attempt=entry["report"]["attempt"])
    return found


def owed_units(chain, kind):
    """The units whose rows are owed `kind` ("extend" or "followup") after
    the chain, by the rows that decide them last."""
    rows = final_rows(chain)
    return [u for u in UNITS if any(
        r["owed"] == kind and row_unit(r) == u for r in rows.values())]


# ------------------------------------------------------- counts, predeclare

def table_counts_path(args):
    return Path(getattr(args, "timing_counts", None) or d.COUNTS)


def storage_counts_path(args, followup=False):
    """The run counts (`--storage-counts`) or, for a follow-up,
    its own (`--followup-counts`)."""
    if followup:
        return Path(getattr(args, "followup_counts", None) or
                    FOLLOWUP_COUNTS)
    return Path(getattr(args, "storage_counts", None) or STORAGE_COUNTS)


def load_storage_counts(path, sides, kind, repo, mseal, committed=True):
    """A storage counts file, checked against this gate: schema, pins,
    manifest, the code and declaration it is bound to, the timing counts'
    seal it binds, the clamp of M (`required`/`capped`) and the commit
    rule."""
    data = a.load(path)
    require(data.get("schema") == COUNTS_SCHEMA and data.get("kind") ==
            kind, "not a storage %s counts file" % kind)
    require(data["base"] == sides["base"]["pin"] and
            data["cand"] == sides["cand"]["pin"],
            "the counts file is of another gate")
    require(data["manifest"] == mseal, "the snapshots were rebuilt since "
            "the counts file was made: predeclare again")
    require(data["code"] == d.code_seals(), "the code changed since the "
            "counts file was made")
    require(data["declared"] == a.seal(offline.DECLARED),
            "the declaration changed since the counts file was made")
    want = data["decision"] if kind == "run" else data["followup"]
    cap = data["m_cap"]
    require(want["k"] == K and want["m"] == min(cap, data["required_m"])
            and data["capped"] == (data["required_m"] > cap),
            "the counts file's M, required_m and capped disagree")
    if committed:
        data["commit"] = d.check_counts_commit(repo, path,
                                               sides["cand"]["pin"])
    return data


def info_run(folder, key, mode, names, ledger, mseal):
    """A replayed information run of this gate (the storage driver's own
    replay, the timing driver's checks)."""
    info, report = replay_one(folder, ledger=ledger)
    d.check_info_run(info, report, key, mode, ledger, names, mseal,
                     LEDGER_TABLE)
    return info, report


def offline_seals(paths):
    """The seals of the S3 reports, each checked as `dispose` checks them:
    its schema, its seal file and the code it was made by."""
    found = {}
    for path in paths or ():
        path = Path(path).resolve(strict=True)
        report = a.load(path)
        require(report.get("schema") == offline.SCHEMA, "not an offline "
                "report: %s" % path)
        recorded = a.load(Path(str(path) + ".seal"))
        require(recorded == a.seal(path), "the seal of %s differs" % path)
        offline.check_code(report["code"])
        require(report["command"] not in found, "two %s reports" %
                report["command"])
        found[report["command"]] = dict(path=str(path), seal=recorded)
    return found


def predeclare_run(args):
    """The counts file of the decision stages, from a smoke, a pilot and a
    control that all ran, verified, on this gate, bound to the committed
    timing counts."""
    sides, mseal = d.pins_of(args)
    key = d.gate_key(sides)
    timing_path = table_counts_path(args).resolve(strict=True)
    timing = d.load_counts(timing_path, sides, "first", args.repo,
                           mseal=mseal)
    pilot_info, pilot = info_run(args.pilot, key, "pilot",
                                 list(PILOT_UNITS), args.ledger, mseal)
    smoke_info, smoke = info_run(args.smoke, key, "smoke", list(UNITS),
                                 args.ledger, mseal)
    control_info, control = info_run(args.control, key, "control",
                                     control_names(), args.ledger, mseal)
    out = pilot["outcome"]
    require(out["covered"], "the pilot is not usable: the release noise "
            "needs M %d, over the cap %d" % (out["required_m"], M_CAP))
    require(smoke["outcome"]["facts"]["ok"], "the smoke run did not pass "
            "the probe facts (reporter in fileDirMap, every process loads "
            "what its kind claims)")
    decision = decision_params(pilot)
    require(control["params"] == decision, "the controls did not run at "
            "the decision configuration (%s, not %s)" % (
                control["params"], decision))
    require(control["pilot"] == dict(
        attempt=pilot["attempt"], seal=pilot_info["seal"]),
        "the controls were sized from another pilot")
    found = control["outcome"]["controls"]
    require(control["outcome"]["negative_control"]["detected"],
            "a control was not detected: " + ", ".join(
                sorted(k for k, c in found.items() if not c["detected"])))
    refs = {u: smoke["outcome"]["digests"][u] for u in REGISTRY + TRIVIAL}
    wall = pilot["outcome"]["median_wall"]
    estimate = dict(per_process_wall=wall, processes=dict(
        run=2 * K * (len(REGISTRY) + len(TRIVIAL) + 2) + K,
        extend=2 * EXTEND_PAIRS), verify_seconds=sum(
            v["seconds"] for v in (smoke.get("verify") or {}).values()))
    return {
        "schema": COUNTS_SCHEMA, "kind": "run", "base": pilot["base"],
        "cand": pilot["cand"], "manifest": mseal, "seed": SEED,
        "seeds": SEEDS, "decision": decision, "m0": out["m0"],
        "required_m": out["required_m"], "m_cap": M_CAP,
        "capped": out["capped"], "resolution": out["resolution"],
        "contingencies": dict(
            extend=dict(pairs=EXTEND_PAIRS, rule="paired_statistics at "
                        "zero margin, for a unit whose value is not "
                        "repeatable within a side"),
            followup=dict(rule="R1 / E2 (b) at M x %d (cap %d), counts "
                          "committed alone" % (FOLLOWUP_FACTOR,
                                               M_CAP_FOLLOWUP))),
        "timing_counts": dict(path=str(timing_path),
                              seal=a.seal(timing_path),
                              commit=timing["commit"]),
        "declared": a.seal(offline.DECLARED), "references": refs,
        "pilot": dict(attempt=pilot["attempt"], seal=pilot_info["seal"]),
        "smoke": dict(attempt=smoke["attempt"], seal=smoke_info["seal"]),
        "control": dict(attempt=control["attempt"],
                        seal=control_info["seal"], params=control["params"],
                        detected={k: c["detected"]
                                  for k, c in found.items()}),
        "offline": offline_seals(args.offline),
        "time_estimate": estimate, "code": d.code_seals()}


def predeclare_followup(args):
    """The counts file of a follow-up: the units owed it after the chain
    ending in --stage, at M times FOLLOWUP_FACTOR (capped, `required` and
    `capped` recorded as the first counts do)."""
    sides, mseal = d.pins_of(args)
    chain = replay_chain(args.stage, args.ledger, args.repo,
                         args.storage_counts, args.followup_counts)
    owed = owed_units(chain, "followup")
    require(owed, "no unit is owed a follow-up")
    first, last = chain[0]["report"], chain[-1]
    base_m = first["params"]["m"]
    required = base_m * FOLLOWUP_FACTOR
    return {
        "schema": COUNTS_SCHEMA, "kind": "followup", "base": first["base"],
        "cand": first["cand"], "manifest": mseal, "seed": SEEDS[
            "followup"], "workloads": owed, "required_m": required,
        "m_cap": M_CAP_FOLLOWUP, "capped": required > M_CAP_FOLLOWUP,
        "followup": dict(sizes=first["params"]["sizes"],
                         m=min(M_CAP_FOLLOWUP, required), k=K),
        "references": first["references"],
        "replaces": dict(run=str(last["folder"]),
                         attempt=last["report"]["attempt"],
                         seal=last["info"]["seal"]),
        "declared": a.seal(offline.DECLARED), "code": d.code_seals()}


# ------------------------------------------------------------------- specs

def selected(args):
    only = getattr(args, "only", None)
    if not only:
        return list(UNITS)
    require(set(only) <= set(UNITS), "unknown unit in --only")
    return [u for u in UNITS if u in only]


def sizes_arg(text):
    sizes = [int(x) for x in text.split(",")]
    require(sizes == sorted(set(sizes)) and all(n >= 0 for n in sizes),
            "--sizes is increasing non-negative integers")
    return tuple(sizes)


def spec_of(stage, names, params, **extra):
    return dict(dict(references=None), mode=stage,
                stage=stage if stage in DECISIVE else None, names=names,
                params=params, seed=SEEDS[stage], **extra)


def info_spec(args, mode):
    sides, mseal = d.pins_of(args)
    key = d.gate_key(sides)
    if mode == "smoke":
        sizes = tuple(args.sizes or SMOKE_SIZES)
        return spec_of(mode, selected(args), dict(
            sizes=list(sizes), m=args.m or SMOKE_M, k=1))
    sizes = tuple(args.sizes or records.DEFAULT_SIZES)
    if mode == "pilot":
        return spec_of(mode, list(PILOT_UNITS), dict(
            sizes=list(sizes), m=args.m0 or M0, k=K))
    info, pilot = info_run(args.pilot, key, "pilot", list(PILOT_UNITS),
                           None, mseal)
    require(pilot["outcome"]["covered"], "--pilot is not usable: M %d "
            "over the cap" % pilot["outcome"]["required_m"])
    return spec_of(mode, control_names(), decision_params(pilot),
                   pilot=dict(attempt=pilot["attempt"], seal=info["seal"]))


def counts_spec(args, stage, followup=False):
    sides, mseal = d.pins_of(args)
    path = storage_counts_path(args, followup).resolve(strict=True)
    counts = load_storage_counts(path, sides, "followup" if followup else
                                 "run", args.repo, mseal)
    use = d.counts_use(path, counts)
    return sides, counts, use


def run_spec(args):
    require(not getattr(args, "only", None), "a decision stage measures "
            "all the units")
    sides, counts, use = counts_spec(args, "run")
    return spec_of("run", list(UNITS), counts["decision"], counts=use,
                   references=counts["references"])


def link_of(chain):
    last = chain[-1]
    return dict(run=str(last["folder"]), attempt=last["report"]["attempt"],
                seal=last["info"]["seal"])


def extend_spec(args):
    sides, counts, use = counts_spec(args, "extend")
    chain = replay_chain(args.first, None, args.repo, args.storage_counts)
    owed = owed_units(chain, "extend")
    require(owed, "no unit is owed the %d-pair stage" % EXTEND_PAIRS)
    return spec_of("extend", owed, dict(
        counts["decision"], pairs=EXTEND_PAIRS), counts=use,
        first=link_of(chain), references=counts["references"])


def followup_spec(args):
    sides, counts, use = counts_spec(args, "followup", True)
    chain = replay_chain(args.stage, None, args.repo, args.storage_counts,
                         args.followup_counts)
    owed = owed_units(chain, "followup")
    require(owed and owed == counts["workloads"], "the follow-up counts "
            "are not of the units owed: %s" % owed)
    return spec_of("followup", owed, counts["followup"], counts=use,
                   replaces=link_of(chain),
                   references=counts["references"])


def audit_spec(args):
    sides, counts, use = counts_spec(args, "audit")
    return spec_of("audit", [], {}, counts=use)


# --------------------------------------------------------------------- CLI

def exit_of(report):
    """0 pass, 1 fail (a failing stage, an undetected control), 2 an
    inconclusive or blocked stage (or a pilot that cannot resolve), 3 the
    run failed or was refused."""
    if not report["success"]:
        return 2 if report.get("blocked") else 3
    out = report["outcome"]
    mode = report["mode"]
    if mode == "control":
        return 0 if out["negative_control"]["detected"] else 1
    if mode == "pilot":
        return 0 if out["covered"] else 2
    if mode == "smoke":
        return 0 if out["facts"]["ok"] else 2
    return {"pass": 0, "fail": 1}.get(d.stage_status(out["results"]), 2)


def summary_line(report):
    out = report.get("outcome", {})
    head = "TASK33 storage %s: attempt %s, %d processes, success %s" % (
        report["mode"], report.get("attempt"), len(report["runs"]),
        report["success"])
    if not report["success"]:
        return head + "\nfailure: " + report.get("failure", "?")
    if "results" in out:
        return head + "\n" + "\n".join(
            "  %-24s %-12s%s" % (k, r["decision"], "" if not r["owed"] else
                                 " owed " + r["owed"])
            for k, r in sorted(out["results"].items()))
    return head


class Parser(d.Parser):
    pass


def add_common(parser):
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--base-root", type=Path, required=True)
    parser.add_argument("--cand-root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--timing-counts", type=Path, help="the timing "
                        "counts file (default task33_counts.json)")
    parser.add_argument("--storage-counts", type=Path, help="the storage "
                        "counts file (default task33_storage_counts.json)")
    parser.add_argument("--followup-counts", type=Path, help="the "
                        "follow-up's counts file (default "
                        "task33_storage_followup_counts.json)")


def add_run(parser):
    add_common(parser)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scratch", type=d.absolute_path,
                        default=SCRATCH_ROOT)
    parser.add_argument("--timeout", type=int, default=d.TIMEOUT)
    parser.add_argument("--verify-argv", type=shlex.split)
    parser.add_argument("--no-verify", action="store_true")
    parser.add_argument("--authorize-measurements", action="store_true")
    parser.add_argument("--only", action="append", default=[])
    parser.add_argument("--sizes", type=sizes_arg)
    parser.add_argument("--m", type=int, help="smoke: the release size")
    parser.add_argument("--m0", type=int, help="pilot: the release size")


RUN_COMMANDS = ("smoke", "pilot", "control", "run", "extend", "followup",
                "audit")
COMMANDS = RUN_COMMANDS + ("predeclare", "replay", "dispose",
                           "dispose-snapshots")


def build_parser():
    parser = Parser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="command", required=True,
                                parser_class=Parser)
    cmd = {name: sub.add_parser(name) for name in COMMANDS}
    for name in RUN_COMMANDS:
        add_run(cmd[name])
    cmd["control"].add_argument("--pilot", type=Path, required=True)
    cmd["extend"].add_argument("--first", type=Path, required=True,
                               help="the run (or the stage) that owes it")
    cmd["followup"].add_argument("--stage", type=Path, required=True)
    pre = cmd["predeclare"]
    add_common(pre)
    pre.add_argument("--ledger", type=Path)
    pre.add_argument("--pilot", type=Path)
    pre.add_argument("--smoke", type=Path)
    pre.add_argument("--control", type=Path)
    pre.add_argument("--offline", type=Path, action="append", default=[],
                     help="an S3 report (audit, harvest, archive)")
    pre.add_argument("--stage", type=Path, help="follow-up: the stage")
    pre.add_argument("--followup", action="store_true")
    pre.add_argument("--out", type=Path, required=True)
    rep = cmd["replay"]
    rep.add_argument("runs", type=Path, nargs="+")
    rep.add_argument("--ledger", type=Path)
    rep.add_argument("--repo", type=Path)
    rep.add_argument("--storage-counts", type=Path)
    rep.add_argument("--followup-counts", type=Path)
    dis = cmd["dispose"]
    dis.add_argument("--stage", type=Path, action="append", required=True,
                     help="the last stage of the storage chain(s): run, "
                     "or its contingency stage; once each for the audit "
                     "stage")
    dis.add_argument("--timing-stage", type=Path, required=True,
                     help="the last timing stage (replayed under "
                     "--table task33)")
    dis.add_argument("--offline", type=Path, action="append",
                     required=True, help="S3 reports: audit, harvest, "
                     "archive")
    dis.add_argument("--repo", type=Path)
    dis.add_argument("--ledger", type=Path)
    dis.add_argument("--timing-counts", type=Path)
    dis.add_argument("--storage-counts", type=Path)
    dis.add_argument("--followup-counts", type=Path)
    dis.add_argument("--relocated", action="append", default=[],
                     metavar="ATTEMPT=DIR")
    dis.add_argument("--out", type=Path, required=True)
    snaps = cmd["dispose-snapshots"]
    snaps.add_argument("--evidence", type=Path, required=True,
                       help="the evidence/task33 directory")
    snaps.add_argument("--verify-argv", type=shlex.split,
                       help="the snapshot verification (default: "
                       "task32_snapshots.py verify)")
    snaps.add_argument("--manifest", type=Path, required=True)
    snaps.add_argument("--repo", type=Path, required=True)
    snaps.add_argument("--scratch-root", type=Path, default=SCRATCH_ROOT)
    return parser


def dispatch(args):
    command = args.command
    if command in ("smoke", "pilot", "control"):
        spec = info_spec(args, command)
    elif command == "run":
        spec = run_spec(args)
    elif command == "extend":
        spec = extend_spec(args)
    elif command == "followup":
        spec = followup_spec(args)
    elif command == "audit":
        spec = audit_spec(args)
    elif command == "predeclare":
        d.require_ledger(args)
        data = predeclare_followup(args) if args.followup else \
            predeclare_run(args)
        with args.out.open("x") as stream:
            stream.write(d.dumps(data))
        print("wrote %s; commit it alone before any decision process" %
              args.out)
        return 0
    elif command == "replay":
        d.require_ledger(args)
        for folder in args.runs:
            print(json.dumps(replay_chain(
                folder, args.ledger, args.repo, args.storage_counts,
                args.followup_counts)[-1]["info"], sort_keys=True))
        return 0
    else:
        import task33_dispose as dispose
        d.require_ledger(args)
        return (dispose.dispose if command == "dispose" else
                dispose.dispose_snapshots)(args)
    report = run(args, spec)
    print(summary_line(report))
    return exit_of(report)


def main(argv=None):
    return d.main(argv, table=TABLE, build=build_parser, run=dispatch,
                  summarize=summary_line)


if __name__ == "__main__":
    sys.exit(main())
