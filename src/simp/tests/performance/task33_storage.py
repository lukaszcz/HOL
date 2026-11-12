#!/usr/bin/env python3
"""TASK33 storage and release driver (slice S4): the stages that measure
what a fresh process holds (cases L1, L3, S1, S2, S3, R1, E1, E2) with the
probes of task33/ on the two TASK32 snapshots, and the commands around them.

  smoke      every unit once per side (`ext`: candidate only), at small
             sizes and M: the harness works (digests, reporter registered,
             heap facts); information run
  pilot      base only: 3 `graph` and 3 `release` processes at the decision
             sizes and a pilot M0: repeatability and the noise that sizes M
             (required M, clamped to the cap RELEASE_BUDGET_S gives over
             the CPU per object of the pilot's release processes and of the
             smoke's extension process: `required`/`capped`); information
             run, sized from a smoke (--smoke)
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
             within a side); it decides only the rows owed it
  followup   the contingency: R1 / E2 (b) at a larger M (the greater of
             4 M and M x floor range / resolution, capped by 4 times the
             budget), for the units a stage owes (resolution not reached),
             counts committed alone; it decides only the rows owed it
  audit      `src/simp/tests/api-audit/run.py` in the candidate snapshot:
             8 PASS, its receipt sealed under the stage's output (the
             execution is the stage's measuring entry, so that a refused
             audit is a judged attempt)
  predeclare task33_storage_counts.json (or, with --followup, the
             follow-up's) from the replayed smoke, pilot and control and the
             three S3 reports (--offline), bound to the committed timing
             counts
  replay     recompute every decision of finished runs from their archives
             (no process runs)
  dispose    one disposition.json: the timing disposition, the offline
             reports (the sealed ones) and these stages' decisions, one per
             case and kind, with the process redraws
  dispose-snapshots
             remove the snapshots after the last use (design section 5),
             given a sealed disposition.json with nothing owed

The processes, locking, ledger, receipts and their checks are the timing
driver's (task32_downstream.py, the `task33` table of it; its `run_stage`,
`launch_probe`, `check_info_run`, `check_ledger`, ...): this file adds the
units, plans, rules (task33_rules.py) and replay of the storage stages; its
ledger table is `task33-storage` (same attempts.jsonl as the loading
driver). Exit status as the timing driver's: 0 pass, 1 fail, 2
inconclusive or blocked, 3 refused or a usage error, 4 a signal.
"""
import json
import math
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
# CPU seconds one release or extension process may take at the decision M
# (design 8.6, 8.7): the cap on M is this budget over the larger CPU per
# released object of the pilot's release processes and of the smoke's
# extension process (`cap_of`; the start-up counts, so the cost is an upper
# bound); a follow-up may take FOLLOWUP_FACTOR times as much, which must
# stay under the process timeout (`check_budget`). The required M assumes
# that the raw noise in words of a release process does not depend on M
# (the pilot measures it at M0; the follow-up's scaling by the floor range
# makes the same assumption); the decision stages check it by the floor
# (R1 is inconclusive when the floor's range exceeds the resolution).
RELEASE_BUDGET_S = 60
FOLLOWUP_FACTOR = 4  # the least growth of M in a follow-up, and its budget
MAX_REDRAWS = 3  # tries after the first at one position of a plan
SCRATCH_ROOT = Path("/dev/shm/t33")
AUDIT_CASES = 8
AUDIT_UNIT = "api-audit"
OFFLINE_COMMANDS = ("archive", "audit", "harvest")  # the S3 reports

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


def check_budget(timeout=None):
    """A follow-up's budget must fit in the process timeout, else a capped
    follow-up process would always time out."""
    limit = d.TIMEOUT if timeout is None else timeout
    require(FOLLOWUP_FACTOR * RELEASE_BUDGET_S < limit,
            "a follow-up's CPU budget (%d x %s s) is not under the process "
            "timeout (%s s): a capped follow-up process would time out" % (
                FOLLOWUP_FACTOR, RELEASE_BUDGET_S, limit))


check_budget()


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


REGISTRY_PLAIN = "registry-state-empty"  # the ordinary candidate E2 uses
E2_UNITS = dict(a=(EXT, GRAPH), b=(EXT,), c=(EXT, REGISTRY_PLAIN),
                u=(EXT, REGISTRY_PLAIN))


def row_units(r):
    """The units a decision row is measured by (a stage that owes the row
    runs all of them: E2 (a) compares the extension probe's rows with the
    ordinary candidate's)."""
    case, kind = r["case"], r["kind"]
    if case == "E2":
        return E2_UNITS[kind]
    return ({"S1": (GRAPH,), "R1": (RELEASE,), "E1": (EXT,)}.get(case) or
            ("registry-" + kind,))


# ----------------------------------------------------------- the processes

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


def incomparable(receipt, unit, root, probe_dir):
    """Why a rejected process is a redraw, or None: its output is well
    formed but its readings cannot be compared (records.NotComparable) and
    that is its whole rejection (the digest of the output, which cannot be
    made, is the only check it failed)."""
    if receipt["accepted"] or receipt.get("digest_error") is None or \
            receipt["rejection"] != receipt["digest_error"]:
        return None
    try:
        masked = d.mask_text(receipt["stdout"], root, probe_dir)
        records.validate(masked, controls=cases33.controls_of(unit),
                         root=records.ROOT_MASK)
    except records.NotComparable as error:
        return str(error)
    except ValueError:
        return None
    return None


def heap_bytes(report, manifest):
    """{side: {heap: bytes}} of the heaps the units run on, from the sealed
    snapshot manifest (the products it lists)."""
    heaps = sorted({u["heap"] for u in report["units"].values()})
    out = {}
    for side in ("base", "cand"):
        products = manifest["sides"][side]["products"]
        missing = [h for h in heaps if h not in products]
        require(not missing, "the manifest lists no %s: %s" % (
            ", ".join(missing), side))
        out[side] = {h: products[h]["bytes"] for h in heaps}
    return out


def run_item(ctx, report, entry_item, unit, redraw, references):
    """One process of the plan (the label of redraw number `redraw`):
    launched, admitted, archived. Returns (entry, receipt)."""
    side = entry_item["side"]
    entry = dict(workload=unit["name"], phase="candidate",
                 pair=entry_item["pair"], selection=entry_item["selection"],
                 rep=0, side=side, redraw=redraw,
                 expect=entry_item["expect"], superseded=None)
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


def release_kinds(name):
    """The release kinds a unit's `held` readings are needed for (a
    control, `unit+switch`, those of its unit)."""
    return {RELEASE: rules.ORDINARY_RELEASE,
            EXT: rules.EXT_RELEASE}.get(name.split("+")[0], ())


def held_gap(name, summaries):
    """The release kinds of unit `name` for which no process of the group
    has a comparable `held` reading (the sensitivity requirement has
    nothing to look at: a redraw, never a result)."""
    return [k for k in release_kinds(name)
            if not any(p["held_comparable"][k] for p in summaries)]


def summary_of(report, planned, receipt):
    """The summary of a process that is a measurement (accepted, not an
    expected rejection), else None."""
    if not receipt["accepted"] or planned["expect"]:
        return None
    return summarize(receipt, report["units"][planned["unit"]],
                     report["roots"][planned["side"]])


def redraw_reason(report, planned, receipt, summary, prior, last):
    """None, or why this try of a plan position is redrawn (the same
    function a run and its replay apply). A redraw happens only when every
    other admission check passed on the receipt:
    - the output is not comparable (`incomparable`);
    - an anchor moved in the process (either side);
    - at the last position of a (unit, side), no process of the group
      (`prior`: the summaries of the earlier positions, `summary` this
      try) has a comparable `held` reading of a release kind.
    Raises the Refusal/Blocked of an admission check the receipt also
    fails."""
    if planned["expect"]:
        return None
    side = planned["side"]
    if not receipt["accepted"]:
        root, probe_dir = report["roots"][side], report["reporter"][side][
            "dir"]
        reason = incomparable(receipt, report["units"][planned["unit"]],
                              root, probe_dir)
        if reason is not None:
            d.validate(receipt, report["units"][planned["unit"]],
                       Path(root), probe_dir, None, side == "cand")
        return reason
    if summary.get("anchor_moved"):
        return "an anchor moved: %s" % (summary["anchor_moved"],)
    if last:
        gap = held_gap(planned["unit"], prior + [summary])
        if gap:
            return "no comparable held reading of %s" % ", ".join(gap)
    return None


def last_positions(plan):
    """For each position of the plan, whether it is the last of its
    (unit, side)."""
    final = {(p["unit"], p["side"]): i for i, p in enumerate(plan)}
    return [final[(p["unit"], p["side"])] == i for i, p in enumerate(plan)]


def refuse_try(report, entry, receipt, error=None):
    """The refusal of a process that is not admitted (and not a redraw);
    a finding about the candidate also marks the report blocked."""
    blocked = receipt.get("blocked") or isinstance(error, d.Blocked)
    reason = str(error) if error else receipt["rejection"]
    if blocked:
        report["blocked"] = reason
    return d.Refusal("process rejected: %s: %s" % (label_of(entry), reason))


def body(args, spec, report, sides, scratch, fds, verify, journal):
    """The processes of a stage, in the plan's order (`d.run_stage`'s
    `body_fn`), a position redrawn while `redraw_reason` says so, at most
    MAX_REDRAWS times."""
    ctx = d.prepare(args, report, sides, scratch, fds, verify, journal,
                    modules=lambda side: probe_modules(report, side))
    check_lengths(report)
    report["manifest_file"] = str(Path(args.manifest).resolve())
    report["heap_bytes"] = heap_bytes(report, a.load(args.manifest))
    loaded, finals = [], {}
    for planned, last in zip(report["plan"], last_positions(report["plan"])):
        unit = report["units"][planned["unit"]]
        prior = finals.setdefault((planned["unit"], planned["side"]), [])
        for redraw in range(MAX_REDRAWS + 1):
            entry, receipt = run_item(ctx, report, planned, unit, redraw,
                                      report["references"])
            report["runs"].append(entry)
            summary = None
            try:
                summary = summary_of(report, planned, receipt)
                reason = redraw_reason(report, planned, receipt, summary,
                                       prior, last)
            except d.Refusal as error:
                if receipt["accepted"]:
                    raise
                raise refuse_try(report, entry, receipt, error)
            if reason is None or redraw == MAX_REDRAWS:
                break
            entry["superseded"] = reason  # the receipt stays, flagged
        if not receipt["accepted"] and planned["expect"] != "reject":
            raise refuse_try(report, entry, receipt)
        if reason is not None and not (
                summary is not None and summary.get("anchor_moved") and
                planned["side"] == "cand"):
            raise d.Refusal("%s still a redraw after %d: %s" % (
                label_of(entry), MAX_REDRAWS, reason))
        loaded.append((entry, receipt))
        if summary is not None:
            prior.append(summary)
    if verify is not None:
        report["verify"]["after"] = d.run_verify(verify, report["repo"],
                                                 fds)
    report["outcome"] = outcome(report, loaded)


def audit_body(args, spec, report, sides, scratch, fds, verify, journal):
    """The api-audit stage: run.py of the candidate snapshot, its receipt
    (and logs) under the stage's output, sealed in the report. run.py
    itself is not among the driver's code seals: it is a file of the
    candidate snapshot, which the snapshot manifest (verified before and
    after the stage) covers."""
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
    # the execution is the stage's one measuring entry: a refused audit
    # is a judged attempt, not a void one (`d.judged_because`)
    receipt = dict(report["audit"], accepted=True, phase="candidate",
                   workload=AUDIT_UNIT, side="cand", pair=0,
                   selection="candidate", rep=0)
    report["runs"].append(dict(
        workload=AUDIT_UNIT, phase="candidate", pair=0,
        selection="candidate", rep=0, side="cand", redraw=0, expect=None,
        superseded=None, accepted=True,
        **d.archive(Path(report["output"]), AUDIT_UNIT, receipt)))
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
    order; an anchor moved on a baseline process (after the redraws) is a
    refusal (a harness fault, design 8.5)."""
    groups = {}
    for entry, receipt in loaded:
        if not receipt["accepted"]:
            continue
        unit = report["units"][entry["workload"]]
        side = entry["side"]
        summary = summarize(receipt, unit, report["roots"][side])
        if side == "base" and summary.get("anchor_moved"):
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
    out["reported"]["heap_bytes"] = report["heap_bytes"]
    out["owed"] = [list(x) for x in sorted({
        (r["owed"], u) for r in stage_rows(report, out["results"]).values()
        if r["owed"] for u in row_units(r)})]
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


def object_cpu(procs, m):
    """CPU seconds per released object of the pilot's release processes:
    the median whole-process CPU over the objects of all the kinds the
    process releases (an upper bound: the start-up counts)."""
    return statistics.median(cpu_of(procs)) / (
        m * len(records.RELEASE_KINDS))


def ext_object_cpu(smoke):
    """CPU seconds per released object of the smoke's extension process
    (its one candidate process; the start-up and the graph at the smoke's
    sizes count). An upper bound of the per-object cost at the decision M
    only while the graph's cost at the decision sizes stays under about
    (M / smoke M - 1) times the start-up (likely, not checked); a
    pessimistic cost only makes `capped` likelier."""
    cpu = smoke["outcome"]["times"][EXT]["cand"]["cpu"]
    return cpu / (smoke["params"]["m"] * len(records.EXT_RELEASE_KINDS))


def cap_of(cost, ext_cost, m0, factor=1):
    """The most objects per release kind whose release process (at `cost`
    CPU seconds per object) and extension process (at `ext_cost`) both fit
    `factor` times RELEASE_BUDGET_S, never under the pilot's own M0."""
    check_budget()
    require(cost > 0 and ext_cost > 0, "a release process reports no CPU "
            "time (%s, %s s per object): the cap cannot be sized" % (
                cost, ext_cost))
    return max(m0, min(math.floor(Fraction(RELEASE_BUDGET_S * factor) /
                                  Fraction(c)) for c in (cost, ext_cost)))


def pilot_outcome(report, groups):
    """Graph repeatability, the release noise and the M it needs: the
    required M (the noise in words over the resolution, taking the noise
    as independent of M), clamped to the cap the budget gives (never a
    refusal over the cap: `required` and `capped` say what the clamp did).
    The extension process's CPU per object is the smoke's, linked in
    `report["smoke"]`."""
    graph, release = groups[GRAPH]["base"], groups[RELEASE]["base"]
    repeat = {g: all(rules.constant([p["graph"][g][n]["canon_words"]
                                     for p in graph])
                     for n in graph[0]["graph"][g]) for g in
              rules.GRAPH_GATED}
    # The noise is the range of the exact residuals only: a share-pass
    # lower bound is not a reading of the noise (task33_records, "Release
    # readings and share passes"). A kind with no exact residual in the
    # group cannot be sized.
    noise, bounds = {}, {}
    for kind in records.RELEASE_KINDS:
        exact = [p["release"][kind]["after"] - p["release"][kind]["before"]
                 for p in release if not p["residual_bound"][kind]]
        require(exact, "the pilot's release processes have only GC "
                "share-pass bounds for %s: its noise cannot be sized" %
                kind)
        noise[kind] = max(exact) - min(exact)
        count = sum(p["residual_bound"][kind] for p in release)
        if count:
            bounds[kind] = count
    worst = max(noise.values())
    m0 = report["params"]["m"]
    required = max(m0, math.ceil(Fraction(worst) / rules.RESOLUTION))
    cost = object_cpu(release, m0)
    ext_cost = report["smoke"]["object_cpu"]
    cap = cap_of(cost, ext_cost, m0)
    # reported only: the least held size over the comparable readings (a
    # share-pass lower bound >= H_MIN counts), None when there is none
    held = {}
    for k in rules.ORDINARY_RELEASE:
        seen = [p["held"][k] for p in release if p["held_comparable"][k]]
        held[k] = rules.num(min(seen)) if seen else None
    return dict(
        graph_repeatable=repeat, noise_words=noise, bounds=bounds, m0=m0,
        required_m=required, m=min(cap, required), m_cap=cap,
        capped=required > cap, budget_s=RELEASE_BUDGET_S, object_cpu=cost,
        ext_object_cpu=ext_cost,
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
            rows = refusing(rules.r1_rows, base, cand)
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


def refusing(rule, *args):
    """`rule(*args)`; `rules.Inadmissible` (data that violates an admission
    condition the rule relies on) becomes a refusal. Nothing else is
    caught: a Blocked, a Refusal or a programming error propagates."""
    try:
        return rule(*args)
    except rules.Inadmissible as error:
        raise d.Refusal(str(error))


def decide(report, groups, paired):
    """({key: row} of the gated decisions, {key: row} of the reported
    ones) of a decision stage. The stage's units decide their own cases;
    E2 (a) and (c) need the ordinary candidate's `graph` and
    `registry-state-empty` and are decided where both ran. A contingency
    stage decides only the rows its parent owed it (`report["decides"]`:
    the keys); every other row keeps the parent's decision, however the
    stage's processes would have decided it."""
    names = report["workloads"]
    decides = report["decides"]
    declared = offline.load_declared()
    deltas = rules.total_deltas(declared)

    def masked(side, path):
        return d.mask_path(path, report["roots"][side],
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
            found.append(refusing(
                lambda: rules.s2_kind(base, cand, kind, rules.declared_delta(
                    deltas, heap, kind) if all(rules.applicable(
                        base + cand)) else None, paired)))
        elif name == GRAPH:
            found += [rules.s1_kind(base, cand, g, paired)
                      for g in rules.GRAPH_GATED]
        elif name == RELEASE:
            found += refusing(rules.r1_rows, base, cand)
        elif name == EXT:
            found.append(rules.e1_ext(cand))
            found.append(refusing(rules.e2b, cand))
            ordinary = groups.get(GRAPH, {}).get("cand")
            if ordinary:
                found.append(rules.e2a(cand, ordinary, paired))
            plain = groups.get(REGISTRY_PLAIN, {}).get("cand")
            if plain:
                found.append(rules.e2c(cand, plain, declared["e2c"]))
                found.append(rules.e2u(cand, plain))
    found.append(rules.s4_row())
    gated, reported = {}, {}
    for r in found:
        key = rules.key_of(r["case"], r["kind"])
        if r["decision"] not in rules.GATES:
            reported[key] = r
        elif decides is None or key in decides:
            gated[key] = r
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
        "pilot": spec.get("pilot"), "smoke": spec.get("smoke"),
        "decides": spec.get("decides"), "declared": a.seal(offline.DECLARED),
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
        require(incomparable(receipt, unit, root, reporter["dir"])
                is not None, "a rejected process that is not a redraw: " +
                entry["receipt"])
    return receipt


def tries_by_position(report):
    """The runs grouped by plan position: the first try (redraw 0) and its
    redraws."""
    groups = []
    for e in report["runs"]:
        if e["redraw"] == 0:
            groups.append([e])
        else:
            require(groups, "a redraw before any process")
            groups[-1].append(e)
    return groups


def check_plan(report):
    """The runs are the plan's, in order, each position's tries the same
    (workload, side, pair, selection) with consecutive redraw numbers,
    every try but the last one superseded (the reason is recomputed by
    `check_redraws`), and the plan is the stage's own for the units and
    parameters. Returns the tries by position."""
    stage = report["stage"] or report["mode"]
    require(report["plan"] == plan_for(stage, report["workloads"],
                                       report["params"]),
            "the plan is not the stage's")
    groups = tries_by_position(report)
    require(len(groups) == len(report["plan"]),
            "missing, extra or reordered processes")
    for tries, p in zip(groups, report["plan"]):
        require(all((e["workload"], e["side"], e["pair"], e["selection"],
                     e["expect"]) == (p["unit"], p["side"], p["pair"],
                                      p["selection"], p["expect"])
                    for e in tries), "missing, extra or reordered "
                "processes")
        require([e["redraw"] for e in tries] == list(range(len(tries))) and
                len(tries) <= MAX_REDRAWS + 1,
                "redraws are not consecutive or too many: " + p["unit"])
        require(all(e["superseded"] for e in tries[:-1]) and
                not tries[-1]["superseded"],
                "a redrawn try that is not superseded, or the last one is")
    return groups


def check_redraws(report, groups, receipts):
    """Every superseded try is a redraw by `redraw_reason`, recomputed from
    the receipts; the last try of a position is redrawn no longer only
    when the redraws ran out (and a redraw that persists is an anchor that
    moved on the candidate). Returns the final tries [(entry, receipt)]."""
    loaded, finals = [], {}
    lasts = last_positions(report["plan"])
    for tries, p, last in zip(groups, report["plan"], lasts):
        prior = finals.setdefault((p["unit"], p["side"]), [])
        for i, e in enumerate(tries):
            receipt = receipts[e["receipt"]]
            summary = summary_of(report, p, receipt)
            reason = redraw_reason(report, p, receipt, summary, prior, last)
            if i + 1 < len(tries):
                require(reason is not None and e["superseded"] == reason,
                        "a superseded try that is not a redraw: " +
                        e["receipt"])
        require(reason is None or (len(tries) == MAX_REDRAWS + 1 and
                                   summary is not None and
                                   summary.get("anchor_moved") and
                                   p["side"] == "cand"),
                "a try that should have been redrawn: " + e["receipt"])
        loaded.append((e, receipt))
        if summary is not None:
            prior.append(summary)
    return loaded


def check_audit_entry(folder, report):
    """The audit stage's one measuring entry is the sealed receipt of the
    execution the report records."""
    runs = report["runs"]
    require(len(runs) == 1 and runs[0]["workload"] == AUDIT_UNIT and
            runs[0]["accepted"] is True, "the audit stage has not its one "
            "measuring entry")
    path = a.safe_child(folder, runs[0]["receipt"])
    require(a.seal(path) == runs[0]["seal"], "changed audit entry")
    receipt = a.load(path)
    require(all(receipt[k] == v for k, v in report["audit"].items() if k in
                ("command", "exit", "stdout_sha256", "output")),
            "the audit entry is not the recorded execution")


def smoke_link(info, smoke):
    """What a pilot records of the smoke that sized it: the run and the
    CPU per object of its extension process."""
    return dict(attempt=smoke["attempt"], seal=info["seal"],
                object_cpu=ext_object_cpu(smoke))


def decision_params(pilot):
    """The configuration of the decision runs (and of the controls): the
    pilot's sizes and its M, clamped."""
    out = pilot["outcome"]
    return dict(sizes=pilot["params"]["sizes"], m=out["m"], k=K)


def check_heap_bytes(report, manifest=None):
    """The saved-state sizes the stage reports are the sealed manifest's:
    the manifest file (`manifest`, else the one the stage recorded) must be
    the one whose seal the stage bound, and its products give the bytes."""
    path = Path(manifest or report["manifest_file"])
    require(path.is_file() and a.seal(path) == report["manifest"],
            "the snapshot manifest %s is not the one the stage used" % path)
    require(report["heap_bytes"] == jsonable(heap_bytes(report,
                                                        a.load(path))),
            "the stage's heap bytes are not the sealed manifest's")


def replay_one(folder, ledger=None, repo=None, counts=None,
               timing_counts=None, manifest=None):
    """Recompute every observation, check and decision of one finished
    storage stage from its archived receipts (no process runs). Returns
    (info, report). `manifest` is the snapshot manifest file when it moved
    from where the stage recorded it."""
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
            "the declaration changed since the %s run: it is sealed "
            "before the smoke, the pilot and the controls" % mode)
    require((report["decides"] is None) ==
            (mode not in ("extend", "followup")), "malformed run")
    if mode in DECISIVE:
        require(all(report["verify"][k]["exit"] == 0
                    for k in ("before", "after")),
                "a decision stage ran without the snapshot verification")
    if mode != "audit":
        d.check_probe_sources(report)
        check_heap_bytes(report, manifest)
        groups = check_plan(report)
        receipts = {e["receipt"]: check_run(folder, report, e)
                    for e in report["runs"]}
        loaded = check_redraws(report, groups, receipts)
    else:
        check_audit_entry(folder, report)
        loaded = []
    require(d.same(outcome(report, loaded, folder), report["outcome"]),
            "recomputed outcome differs from the report")
    info = dict(replayed=len(report["runs"]), mode=mode, stage=stage,
                seal=seal)
    if mode in DECISIVE:
        info["exit"] = d.stage_status(report["outcome"]["results"])
        info["attempts"] = d.check_ledger(
            ledger or d.ledger_path(report["repo"]), report, seal,
            info["exit"], LEDGER_TABLE)
        check_counts_use(report, counts, repo, timing_counts)
    return info, report


def check_counts_use(report, path, repo, timing_path=None):
    """The stage used this counts file: its seal, the values it declares
    (the parameters and the references), the sizing of M, the timing
    counts it binds (their seal is the timing chain's counts file's) and
    the commit rule where the repository is at hand."""
    used = report["counts"]
    stage = report["stage"]
    file = Path(path or (FOLLOWUP_COUNTS if stage == "followup" else
                         STORAGE_COUNTS))
    require(used is not None and file.is_file() and
            a.seal(file) == used["seal"],
            "the counts file is not the one the stage used: %s" % file)
    data = a.load(file)
    d.check_code(data["code"])
    check_timing_seal(data, timing_path)
    check_sizing(data)
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


def check_timing_seal(data, timing_path=None):
    """The storage counts bind the timing chain's counts file: its seal is
    the one recorded."""
    path = Path(timing_path or d.COUNTS)
    require(path.is_file() and data["timing_counts"]["seal"] ==
            a.seal(path), "the storage counts were made with other timing "
            "counts than %s" % path)


def check_sizing(data):
    """M is what the budget, the CPU per object of the release processes
    and of the extension process, and the noise give: min(cap, required),
    `capped` and, for a follow-up, `required`
    from the base M and the floor range of the rows that owe it."""
    kind = data["kind"]
    factor = 1 if kind == "run" else FOLLOWUP_FACTOR
    cap = cap_of(data["object_cpu"], data["ext_object_cpu"], data["m0"],
                 factor)
    required = data["required_m"]
    if kind == "followup":
        required = max(FOLLOWUP_FACTOR * data["base_m"], math.ceil(
            data["base_m"] * Fraction(str(data["floor_range"])) /
            rules.RESOLUTION))
        require(required == data["required_m"], "the follow-up counts' "
                "required M is not the base M scaled by the floor range")
    want = data["decision"] if kind == "run" else data["followup"]
    require(data["budget_s"] == RELEASE_BUDGET_S and data["m_cap"] == cap
            and want["k"] == K and want["m"] == min(cap, required)
            and data["capped"] == (required > cap),
            "the counts file's budget, cap, M, required_m and capped "
            "disagree")


def parents(report):
    return report.get("first_stage") or report.get("replaces")


def replay_chain(folder, ledger=None, repo=None, counts=None,
                 followup_counts=None, timing_counts=None, manifest=None):
    """The stage chain ending in `folder`: [{stage, report, info, folder}].
    A contingency stage (extend, followup) names its parent run, which is
    replayed and tied to it (same gate, manifest, units owed)."""
    folder = Path(folder).resolve(strict=True)
    stage = a.load(folder / "downstream.json")["stage"]
    info, report = replay_one(folder, ledger, repo, followup_counts if
                              stage == "followup" else counts,
                              timing_counts, manifest)
    here = dict(stage=report["stage"], report=report, info=info,
                folder=folder)
    link = parents(report)
    if link is None:
        return [here]
    parent = replay_chain(link["run"], ledger, repo, counts,
                          followup_counts, timing_counts, manifest)
    last = parent[-1]
    require(a.seal(Path(link["run"]) / "downstream.json") == link["seal"]
            and link["attempt"] == last["report"]["attempt"]
            and link.get("stages") == [e["stage"] for e in parent],
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
    require(report["decides"] == owed_keys(parent, kind), "the %s stage "
            "does not decide exactly the rows owed it" % report["stage"])
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


def settle(rows, ran):
    """`rows` ({key: row}) after the stages `ran` (names, in order) with
    the stages still to come taken into account: a row is owed
    (inconclusive, `owed` the stage) only while that contingency stage
    ("extend", "followup") has not run (each is run once); an inconclusive
    row owed no stage that may still run is blocked (the TASK32
    convention); every other row owes nothing."""
    out = {}
    for key, r in rows.items():
        if r["decision"] != rules.INCONCLUSIVE:
            r = dict(r, owed=None)
        elif not (r["owed"] and r["owed"] not in ran):
            r = dict(r, decision=rules.BLOCKED, owed=None, reason=(
                "%s: still inconclusive after the last allowed stage%s" % (
                    r["reason"], " (%s ran)" % r["owed"] if r["owed"]
                    else "")))
        out[key] = r
    return out


def settled_rows(chain):
    """`settle` of the chain's final rows (`final_rows`)."""
    return settle(final_rows(chain), [e["stage"] for e in chain])


def stage_rows(report, results):
    """The `results` of a stage, settled by the stages that ran up to and
    including it (the parent chain's names are in its link): what the
    stage prints and records as owed, as the disposition settles it."""
    link = parents(report) or {}
    return settle(results, link.get("stages", []) + [report["stage"]])


def owed_rows(chain, kind):
    """The rows owed `kind` ("extend" or "followup") after the chain."""
    return [r for r in settled_rows(chain).values() if r["owed"] == kind]


def owed_keys(chain, kind):
    """The keys of the rows owed `kind`: what that stage decides."""
    return sorted(rules.key_of(r["case"], r["kind"])
                  for r in owed_rows(chain, kind))


def owed_units(chain, kind):
    """The units whose measurements the rows owed `kind` need."""
    needed = {u for r in owed_rows(chain, kind) for u in row_units(r)}
    return [u for u in UNITS if u in needed]


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


def load_storage_counts(path, sides, kind, repo, mseal, timing_path,
                        committed=True):
    """A storage counts file, checked against this gate: schema, pins,
    manifest, the code and declaration it is bound to, the timing counts'
    seal it binds, the sizing of M (`check_sizing`) and the commit rule."""
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
    check_timing_seal(data, timing_path)
    check_sizing(data)
    if committed:
        data["commit"] = d.check_counts_commit(repo, path,
                                               sides["cand"]["pin"])
    return data


def info_run(folder, key, mode, names, ledger, mseal, manifest=None):
    """A replayed information run of this gate (the storage driver's own
    replay, the timing driver's checks); `manifest` is the snapshot
    manifest file when it moved."""
    info, report = replay_one(folder, ledger=ledger, manifest=manifest)
    d.check_info_run(info, report, key, mode, ledger, names, mseal,
                     LEDGER_TABLE)
    return info, report


def offline_seals(paths):
    """The seals of the three S3 reports (OFFLINE_COMMANDS), each checked
    as `dispose` checks them: its schema, its seal file and the code it was
    made by."""
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
    require(set(found) == set(OFFLINE_COMMANDS), "the S3 reports (--offline) "
            "are %s, not exactly %s" % (sorted(found),
                                        sorted(OFFLINE_COMMANDS)))
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
                                 list(PILOT_UNITS), args.ledger, mseal,
                                 args.manifest)
    smoke_info, smoke = info_run(args.smoke, key, "smoke", list(UNITS),
                                 args.ledger, mseal, args.manifest)
    require(pilot["smoke"] == smoke_link(smoke_info, smoke),
            "the pilot was sized from another smoke")
    control_info, control = info_run(args.control, key, "control",
                                     control_names(), args.ledger, mseal,
                                     args.manifest)
    out = pilot["outcome"]
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
    wall = dict(pilot["outcome"]["median_wall"])
    scale = Fraction(decision["m"], out["m0"])
    # the release process scales with M (an upper bound: start-up
    # counts); the extension probe is a graph and a release process
    wall[EXT] = (wall[RELEASE] * float(scale) + wall[GRAPH])
    wall[RELEASE] = wall[RELEASE] * float(scale)
    estimate = dict(per_process_wall=wall, m=decision["m"], processes=dict(
        run=2 * K * (len(REGISTRY) + len(TRIVIAL) + 2) + K,
        extend=2 * EXTEND_PAIRS), verify_seconds=sum(
            v["seconds"] for v in (smoke.get("verify") or {}).values()))
    return {
        "schema": COUNTS_SCHEMA, "kind": "run", "base": pilot["base"],
        "cand": pilot["cand"], "manifest": mseal, "seed": SEED,
        "seeds": SEEDS, "decision": decision, "m0": out["m0"],
        "required_m": out["required_m"], "m_cap": out["m_cap"],
        "capped": out["capped"], "budget_s": out["budget_s"],
        "object_cpu": out["object_cpu"],
        "ext_object_cpu": out["ext_object_cpu"],
        "resolution": out["resolution"],
        "contingencies": dict(
            extend=dict(pairs=EXTEND_PAIRS, rule="paired_statistics at "
                        "zero margin, for a unit whose value is not "
                        "repeatable within a side"),
            followup=dict(rule="R1 / E2 (b) at max(M x %d, M x floor "
                          "range / %s), capped by %d times the budget, "
                          "counts committed alone" % (
                              FOLLOWUP_FACTOR, rules.RESOLUTION,
                              FOLLOWUP_FACTOR))),
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


def floor_range_of(r):
    """The no-op floor's range (a Fraction) of an R1 row, or the widest of
    an E2 (b) row's kinds."""
    rows = r["kinds"].values() if "kinds" in r else [r]
    return max(Fraction(str(x["floor_range"])) for x in rows)


def predeclare_followup(args):
    """The counts file of a follow-up: the units owed it after the chain
    ending in --stage, at M = max(M x FOLLOWUP_FACTOR, M x floor range /
    resolution) (capped by FOLLOWUP_FACTOR times the budget; `required_m`
    and `capped` recorded as the first counts do)."""
    sides, mseal = d.pins_of(args)
    timing_path = table_counts_path(args).resolve(strict=True)
    run_counts = load_storage_counts(
        storage_counts_path(args).resolve(strict=True), sides, "run",
        args.repo, mseal, timing_path, committed=False)
    chain = replay_chain(args.stage, args.ledger, args.repo,
                         args.storage_counts, args.followup_counts,
                         args.timing_counts, args.manifest)
    owed = owed_units(chain, "followup")
    require(owed, "no unit is owed a follow-up")
    first = chain[0]["report"]
    base_m = first["params"]["m"]
    floor = max(floor_range_of(r) for r in owed_rows(chain, "followup"))
    required = max(FOLLOWUP_FACTOR * base_m,
                   math.ceil(base_m * floor / rules.RESOLUTION))
    cap = cap_of(run_counts["object_cpu"], run_counts["ext_object_cpu"],
                 run_counts["m0"], FOLLOWUP_FACTOR)
    return {
        "schema": COUNTS_SCHEMA, "kind": "followup", "base": first["base"],
        "cand": first["cand"], "manifest": mseal, "seed": SEEDS[
            "followup"], "workloads": owed, "required_m": required,
        "base_m": base_m, "floor_range": rules.num(floor),
        "m0": run_counts["m0"], "object_cpu": run_counts["object_cpu"],
        "ext_object_cpu": run_counts["ext_object_cpu"],
        "budget_s": RELEASE_BUDGET_S, "m_cap": cap,
        "capped": required > cap,
        "followup": dict(sizes=first["params"]["sizes"],
                         m=min(cap, required), k=K),
        "references": first["references"],
        "timing_counts": run_counts["timing_counts"],
        "replaces": dict(run=str(chain[-1]["folder"]),
                         attempt=chain[-1]["report"]["attempt"],
                         seal=chain[-1]["info"]["seal"]),
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
        info, smoke = info_run(args.smoke, key, "smoke", list(UNITS), None,
                               mseal, args.manifest)
        require(smoke["outcome"]["facts"]["ok"], "--smoke did not pass the "
                "probe facts")
        return spec_of(mode, list(PILOT_UNITS), dict(
            sizes=list(sizes), m=args.m0 or M0, k=K),
            smoke=smoke_link(info, smoke))
    info, pilot = info_run(args.pilot, key, "pilot", list(PILOT_UNITS),
                           None, mseal, args.manifest)
    return spec_of(mode, control_names(), decision_params(pilot),
                   pilot=dict(attempt=pilot["attempt"], seal=info["seal"]))


def counts_spec(args, stage, followup=False):
    sides, mseal = d.pins_of(args)
    path = storage_counts_path(args, followup).resolve(strict=True)
    counts = load_storage_counts(path, sides, "followup" if followup else
                                 "run", args.repo, mseal,
                                 table_counts_path(args))
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
                seal=last["info"]["seal"],
                stages=[e["stage"] for e in chain])


def extend_spec(args):
    sides, counts, use = counts_spec(args, "extend")
    chain = replay_chain(args.first, None, args.repo, args.storage_counts,
                         args.followup_counts, args.timing_counts,
                         args.manifest)
    owed = owed_units(chain, "extend")
    require(owed, "no unit is owed the %d-pair stage" % EXTEND_PAIRS)
    return spec_of("extend", owed, dict(
        counts["decision"], pairs=EXTEND_PAIRS), counts=use,
        first=link_of(chain), references=counts["references"],
        decides=owed_keys(chain, "extend"))


def followup_spec(args):
    sides, counts, use = counts_spec(args, "followup", True)
    chain = replay_chain(args.stage, None, args.repo, args.storage_counts,
                         args.followup_counts, args.timing_counts,
                         args.manifest)
    owed = owed_units(chain, "followup")
    require(owed and owed == counts["workloads"], "the follow-up counts "
            "are not of the units owed: %s" % owed)
    return spec_of("followup", owed, counts["followup"], counts=use,
                   replaces=link_of(chain),
                   references=counts["references"],
                   decides=owed_keys(chain, "followup"))


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
        return 0
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
            for k, r in sorted(stage_rows(report, out["results"]).items()))
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
    cmd["pilot"].add_argument("--smoke", type=Path, required=True,
                              help="the smoke run (its extension "
                              "process's CPU per object caps M)")
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
    rep.add_argument("--timing-counts", type=Path)
    rep.add_argument("--manifest", type=Path, help="the snapshot manifest "
                     "(default: where the stages recorded it)")
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
    dis.add_argument("--manifest", type=Path, help="the snapshot manifest "
                     "(default: where the stages recorded it)")
    dis.add_argument("--storage-counts", type=Path)
    dis.add_argument("--timing-followup-counts", type=Path)
    dis.add_argument("--storage-followup-counts", type=Path)
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
    snaps.add_argument("--scratch-root", type=Path, default=SCRATCH_ROOT,
                       help="must be the declared %s" % SCRATCH_ROOT)
    return parser


def dispatch(args):
    command = args.command
    if command in RUN_COMMANDS:
        check_budget(args.timeout)
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
                args.followup_counts, args.timing_counts,
                args.manifest)[-1]["info"],
                sort_keys=True))
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
