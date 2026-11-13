#!/usr/bin/env python3
"""The TASK37 disposition: one decision for every required workload.

TASK37 reruns the final performance gate at the final candidate. This
command joins what the measurement stages produced into ONE disposition
(`disposition.json`, with a short `SUMMARY.txt`), the way `task31_dispose.py`
joins TASK31's three gates. Every input is named by an explicit path
option: nothing is looked up in the repository, and the streams of the
measurement may live in different clones (each timing table has its own
ledger). A missing input is a refusal, never a pass.

TASK37 protocol (the decision rule is design decision 11)
---------------------------------------------------------

Cells. The matrix (every MatrixPerformance case at every size: the TASK29
and TASK30 families, 306 cells), the client cells (the TASK31 cells, 278)
and the downstream cells (11): `task37_cases.py`. A cell passes if and only
if

- identity: its row in the identity table of its kind is `identical` or
  `attributed` (`different` fails; anything else is not a decision);
- allocation: the allocation task of its kind decided `pass` with a work
  row `equal`, from at least the task's own number of pairs (taken from the
  task's inventory, never a constant here);
- timing, where the cell is sampled: the timing table decided `pass`.

An unsampled cell passes on identity and exact allocation (the stratified
policy the user approved for TASK31 and extended to the matrix, design
"Scope"); it is recorded with policy `stratified`. A timing row outside the
expected sample is a refusal. Sampled sets: `task37_cases.CLIENT_SAMPLE` and
`MATRIX_SAMPLE`.

Policies carried over, each recorded on the cell:

- D2: the 33 heavy size-10000 tactic cells (`task31_cases.INFEASIBLE`) are
  identity-only; an attributed one also needs its family's measured cells
  (an allocation cell of at most 1000 assumptions that passed with an
  attributed identity, and a passing timing cell of the sample).
- D4: the thirteen cells of `task30_dispose.DISPOSITION["attributed"]` get
  a fresh decision. The only carry-over: a timing chain whose decisive first
  stage is control-limited is not owed a second stage; the cell is then a
  pass with policy `D4` (its identity and exact allocation still required).
  A pass or a fail of any stage decides as for any cell.
- R-1: every attempt of a timing table in its ledger is judged or void
  (`void_attempts.attempts_of`, through the table's engine in
  `task37_grid.ENGINES`); the attempts are recorded.

Inconclusive never passes. A cell with no decision is `incomplete`, and
what is owed is listed explicitly on it (`stage2`, `followup`,
`attribution`, `redraw`) and in the top-level `owed`. A control-limited or
inconclusive cell with no stage left is `blocked` (still incomplete, owing
an attribution).

Timing inputs (per table `task37-client`, `task37-matrix`): the final stage
directory (`inventory.json`, `decisions.json` of timing_grid; an extension
names its first stage by `grid`, whose seals it carries and which is read
too) and optionally follow-up directories whose cells replace the table's
for those cells. The counts file the inventory names must be the committed
one: `counts_file` is the table's file and `iterations_seal` its seal now
(a stale counts file is refused). Host-load data the inventory carries
(`environment`, `host_load`, `loadavg`) is copied, reported only.

Other inputs. Identity tables: `task31_identity_grid` for the client cells,
`task37_matrix_identity` (`task37-matrix-identity`,
`task37-downstream-identity`), each a directory with `inventory.json` and
`decisions.json`. Allocation: three `allocation_matrix` outputs
(`task37-matrix`, `task37-client`, `task37-downstream`). TASK32: the
disposition of `task32_downstream.py` (15 units; `followup` and
`second stage owed` rows are owed, other blocked rows are blocked). TASK33:
`task33_dispose.py`'s `disposition.json` (every expected storage decision
present; its `owed`, `reported`, `attribution_needed` and `process_redraws`
are carried). Both must carry the `candidate` they were measured at. The
startup gate and the two loading gates are receipts (`receipt` below), and
the D7 build timing receipt is reported only, never a gate.

Commands

    task37_dispose.py --candidate REV --identity-client DIR
        --identity-matrix DIR --identity-downstream DIR
        --alloc-matrix DIR --alloc-client DIR --alloc-downstream DIR
        --timing-client DIR [--followup-client DIR ...] --ledger-client F
        --timing-matrix DIR [--followup-matrix DIR ...] --ledger-matrix F
        --task32 FILE --task33 FILE --startup-gate FILE
        --loading-simplib FILE --loading-conglib FILE [--d7-build FILE]
        (--record OUTDIR | --check OUTDIR)
    task37_dispose.py receipt --gate NAME --candidate REV --status S
        --exit N --out FILE [--report FILE ...] [--attribution TEXT ...]

`--record` writes OUTDIR/disposition.json and OUTDIR/SUMMARY.txt (OUTDIR
must be new). `--check` derives the decisions again from the inputs and
requires that OUTDIR/disposition.json is the same. Seals cover the code
(`CODE`, with `HISTORY` for earlier versions a record was made by) and every
input file. The exit status is 0 when every workload passes, 1 when one
fails, 2 when some is incomplete, 3 when the command is refused. The last
line printed is the verdict.

Unsupported: aarch64 Linux only, Poly/ML 5.9.2, allocation only with the
private counter, RSS reported only (recorded as `scope`).
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task37_cases as cases
import timing_grid as tg
from void_attempts import attempts_of

SCHEMA = "task37-disposition-v1"
RECEIPT_SCHEMA = "task37-receipt-v1"
SCOPE = ("aarch64 Linux only; Poly/ML 5.9.2; allocation only with the "
         "private counter; RSS reported only")
GATES = ("startup-gate", "loading-simpLib", "loading-congLib")
D7 = "d7-build"
RECEIPT_STATUS = ("pass", "attributed", "fail", "inconclusive")
COUNTS = {"task37-client": "task37_client_iterations.json",
          "task37-matrix": "task37_matrix_iterations.json"}
# Where the committed counts files are (tests point this elsewhere).
COUNTS_DIR = a.HERE
LOAD_KEYS = ("environment", "host_load", "loadavg")
# Every module whose decision or seal the record depends on.
CODE = ("task37_dispose.py", "task37_cases.py", "task37_matrix_identity.py",
        "task37_grid.py", "task31_identity_grid.py", "task31_cases.py",
        "task30_dispose.py", "task32_downstream.py", "task32_cases.py",
        "task33_dispose.py", "task33_rules.py", "task33_storage.py",
        "timing_grid.py", "acceptance.py", "void_attempts.py",
        "allocation_matrix.py", "allocation_schema.py",
        "allocation_analysis.py", "matrix_schema.py")
HISTORY = {}

STATUS_FAIL, STATUS_INCOMPLETE, STATUS_PASS = "fail", "incomplete", "pass"


def seals():
    return {name: a.seal(a.HERE / name) for name in CODE}


def check_code(recorded):
    """The recorded seals are those of the code now or of an earlier
    version HISTORY names; the refusal names the files and the entries."""
    now = seals()
    a.require(isinstance(recorded, dict) and set(recorded) == set(CODE),
              "changed TASK37 disposition: the recorded code is not %s"
              % ", ".join(CODE))
    changed = [n for n in CODE if recorded[n] != now[n] and
               recorded[n] not in HISTORY.get(n, ())]
    a.require(not changed, "changed TASK37 disposition: %s changed since "
              "it was recorded; add the seal it was recorded by to "
              "task37_dispose.HISTORY: %s" % (", ".join(changed), "; ".join(
                  "%s: %s" % (n, json.dumps(recorded[n], sort_keys=True))
                  for n in changed)))


def canonical(value):
    return json.dumps(value, sort_keys=True)


def same_rev(given, found):
    """Whether two revisions are the same, one possibly abbreviated (at
    least ten digits)."""
    if not (isinstance(given, str) and isinstance(found, str)):
        return False
    short, long = sorted((given, found), key=len)
    return len(short) >= 10 and long.startswith(short)


def tie(label, document, candidate, baseline=True):
    """The document is of the candidate (and of the pinned baseline)."""
    found = document.get("candidate") if isinstance(document, dict) else None
    a.require(found is not None, "%s records no candidate" % label)
    a.require(same_rev(candidate, found),
              "%s is of another candidate (%s, not %s)" % (
                  label, found, candidate))
    if baseline and "baseline" in document:
        a.require(document["baseline"] == a.BASE,
                  "%s is against another baseline (%s)" % (
                      label, document["baseline"]))
    return found


def read(path, label):
    a.require(path is not None, "no %s given" % label)
    path = Path(path)
    a.require(path.is_file(), "%s is missing: %s" % (label, path))
    return a.load(path)


# ------------------------------------------------------------- identity

IDENTITY_OK = ("identical", "attributed")


def load_identity(root, label, names, candidate):
    """The identity table of `names` in directory `root`: {cells, status,
    unaccounted, attributed, seals}."""
    root = Path(root)
    inventory = read(root / "inventory.json", label + " inventory")
    decisions = read(root / "decisions.json", label + " decisions")
    tie(label + " inventory", inventory, candidate)
    found = tie(label + " decisions", decisions, candidate)
    a.require(not decisions.get("diagnostic") and
              not inventory.get("diagnostic"),
              "%s is a diagnostic, not the whole table" % label)
    cells = decisions.get("cells")
    a.require(isinstance(cells, dict) and set(cells) == set(names),
              "%s has not exactly the cells of its kind (%d expected)" % (
                  label, len(names)))
    for name, row in cells.items():
        a.require(isinstance(row, dict) and isinstance(
            row.get("status"), str), "malformed %s row: %s" % (label, name))
    return dict(cells=cells, status=decisions.get("status"),
                unaccounted=decisions.get("unaccounted", []),
                attributed=decisions.get("attributed", []),
                candidate=found,
                seals={"inventory": a.seal(root / "inventory.json"),
                       "decisions": a.seal(root / "decisions.json")})


# ----------------------------------------------------------- allocation

WORK = ("equal", "differs", "inconclusive", None)
DECISIONS = ("pass", "fail", "inconclusive")


def load_allocation(root, task, names, infeasible, candidate):
    """{rows: {name: {decision, work, pairs}}, pairs, seals} of an
    allocation task; the pairs a passing row needs are the task's own."""
    root = Path(root)
    inventory = read(root / "inventory.json", task + " inventory")
    a.require(root.joinpath("decisions.json").is_file(),
              "the %s allocation is partial: it has no decisions" % task)
    decisions = read(root / "decisions.json", task + " decisions")
    a.require(inventory.get("task") == task,
              "the allocation grid is not a %s grid (%s)" % (
                  task, inventory.get("task")))
    tie(task + " inventory", inventory, candidate)
    tie(task + " decisions", decisions, candidate)
    pairs = inventory.get("pairs")
    a.require(isinstance(pairs, int) and not isinstance(pairs, bool) and
              pairs >= 1, "the %s inventory has no pair count" % task)
    a.require(decisions.get("complete") is True,
              "the %s allocation is not complete" % task)
    a.require(decisions.get("infeasible") == sorted(infeasible),
              "the %s infeasible cells are not the task's" % task)
    rows = {}
    for row in decisions.get("rows", []):
        a.require(isinstance(row, dict) and isinstance(row.get("case"), str)
                  and isinstance(row.get("size"), int) and
                  row.get("decision") in DECISIONS and
                  row.get("work") in WORK and
                  (isinstance(row.get("pairs"), int) or (
                      row.get("pairs") is None and
                      row.get("decision") == "inconclusive")),
                  "malformed allocation row: %r" % (row,))
        name = cases.name_of(row["case"], row["size"])
        a.require(name in names, "%s row of a cell that is not its: %s"
                  % (task, name))
        a.require(name not in rows, "repeated %s row: %s" % (task, name))
        a.require(row["decision"] != "pass" or row["pairs"] >= pairs,
                  "a passing %s row of fewer than the task's %d pairs: %s"
                  % (task, pairs, name))
        rows[name] = dict(decision=row["decision"], work=row["work"],
                          pairs=row["pairs"])
    missing = sorted(set(names) - set(rows))
    a.require(not missing, "the %s allocation has no row for: %s" % (
        task, ", ".join(missing[:5])))
    return dict(rows=rows, pairs=pairs,
                seals={"inventory": a.seal(root / "inventory.json"),
                       "decisions": a.seal(root / "decisions.json")})


# --------------------------------------------------------------- timing

def class_map(decisions):
    """({cell: class}, retained-slope class or None) of a grid decision."""
    found, scaling = {}, None
    for kind, names in tg.classify(decisions).items():
        for name in names:
            if name == "retained_scaling":
                scaling = kind
            else:
                found[name] = kind
    return found, scaling


def is_extension(inventory):
    return str(inventory.get("schema", "")).endswith("-extension-v1")


def read_stage(root, label):
    """One timing output: its inventory, its cell classes, its first
    stage's classes (read and sealed through `grid` for an extension), the
    cells its second stage remeasured, and the host-load data."""
    root = Path(root).resolve()
    inventory = read(root / "inventory.json", label + " inventory")
    decisions = read(root / "decisions.json", label + " decisions")
    final, scaling = class_map(decisions)
    first, plan, first_root = final, {}, root
    if is_extension(inventory):
        first_root = (root / inventory["grid"]).resolve()
        a.require(first_root.joinpath("decisions.json").is_file() and
                  a.seal(first_root / "inventory.json") ==
                  inventory.get("grid_inventory") and
                  a.seal(first_root / "decisions.json") ==
                  inventory.get("grid_decisions"),
                  "%s: the first stage is not the one sealed" % label)
        first, _ = class_map(a.load(first_root / "decisions.json"))
        plan = {cases.name_of(c, s): p for c, s, p in
                decisions["remeasured"]["plan"]}
    first_inventory = a.load(first_root / "inventory.json")
    load = {}
    for key in LOAD_KEYS:
        if key in first_inventory:
            load[key] = first_inventory[key]
    seal_files = [root / "inventory.json", root / "decisions.json"]
    if first_root != root:
        seal_files += [first_root / "inventory.json",
                       first_root / "decisions.json"]
    return dict(root=root, inventory=inventory,
                first_inventory=first_inventory, final=final,
                scaling=scaling, first=first, plan=plan, load=load,
                seals={str(p): a.seal(p) for p in seal_files})


def check_counts(stage, label, expected=None):
    """The counts file the stage names is the committed one, unchanged."""
    for inventory in (stage["inventory"], stage["first_inventory"]):
        name = inventory.get("counts_file")
        a.require(isinstance(name, str) and name and
                  (expected is None or name == expected),
                  "%s names the counts file %r, not %s" % (
                      label, name, expected))
        path = COUNTS_DIR / name
        a.require(path.is_file(), "%s: the counts file %s is missing"
                  % (label, path))
        a.require(a.seal(path) == inventory.get("iterations_seal"),
                  "%s: the counts file %s is not the one the grid used "
                  "(stale counts file)" % (label, name))
    return a.seal(COUNTS_DIR / stage["inventory"]["counts_file"])


def timing_engines():
    """{table name: timing engine} of `task37_grid` (`ENGINES`); a
    follow-up table is named `<table>-followup`."""
    import task37_grid
    return task37_grid.ENGINES


def judged_attempts(engine, root):
    """{attempt id: output} of a final stage of `engine`'s table and, for
    a second stage, of its first."""
    root = Path(root).resolve()
    found = a.load(root / "inventory.json")
    judged = {found["attempt"]: root}
    if is_extension(found):
        first = (root / found["grid"]).resolve()
        judged[a.load(first / "inventory.json")["attempt"]] = first
    return judged


def table_attempts(engine, root, repo, ledger):
    """Every attempt of the table in `ledger`: judged or void (R-1)."""
    return attempts_of(argparse.Namespace(repo=repo, ledger=ledger),
                       engine, judged_attempts(engine, root))


def load_timing(table, root, followups, ledger, expected, candidate, repo,
                engines):
    """The timing table: {cells: {name: row}, scaling, attempts, load,
    seals}. A cell's row: class, first (its decisive chain's first stage),
    stage2 and followup (whether they ran), earlier (the classes the
    follow-up replaced)."""
    a.require(root is not None, "no timing table %s given" % table)
    a.require(ledger is not None and Path(ledger).is_file(),
              "no attempts ledger for %s: %s" % (table, ledger))
    main = read_stage(root, table)
    tie(table + " inventory", main["inventory"], candidate)
    check_counts(main, table, COUNTS[table])
    a.require(set(main["final"]) == set(expected),
              "the %s table is not the expected sample (%d cells)" % (
                  table, len(expected)))
    rows = {n: dict(cls=c, first=main["first"][n], stage2=n in main["plan"],
                    followup=False, earlier=[])
            for n, c in main["final"].items()}
    seals = dict(main["seals"])
    load = {table: main["load"]}
    attempts = list(table_attempts(engines[table], main["root"], repo,
                                   ledger))
    for i, path in enumerate(followups):
        stage = read_stage(path, "%s follow-up %d" % (table, i + 1))
        tie("%s follow-up inventory" % table, stage["inventory"], candidate)
        check_counts(stage, "%s follow-up" % table)
        a.require(stage["final"] and set(stage["final"]) <= set(rows),
                  "a %s follow-up has cells outside the table" % table)
        a.require(stage["scaling"] is None,
                  "a %s follow-up has a retained slope" % table)
        name = table + "-followup"
        a.require(name in engines, "no engine for the %s table" % name)
        attempts += table_attempts(engines[name], stage["root"], repo,
                                   ledger)
        for n, c in stage["final"].items():
            rows[n] = dict(cls=c, first=stage["first"][n],
                           stage2=n in stage["plan"], followup=True,
                           earlier=rows[n]["earlier"] + [rows[n]["cls"]])
        seals.update(stage["seals"])
        load["%s-followup-%d" % (table, i + 1)] = stage["load"]
    seals["ledger"] = a.seal(Path(ledger))
    return dict(cells=rows, scaling=main["scaling"], attempts=attempts,
                load=load, seals=seals)


# ---------------------------------------------------- TASK32, TASK33, gates

NOTE_SECOND = "second stage owed"
T32_STATUSES = ("pass", "fail", "followup", "blocked")


def load_task32(path, candidate):
    """{unit: decision record} of a TASK32 disposition."""
    import task32_cases
    doc = read(path, "the TASK32 disposition")
    tie("the TASK32 disposition", doc, candidate, baseline=False)
    work = doc.get("workloads")
    a.require(isinstance(work, dict) and
              set(work) == set(task32_cases.NAMES),
              "the TASK32 disposition has not exactly the %d units" %
              len(task32_cases.NAMES))
    units = {}
    for unit in task32_cases.NAMES:
        row = work[unit]
        a.require(isinstance(row, dict) and
                  row.get("status") in T32_STATUSES,
                  "malformed TASK32 unit: " + unit)
        status, note = row["status"], row.get("note")
        record = dict(unit=unit, source=status, note=note, failed=[],
                      missing=[], owed=[], stages=row.get("stages"))
        if status == "fail":
            record["failed"].append("downstream timing: fail")
        elif status == "followup":
            record["missing"].append("downstream timing: inconclusive")
            record["owed"].append("followup")
        elif status == "blocked":
            record["missing"].append("downstream timing: blocked")
            record["owed"].append(
                "stage2" if note == NOTE_SECOND else "attribution")
        units[unit] = record
    worst = ("fail" if any(r["status"] == "fail" for r in work.values())
             else "pass" if all(r["status"] == "pass" for r in work.values())
             else "blocked")
    a.require(doc.get("status") == worst,
              "the TASK32 disposition's status is not that of its units")
    return units, a.seal(Path(path))


def load_task33(path, candidate):
    """The TASK33 decisions: ({key: record}, reported, carried, seal)."""
    import task33_dispose
    import task33_rules as rules
    doc = read(path, "the TASK33 disposition")
    tie("the TASK33 disposition", doc, candidate, baseline=False)
    a.require(doc.get("schema") == task33_dispose.SCHEMA,
              "not a TASK33 disposition")
    found, reported = {}, []
    for x in doc.get("decisions", []):
        a.require(isinstance(x, dict) and "case" in x and "kind" in x and
                  x.get("decision") in rules.GATES + (
                      rules.REPORTED, rules.UNSUPPORTED),
                  "malformed TASK33 decision: %r" % (x,))
        key = "%s:%s" % (x["case"], x["kind"])
        a.require(key not in found, "repeated TASK33 decision: " + key)
        if x["decision"] in (rules.REPORTED, rules.UNSUPPORTED):
            reported.append(dict(key=key, decision=x["decision"],
                                 reason=x.get("reason", "")))
            found[key] = None
            continue
        record = dict(key=key, source=x["decision"], failed=[], missing=[],
                      owed=[x["owed"]] if x.get("owed") else [],
                      reason=x.get("reason", ""))
        if x["decision"] == rules.FAIL:
            record["failed"].append("TASK33: fail")
        elif x["decision"] != rules.PASS:
            record["missing"].append("TASK33: " + x["decision"])
            record["owed"] = record["owed"] or ["attribution"]
        found[key] = record
    keys = {"%s:%s" % k for k in task33_dispose.expected_storage()}
    absent = sorted(keys - set(found))
    a.require(not absent, "the TASK33 disposition has no decision for: " +
              ", ".join(absent[:5]))
    gates = [x["decision"] for x in doc["decisions"]
             if x["decision"] in rules.GATES]
    a.require(gates and doc.get("status") == rules.worst(gates),
              "the TASK33 disposition's status is not that of its "
              "decisions")
    carried = {k: doc.get(k, []) for k in (
        "owed", "attribution_needed", "process_redraws")}
    return ({k: v for k, v in found.items() if v is not None}, reported,
            carried, a.seal(Path(path)))


def load_receipt(path, gate, candidate):
    """A gate receipt (`receipt` command): its record and seal. The files
    it names are sealed again, and must be as they were."""
    doc = read(path, "the %s receipt" % gate)
    a.require(doc.get("schema") == RECEIPT_SCHEMA and
              doc.get("gate") == gate,
              "not a %s receipt: %s" % (gate, path))
    tie("the %s receipt" % gate, doc, candidate)
    a.require(doc.get("status") in RECEIPT_STATUS and
              isinstance(doc.get("exit"), int),
              "the %s receipt has no status" % gate)
    for held in doc.get("reports", []):
        target = Path(held["path"])
        a.require(target.is_file() and a.seal(target) == held["seal"],
                  "the %s receipt's report changed or is missing: %s" % (
                      gate, held["path"]))
    return dict(doc, seal=a.seal(Path(path)))


def gate_record(receipt):
    status = receipt["status"]
    record = dict(gate=receipt["gate"], source=status, failed=[],
                  missing=[], owed=[], attribution=receipt.get(
                      "attribution", []), exit=receipt["exit"])
    if status == "fail":
        record["failed"].append("%s: fail" % receipt["gate"])
    elif status == "inconclusive":
        record["missing"].append("%s: inconclusive" % receipt["gate"])
        record["owed"].append("attribution")
    elif status == "attributed" and not record["attribution"]:
        record["missing"].append("%s: attributed with no attribution"
                                 % receipt["gate"])
        record["owed"].append("attribution")
    return record


def make_receipt(gate, candidate, status, exit_status, reports=(),
                 attribution=(), note=""):
    """The receipt of a gate the lead ran."""
    a.require(gate in GATES + (D7,), "unknown gate " + gate)
    a.require(status in RECEIPT_STATUS, "unknown status " + status)
    want = {"pass": 0, "attributed": 0, "fail": 1}.get(status, 2)
    a.require(status == "inconclusive" or exit_status == want or
              gate == D7, "exit %d is not that of %s" % (exit_status,
                                                         status))
    return dict(schema=RECEIPT_SCHEMA, gate=gate, candidate=candidate,
                baseline=a.BASE, status=status, exit=exit_status,
                attribution=list(attribution), note=note,
                reports=[dict(path=str(Path(p).resolve()),
                              seal=a.seal(Path(p))) for p in reports])


# ------------------------------------------------------------- the rule

def family_of(name):
    import task31_cases as c31
    case = name.rsplit("-", 1)[0]
    for family in c31.FAMILIES:
        if case in ("tactic_%s_%s" % (family, stage) for stage in c31.STAGES):
            return family
    return None


def size_of(name):
    return int(name.rsplit("-", 1)[1])


ALLOCATION_LIMIT = 1000


def measured_by(name, identity, allocated, timed):
    """What measured the attribution of a D2 cell: its family's feasible
    cells of at most 1000 assumptions that passed allocation with an
    attributed identity, and its family's passing cells of the timing
    sample."""
    family = family_of(name)
    cells = [n for n in identity if family and family_of(n) == family and
             n not in cases.INFEASIBLE]
    return dict(
        allocation=sorted(n for n in cells if size_of(n) <= ALLOCATION_LIMIT
                          and allocation_passed(allocated.get(n)) and
                          identity[n]["status"] == "attributed"),
        timing=sorted(n for n in cells if n in timed and
                      timed[n]["cls"] == "pass"))


def allocation_passed(row):
    return row is not None and row["decision"] == "pass" and \
        row["work"] == "equal"


def judge_identity(identity, failed, missing):
    if identity["status"] == "different":
        failed.append("identity: the loaded closure or the work differs")
    elif identity["status"] not in IDENTITY_OK:
        missing.append("identity: " + str(identity["status"]))


def judge_allocation(row, failed, missing):
    if row is None:
        missing.append("allocation: no decision")
        return
    if row["decision"] == "fail":
        failed.append("allocation: fail")
    if row["work"] == "differs":
        failed.append("allocation: the work row differs")
    if row["decision"] == "inconclusive":
        missing.append("allocation: inconclusive")
    elif row["decision"] == "pass" and row["work"] not in (
            "equal", "differs"):
        missing.append("allocation: the work row is %s" % (
            row["work"] or "missing"))


def judge_timing(name, row, d4, found, failed, missing, owed):
    """The timing decision of a sampled cell; sets `policy` on D4."""
    cls = row["cls"]
    if cls == "pass":
        return
    if cls == "fail":
        failed.append("timing: fail")
    elif cls == "control_limited" and name in d4 and \
            row["first"] == "control_limited":
        found["policy"] = "D4"
        found["policy_note"] = (
            "fresh decisive first stage control-limited: stage 2 skipped, "
            "disposed by policy D4 with identity and exact allocation")
    elif cls == "protocol":
        missing.append("timing: no admitted measurement")
        owed.append("redraw")
    elif cls == "control_limited":
        missing.append("timing: control-limited")
        owed.append("attribution" if row["stage2"] else "stage2")
    else:
        missing.append("timing: inconclusive")
        owed.append("attribution" if row["followup"] else "followup")


def judge(name, identity, allocated, timed, d4, groups=None):
    """One cell: its record. `timed` is the cell's timing row or None where
    it is not sampled."""
    infeasible = name in cases.INFEASIBLE
    found = dict(
        name=name, identity=identity["status"], policy=None,
        allocation=None if allocated is None else allocated["decision"],
        allocation_work=None if allocated is None else allocated["work"],
        allocation_pairs=None if allocated is None else allocated["pairs"],
        timing=None if timed is None else timed["cls"],
        timing_chain=None if timed is None else dict(
            first=timed["first"], stage2=timed["stage2"],
            followup=timed["followup"], earlier=timed["earlier"]),
        attribution=[dict(path=r["path"], reason=r["reason"])
                     for r in identity.get("attributed", [])])
    failed, missing, owed = [], [], []
    judge_identity(identity, failed, missing)
    if infeasible:
        found["policy"] = "D2"
        found["note"] = "heavy size-10000 tactic cell: identity only"
        if identity["status"] == "attributed":
            found["measured_by"] = groups
            if not (groups["allocation"] and groups["timing"]):
                missing.append("attribution not measured in its family")
                owed.append("attribution")
    else:
        judge_allocation(allocated, failed, missing)
        if timed is not None:
            judge_timing(name, timed, d4, found, failed, missing, owed)
        else:
            found["policy"] = "stratified"
            found["note"] = "unsampled: identity and exact allocation"
    found["failed"], found["missing"], found["owed"] = failed, missing, owed
    found["blocked"] = bool(missing) and owed == ["attribution"]
    found["status"] = (STATUS_FAIL if failed else
                       STATUS_INCOMPLETE if missing else STATUS_PASS)
    return found


def status_of(records):
    kinds = {r["status"] for r in records}
    return (STATUS_FAIL if STATUS_FAIL in kinds else
            STATUS_INCOMPLETE if STATUS_INCOMPLETE in kinds else
            STATUS_PASS)


def finish(record):
    """Status of an auxiliary record from its failures and omissions."""
    record["status"] = (STATUS_FAIL if record["failed"] else
                        STATUS_INCOMPLETE if record["missing"]
                        else STATUS_PASS)
    return record


def dispose(identity, allocation, timing, units, decisions33, receipts,
            d4=None):
    """Every workload's record, the status of the whole. `identity` and
    `allocation` map their kind (client, matrix, downstream) to the loaded
    tables, `timing` maps a table to its loaded rows."""
    d4 = set(cases.d4() if d4 is None else d4)
    ident = {n: row for k in identity.values() for n, row in
             k["cells"].items()}
    alloc = {n: row for k in allocation.values() for n, row in
             k["rows"].items()}
    timed = {n: row for k in timing.values() for n, row in
             k["cells"].items()}
    order = cases.MATRIX + cases.CLIENT + cases.DOWNSTREAM
    a.require(set(order) == set(ident) and len(order) == len(ident),
              "the identity tables are not the cells of TASK37")
    records = {}
    for n in order:
        groups = measured_by(n, identity["client"]["cells"], alloc, timed) \
            if n in cases.INFEASIBLE else None
        records[n] = judge(n, ident[n], alloc.get(n), timed.get(n), d4,
                           groups)
    workloads = dict(records)
    unit_records = {u: finish(dict(r)) for u, r in units.items()}
    t33 = {k: finish(dict(r)) for k, r in decisions33.items()}
    gates = {g: finish(gate_record(r)) for g, r in receipts.items()}
    scaling = {t: v["scaling"] for t, v in timing.items()
               if v["scaling"] is not None}
    scaling_records = {t: finish(dict(
        failed=["retained slope: fail"] if s == "fail" else [],
        missing=[] if s in ("pass", "fail") else
        ["retained slope: " + s], owed=[], class_=s))
        for t, s in scaling.items()}
    every = (list(records.values()) + list(unit_records.values()) +
             list(t33.values()) + list(gates.values()) +
             list(scaling_records.values()))
    grid = [k["status"] for k in identity.values()]
    status = status_of(every)
    if "different" in grid:
        status = STATUS_FAIL
    elif status == STATUS_PASS and any(s not in IDENTITY_OK for s in grid):
        status = STATUS_INCOMPLETE
    counts = {k: sum(r["status"] == k for r in every)
              for k in (STATUS_PASS, STATUS_FAIL, STATUS_INCOMPLETE)}
    owed = [dict(workload=w, owed=o) for w, r in (
        list(records.items()) + list(unit_records.items()) +
        list(t33.items()) + list(gates.items())) for o in r["owed"]]
    policies = {p: sorted(n for n, r in records.items()
                          if r["policy"] == p)
                for p in ("D2", "D4", "stratified")}
    return dict(
        schema=SCHEMA, status=status, counts=counts,
        kinds=dict(matrix=len(cases.MATRIX), client=len(cases.CLIENT),
                   downstream=len(cases.DOWNSTREAM),
                   task32_units=len(unit_records),
                   task33_decisions=len(t33), gates=len(gates)),
        identity_status={k: v["status"] for k, v in identity.items()},
        identity_unaccounted={k: v["unaccounted"] for k, v in
                              identity.items()},
        cells=records, task32=unit_records, task33=t33, gates=gates,
        retained_slope=scaling_records, policies=policies, owed=owed)


# ------------------------------------------------------------- the command

def derive(args):
    cand = args.candidate
    a.require(isinstance(cand, str) and len(cand) >= 10,
              "--candidate must be a revision of at least ten digits")
    inputs = {}
    identity = {}
    for kind, root, names in (
            ("client", args.identity_client, cases.CLIENT),
            ("matrix", args.identity_matrix, cases.MATRIX),
            ("downstream", args.identity_downstream, cases.DOWNSTREAM)):
        a.require(root is not None, "no identity table for %s cells" % kind)
        identity[kind] = load_identity(root, "identity " + kind, names, cand)
        inputs["identity-" + kind] = identity[kind]["seals"]
    allocation = {}
    for kind, task, root, names, skipped in (
            ("matrix", "task37-matrix", args.alloc_matrix, cases.MATRIX, ()),
            ("client", "task37-client", args.alloc_client,
             cases.CLIENT_ALLOCATED, cases.INFEASIBLE),
            ("downstream", "task37-downstream", args.alloc_downstream,
             cases.DOWNSTREAM, ())):
        a.require(root is not None, "no allocation output for " + task)
        allocation[kind] = load_allocation(root, task, names, skipped, cand)
        inputs["allocation-" + kind] = allocation[kind]["seals"]
    engines = timing_engines()
    timing = {}
    for table, root, followups, ledger, sample in (
            ("task37-client", args.timing_client, args.followup_client,
             args.ledger_client, cases.CLIENT_SAMPLE),
            ("task37-matrix", args.timing_matrix, args.followup_matrix,
             args.ledger_matrix, cases.MATRIX_SAMPLE)):
        timing[table] = load_timing(table, root, followups or [], ledger,
                                    sample, cand, args.repo, engines)
        inputs[table] = timing[table]["seals"]
    units, inputs["task32"] = load_task32(args.task32, cand)
    t33, reported33, carried33, inputs["task33"] = load_task33(
        args.task33, cand)
    receipts = {}
    for gate, path in zip(GATES, (args.startup_gate, args.loading_simplib,
                                  args.loading_conglib)):
        receipts[gate] = load_receipt(path, gate, cand)
        inputs[gate] = receipts[gate]["seal"]
    d7 = None
    if args.d7_build is not None:
        d7 = load_receipt(args.d7_build, D7, cand)
        inputs[D7] = d7["seal"]
    record = dispose(identity, allocation, timing, units, t33, receipts)
    record.update(
        candidate=identity["client"]["candidate"], baseline=a.BASE,
        scope=SCOPE, inputs=inputs, code=seals(),
        allocation_pairs={k: v["pairs"] for k, v in allocation.items()},
        timing_attempts={t: v["attempts"] for t, v in timing.items()},
        host_load={t: v["load"] for t, v in timing.items()},
        reported=dict(
            task33=reported33, task33_carried=carried33,
            d7_build=None if d7 is None else dict(
                status=d7["status"], exit=d7["exit"],
                note=d7.get("note", ""), gate=False)))
    return record


def lines(record):
    out = []
    for table, found in record["timing_attempts"].items():
        for x in found:
            out.append("TIMING-ATTEMPT %s %s status %s: %s" % (
                table, x["attempt"], x["status"],
                "void (no measurement admitted)" if x["void"]
                else "judged"))
    for kind, paths in record["identity_unaccounted"].items():
        out += ["FAIL identity %s: unaccounted difference %s" % (kind, p)
                for p in paths]
    groups = [("cell", record["cells"]), ("task32", record["task32"]),
              ("task33", record["task33"]), ("gate", record["gates"])]
    for label, rows in groups:
        for name, r in rows.items():
            if r["status"] == STATUS_PASS and not r.get("policy") in (
                    "D2", "D4"):
                continue
            why = r["failed"] + r["missing"] or [
                "policy %s: %s" % (r["policy"], r.get("policy_note") or
                                   r.get("note"))]
            out.append("%s %s %s: %s%s" % (
                r["status"].upper(), label, name, "; ".join(why),
                " [owed: %s]" % ", ".join(r["owed"]) if r["owed"] else ""))
    for t, r in record["retained_slope"].items():
        if r["status"] != STATUS_PASS:
            out.append("%s retained slope %s" % (r["status"].upper(), t))
    return out


def verdict(record):
    return ("TASK37 disposition: %s %s (%s; candidate %s; policies D2 %d, "
            "D4 %d, stratified %d; owed %d)" % (
                record["status"], json.dumps(record["counts"]),
                ", ".join("%s %d" % kv for kv in record["kinds"].items()),
                record["candidate"], len(record["policies"]["D2"]),
                len(record["policies"]["D4"]),
                len(record["policies"]["stratified"]),
                len(record["owed"])))


def summary(record):
    reported = record["reported"]
    text = lines(record) + ["", verdict(record), "scope: " + record["scope"]]
    d7 = reported["d7_build"]
    text.append("D7 build (reported, not a gate): " + (
        "not provided" if d7 is None else "%s, exit %s %s" % (
            d7["status"], d7["exit"], d7["note"])))
    return "\n".join(text) + "\n"


def disposition(args):
    if args.check:
        held_path = Path(args.check) / "disposition.json"
        held = read(held_path, "the recorded disposition")
        check_code(held.get("code"))
    record = derive(args)
    for line in lines(record):
        print(line)
    if args.record:
        out = Path(args.record)
        a.require(not out.exists(), "refusing to replace %s" % out)
        out.mkdir(parents=True)
        a.save(out / "disposition.json", record)
        (out / "SUMMARY.txt").write_text(summary(record))
    else:
        a.require(canonical(dict(held, code=record["code"])) ==
                  canonical(record), "changed TASK37 disposition")
    print(verdict(record))
    return {STATUS_PASS: 0, STATUS_FAIL: 1}.get(record["status"], 2)


def receipt_command(argv):
    p = argparse.ArgumentParser(prog="task37_dispose.py receipt")
    add = p.add_argument
    add("--gate", required=True, choices=GATES + (D7,))
    add("--candidate", required=True)
    add("--status", required=True, choices=RECEIPT_STATUS)
    add("--exit", type=int, required=True, dest="exit_status")
    add("--out", type=Path, required=True)
    add("--report", type=Path, action="append", default=[])
    add("--attribution", action="append", default=[])
    add("--note", default="")
    args = p.parse_args(argv)
    a.save(args.out, make_receipt(
        args.gate, args.candidate, args.status, args.exit_status,
        args.report, args.attribution, args.note))
    return 0


def parser():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    add = p.add_argument
    add("--candidate", required=True)
    for name in ("client", "matrix", "downstream"):
        add("--identity-" + name, type=Path, help="identity table")
        add("--alloc-" + name, type=Path, help="allocation output")
    for name in ("client", "matrix"):
        add("--timing-" + name, type=Path, help="final stage of the table")
        add("--followup-" + name, type=Path, action="append",
            help="a follow-up of the table (repeatable)")
        add("--ledger-" + name, type=Path, help="attempts ledger of the "
            "table")
    add("--task32", type=Path)
    add("--task33", type=Path)
    add("--startup-gate", type=Path, help="startup gate receipt")
    add("--loading-simplib", type=Path)
    add("--loading-conglib", type=Path)
    add("--d7-build", type=Path, help="D7 build receipt (reported only)")
    add("--repo", type=Path, default=a.HERE.parents[3])
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--record", type=Path, help="write to this new dir")
    mode.add_argument("--check", type=Path, help="require this recorded "
                      "disposition to be derived again")
    return p


def main(argv=None):
    """The status of the disposition, or REFUSED (3) with one line on the
    standard error."""
    argv = sys.argv[1:] if argv is None else argv
    with tg.terminating_as_interrupt():
        try:
            if argv[:1] == ["receipt"]:
                return receipt_command(argv[1:])
            return disposition(parser().parse_args(argv))
        except Exception as error:
            text = str(error)
            if not isinstance(error, ValueError):
                import traceback
                traceback.print_exc()
                text = "%s: %s" % (type(error).__name__, text)
            print("REFUSED: " + " ".join(text.split()), file=sys.stderr,
                  flush=True)
            return tg.REFUSED


if __name__ == "__main__":
    sys.exit(main())
