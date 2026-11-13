"""The auxiliary gates of the TASK37 disposition, read and replayed.

`task37_dispose.py` joins them with the cell decisions. Nothing here takes a
status from the command line: each gate's status is read from the archive
of the producer's own decision, and its replay (the producer's own replay
function) then recomputes that archive, so a status that is not the
recomputed one refuses the disposition.

What each replay re-derives, and what it cannot:

- TASK32 (`task32_downstream.replay_chain`, `disposition`): every stage of
  the chain from its archived receipts, the ledger and the counts file; the
  disposition is then derived again and compared with the file. No snapshot
  tree is needed (the receipts are archived); the stages' `repo` (read
  from the report) is not consulted, D is.
- TASK33 (`task33_storage.dispatch` on `dispose`, under the TASK37
  declaration): the timing chain, the storage chains, the S3 reports'
  seals and code, the ledgers; the disposition is derived again into a
  scratch file and compared with the given one but for its `code` record
  (which is checked against the table's history). The `.seal` file of the
  given one is checked. As for TASK32 no snapshot tree is read by the
  replay.
- the startup gate (`startup_gate.replay`): every decision from the process
  records of the archive alone; the record it is sealed to is the one the
  caller names. A TASK37 gate always has one (`run_startup_gate.sh` makes
  it in the run, from the TASK37 template and the run's own `who_pays.out`,
  and `header.json` seals its sha256), which must be that file and must
  name the baseline and the candidate of the gate; its null control has
  none. The null control is replayed too and must pass, or the gate is
  `inconclusive`. NOT re-derived: the builds, the path-length cells
  (`startup_gate.py cell`) and `check_deltas`, which only reports and
  needs the built trees.
- loading (`loading.replay`): every observation, extension check and
  decision of the run from its archived process receipts, with the attempts
  ledger. The two shards (simpLib, congLib) must have been run with the
  same api-audit receipt (`run_api_audit.sh` makes it once; the reports
  record its seal), which is sealed in the record. NOT re-derived: the API
  audit receipt's own run.
- TASK33 is judged under `task37_declared.json`: the declaration must be
  valid and filled, and name the baseline and the candidate of the
  disposition (the stages and the offline reports are bound to it by the
  storage driver's own replay, `check_declared` and `check_offline_identity`).

The reviewed lines: the recorded candidates and harnesses are accepted by
`task37_lineage.Lineage`.
"""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import shlex
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import task32_downstream as d32

NOTE_SECOND = d32.NOTE_SECOND
RECEIPT_SCHEMA = "task37-receipt-v1"
RECEIPT_STATUS = ("pass", "attributed", "fail", "inconclusive")
STARTUP = "startup-gate"
LOADING = {"loading-simpLib": "simpLib", "loading-congLib": "congLib"}
GATES = (STARTUP,) + tuple(LOADING)
D7 = "d7-build"
EXITS = {"pass": 0, "attributed": 0, "fail": 1, "inconclusive": 2}
# The owed stage of the sources' vocabulary: TASK33 calls the timing
# `extend` stage `second`, the cells `stage2`.
OWED_NAMES = dict(second="stage2")
T32_STATUSES = ("pass", "fail", "followup", "blocked")


def quiet(function, *args):
    """`function(*args)` with its output discarded."""
    with contextlib.redirect_stdout(io.StringIO()), \
            contextlib.redirect_stderr(io.StringIO()):
        return function(*args)


def read(path, label):
    a.require(path is not None, "no %s given" % label)
    path = Path(path)
    a.require(path.is_file(), "%s is missing: %s" % (label, path))
    return a.load(path)


def parse(parser, argv, label):
    """The producer's own parser on `argv`; its usage error is a refusal,
    not an exit."""
    try:
        return parser.parse_args(argv)
    except SystemExit:
        raise ValueError("the %s arguments are not those of its own "
                         "command: %s" % (label, " ".join(argv)))


def check_repo(args, lineage, label):
    if getattr(args, "repo", None) is None:
        args.repo = lineage.repo
    a.require(Path(args.repo).resolve() == lineage.repo,
              "the %s replay names the checkout %s, not %s (the one "
              "commit point)" % (label, args.repo, lineage.repo))


# ---------------------------------------------------------------- TASK32

def read_task32(path, lineage):
    """({unit: record}, seal, candidate) of the TASK32 disposition."""
    import task32_cases
    doc = read(path, "the TASK32 disposition")
    found = lineage.candidate_of("task32", doc.get("candidate"))
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
    return units, a.seal(Path(path)), found


def replay_task32(path, text, lineage):
    """Derive the TASK32 disposition again from the arguments of its own
    `dispose` command (`text`, without --out) and require the file to be
    it."""
    held = a.load(Path(path))
    with d32.using_table("task32"):
        args = parse(d32.build_parser(), ["dispose", *shlex.split(text),
                                          "--out", "/dev/null"],
                     "TASK32")
        check_repo(args, lineage, "TASK32")
        d32.require_ledger(args)

        def derive():
            chain = d32.replay_chain(
                args.stage, args.ledger, args.counts, args.followup_counts,
                args.repo)
            return d32.disposition(
                chain, args.ledger or d32.ledger_path(
                    chain[0]["report"]["repo"]), args.counts,
                d32.parse_relocated(args.relocated))
        found = quiet(derive)
    a.require(d32.same(json.loads(json.dumps(found)), held),
              "the TASK32 disposition is not the one its stages derive")


# ---------------------------------------------------------------- TASK33

def read_task33(path, lineage):
    """({key: record}, reported, carried, seal, candidate) of TASK33."""
    import task33_dispose
    import task33_rules as rules
    doc = read(path, "the TASK33 disposition")
    found_candidate = lineage.candidate_of("task33", doc.get("candidate"))
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
        owed = [OWED_NAMES.get(x["owed"], x["owed"])] if x.get("owed") \
            else []
        record = dict(key=key, source=x["decision"], failed=[], missing=[],
                      owed=owed, reason=x.get("reason", ""))
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
    seal = a.load(Path(str(path) + ".seal")) \
        if Path(str(path) + ".seal").is_file() else None
    a.require(seal == a.seal(Path(path)),
              "the TASK33 disposition has no .seal file that seals it")
    return ({k: v for k, v in found.items() if v is not None}, reported,
            carried, a.seal(Path(path)), found_candidate)


def replay_task33(path, text, lineage):
    """Derive the TASK33 disposition again from the arguments of its own
    `dispose` command (`text`, without --out; it must name the TASK37
    declaration) and require the file to be it, but for the `code` record,
    which must be that of the code now or of its history."""
    import task33_storage as storage
    held = a.load(Path(path))
    with tempfile.TemporaryDirectory(prefix="task37-t33-") as scratch, \
            d32.using_table(storage.TABLE):
        out = Path(scratch) / "disposition.json"
        args = parse(storage.build_parser(), ["dispose", *shlex.split(text),
                                              "--out", str(out)], "TASK33")
        a.require(args.declared is not None and Path(
            args.declared).resolve() == (a.HERE / "task37_declared.json"
                                         ).resolve(),
                  "the TASK33 replay is not under --declared "
                  "task37_declared.json")
        check_repo(args, lineage, "TASK33")
        d32.check_code(held.get("code"))
        quiet(storage.dispatch, args)
        check_declared(held, a.HERE / "task37_declared.json")
        found = a.load(out)
    a.require(d32.same(dict(found, code=None), dict(held, code=None)),
              "the TASK33 disposition is not the one its stages derive")


def check_declared(held, path):
    """The declaration the TASK33 disposition was judged under is valid
    and filled (no placeholder) and is for the baseline and the candidate
    of the disposition."""
    import task33_offline as offline
    declared = offline.load_declared(path)
    problems = offline.shape_problems(declared)
    a.require(not problems, "the declaration %s is not valid: %s" % (
        Path(path).name, "; ".join(problems)))
    a.require(declared["base"] == a.BASE,
              "the declaration is for another baseline than %s" % a.BASE)
    a.require(declared["cand"] == held.get("candidate"),
              "the declaration is for candidate %s, the TASK33 "
              "disposition's is %s" % (declared["cand"],
                                       held.get("candidate")))


# ---------------------------------------------------------- startup gate

def read_startup(out, null, lineage, label=STARTUP):
    """The startup gate archive `out` (a gate, or with `null` its null
    control): its header and decisions, with the candidate and harness it
    names accepted. Returns (header, decisions)."""
    import startup_gate as sg
    out = Path(out)
    header = read(out / "header.json", label + " header")
    decisions = read(out / "decisions.json", label + " decisions")
    a.require(header.get("schema") == sg.SCHEMA and
              bool(header.get("null")) == null,
              "%s is not a%s startup gate archive" % (
                  label, " null" if null else ""))
    a.require(isinstance(header.get("pairs"), int) and
              header["pairs"] >= sg.PAIRS, "%s has fewer than %d pairs" % (
                  label, sg.PAIRS))
    lineage.harness(label, header.get("harness"), clean=True)
    a.require(bool(header.get("record_sha256")) != null,
              "%s %s" % (label, "has a record, which a null control "
                         "never has" if null else
                         "is sealed to no record: a TASK37 gate always "
                         "has one, made in its run"))
    trees, sides = header["trees"], header["sides"]
    for side in ("base", "candidate"):
        revs = {trees[l]["rev"] for l in sides[side]}
        a.require(len(revs) == 1, "%s: more than one revision on the %s "
                  "side" % (label, side))
        rev = revs.pop()
        if side == "base" or null:
            a.require(lineage.commit(label, rev) == a.BASE,
                      "%s: the baseline images are not the pinned "
                      "baseline" % label)
        else:
            lineage.candidate_of(label, rev)
    return header, decisions


def check_record(header, record, lineage, label=STARTUP):
    """The record file is the one the gate is sealed to (sha256 in
    `header.json`) and it names the baseline and the candidate the gate
    measured (the template's `Baseline: develop <sha>` and candidate
    lines). Returns the record's seal."""
    a.require(record is not None, "%s is sealed to a record: pass it" %
              label)
    record = Path(record)
    a.require(record.is_file(), "%s record is missing: %s" % (label, record))
    data = record.read_bytes()
    a.require(hashlib.sha256(data).hexdigest() == header["record_sha256"],
              "%s record differs from its seal in header.json" % label)
    text = data.decode()
    for side in ("base", "candidate"):
        for rev in {header["trees"][l]["rev"] for l in header["sides"][side]}:
            full = lineage.commit(label, rev)
            a.require(full in text, "%s record does not name the %s %s" %
                      (label, side, full))
    return a.seal(record)


def replay_startup(out, record):
    import startup_gate as sg
    import argparse
    code = quiet(sg.replay, argparse.Namespace(output=Path(out),
                                               record=record))
    a.require(code == 0, "the startup gate in %s did not replay" % out)


def startup_gate(header, decisions, null_decisions):
    """The gate record of the startup gate: its status is that of its
    decision (`pass`, `attributed` with the notes as the attribution,
    `fail`; anything else, a blocked or a smoke run, is inconclusive), and
    a null control that did not pass makes it inconclusive."""
    decision = decisions.get("decision")
    status = decision if decision in ("pass", "attributed", "fail") \
        else "inconclusive"
    reasons = list(decisions.get("reasons", [])) + list(
        decisions.get("blockers", []))
    if status != "fail" and null_decisions.get("decision") != "pass":
        status = "inconclusive"
        reasons.append("the null control is %s, not pass" %
                       null_decisions.get("decision"))
    return gate_record(STARTUP, status, list(decisions.get("notes", [])),
                       reasons, header["record_sha256"])


# --------------------------------------------------------------- loading

def read_loading(out, gate, lineage):
    """The loading run archive `out` of `gate`: its report with the
    candidate accepted; returns (report, results status)."""
    import loading
    out = Path(out)
    report = read(out / "loading.json", gate + " report")
    a.require(report.get("schema") == loading.SCHEMA and
              report.get("success") is True and
              report.get("mode") == "isolated-source" and
              report.get("module") == LOADING[gate] and
              report.get("stage") in ("first", "second"),
              "%s is not a successful decision run of %s" % (
                  gate, LOADING[gate]))
    chosen = report["selections"]
    a.require(lineage.commit(gate, chosen["baseline"]["revision"]) ==
              a.BASE, "%s was measured against another baseline" % gate)
    lineage.candidate_of(gate, chosen["candidate"]["revision"])
    code = loading.exit_status(report["results"]["candidate"]["metrics"])
    status = {0: "pass", 1: "fail"}.get(code, "inconclusive")
    return report, status


def check_one_audit(reports):
    """The loading shards ran with one api-audit receipt: {gate: report};
    returns its seal."""
    seals = {}
    for gate, report in reports.items():
        found = report.get("semantic_gate")
        a.require(isinstance(found, dict) and found.get("seal"),
                  "%s records no api-audit receipt" % gate)
        seals[gate] = json.dumps(found["seal"], sort_keys=True)
    a.require(len(set(seals.values())) == 1,
              "the loading shards were run with different api-audit "
              "receipts (it is made once): %s" % ", ".join(
                  "%s %s" % kv for kv in sorted(seals.items())))
    return next(iter(reports.values()))["semantic_gate"]["seal"]


def replay_loading(out, ledger):
    import loading
    info = quiet(loading.replay, Path(out), None, None, ledger)
    return info


def loading_gate(gate, report, status):
    record = gate_record(gate, status, [], [], None)
    if status == "inconclusive":
        record["owed"] = ["stage2" if report["stage"] == "first"
                          else "attribution"]
    return record


# --------------------------------------------------------------- records

def gate_record(gate, status, attribution, reasons, sealed):
    """The record of a gate: failures and omissions by status; an
    `attributed` one with no attribution, or an inconclusive one, owes an
    attribution."""
    record = dict(gate=gate, source=status, failed=[], missing=[], owed=[],
                  attribution=attribution, reasons=reasons,
                  exit=EXITS[status], sealed_to=sealed)
    if status == "fail":
        record["failed"].append("%s: fail" % gate)
    elif status == "inconclusive":
        record["missing"].append("%s: inconclusive" % gate)
        record["owed"].append("attribution")
    elif status == "attributed" and not attribution:
        record["missing"].append("%s: attributed with no attribution" % gate)
        record["owed"].append("attribution")
    return record


# -------------------------------------------------- the D7 build receipt

def make_receipt(gate, candidate, status, exit_status, reports=(),
                 attribution=(), note=""):
    """The receipt of the D7 build timing, which is reported and never a
    gate: its status and exit are typed, so the exit must be that of the
    status, and at least one sealed report must back it."""
    a.require(gate == D7, "a receipt is made for %s only; the other gates "
              "are replayed" % D7)
    a.require(status in RECEIPT_STATUS, "unknown status " + status)
    a.require(exit_status == EXITS[status],
              "exit %d is not that of %s (%d)" % (
                  exit_status, status, EXITS[status]))
    a.require(reports, "a receipt needs at least one sealed --report")
    return dict(schema=RECEIPT_SCHEMA, gate=gate, candidate=candidate,
                baseline=a.BASE, status=status, exit=exit_status,
                attribution=list(attribution), note=note,
                reports=[dict(path=str(Path(p).resolve()),
                              seal=a.seal(Path(p))) for p in reports])


def load_receipt(path, lineage):
    """The D7 receipt: its record and seal. The files it names are sealed
    again, and must be as they were."""
    doc = read(path, "the %s receipt" % D7)
    a.require(doc.get("schema") == RECEIPT_SCHEMA and doc.get("gate") == D7,
              "not a %s receipt: %s" % (D7, path))
    lineage.candidate_of(D7, doc.get("candidate"))
    a.require(doc.get("baseline") == a.BASE and
              doc.get("status") in RECEIPT_STATUS and
              doc.get("exit") == EXITS.get(doc.get("status")),
              "the %s receipt has no status" % D7)
    a.require(doc.get("reports"), "the %s receipt names no report" % D7)
    for held in doc["reports"]:
        target = Path(held["path"])
        a.require(target.is_file() and a.seal(target) == held["seal"],
                  "the %s receipt's report changed or is missing: %s" % (
                      D7, held["path"]))
    return dict(doc, seal=a.seal(Path(path)))
