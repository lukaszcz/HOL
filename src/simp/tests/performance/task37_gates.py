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
  `inconclusive`. The record is made with the load deltas DECLARED from an
  archive (design decision 21; `fill_record.py` writes them beside the
  record as a sidecar, `--startup-declared`, whose `record_sha256` is the
  record's): `read_declared` binds the sidecar to the record, and
  `declared_problems` requires its Ds and Dc to equal the R2
  `load.total` of load-simpLib and load-congLib on EVERY image of the
  judged gate; a difference makes the gate `fail` (visible in the
  disposition, never transferred). Every attempt of the runner is in an
  attempts ledger (`--startup-ledger`, R-1: a failed attempt stays), and
  the judged gate must be the last one (`startup_attempts`); an attempt
  counts as complete only with its `done` file (`<output>/done`, written
  by the runner at its end; it is not a ledger line) and a close status of
  0 or 2 (2: completed with a soft step failed). An incomplete last
  attempt with no gate decision is void (refused); with one it is judged
  by it (decision 26): fail or blocked on grounds other than the declared
  deltas is the gate's result, a pass or a failure on the declared deltas
  alone leaves it incomplete owing a `redraw`. Every earlier attempt is
  judged by its gate decision whenever `gate/decisions.json` exists,
  complete or not, and recorded; it blocks a redraw only when it is
  complete and passed, or decided fail or blocked on grounds other than
  the declared deltas (void attempts, delta-only failures and incomplete
  passing attempts do not block); a sidecar is bound to its record and
  its sealed `inputs.txt`. NOT re-derived: the builds, the path-length cells
  (`startup_gate.py cell`) and the runner's `check_deltas` (whole load
  rows against the declared archive), which needs the built trees; the
  declared totals are re-checked here from `decisions.json`.
- loading (`loading.replay`): every observation, extension check and
  decision of the run from its archived process receipts, with the attempts
  ledger. The two shards (simpLib, congLib) must have been run with the
  same api-audit receipt (`run_api_audit.sh` makes it once; the reports
  record its seal), which is sealed in the record and must exist, with the
  seal the reports record and pass (`check_one_audit`: the loading replay
  itself only checks it when the file is there). NOT re-derived: the API
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
import re
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
# The TASK37 tables of the TASK32 and TASK33 drivers (decision 22).
TABLE32, TABLE33 = "task37-t32", "task37-t33"
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
    a.require(doc.get("table") == TABLE32,
              "the TASK32 disposition is of table %s, not of TASK37's "
              "table %s" % (doc.get("table"), TABLE32))
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
    with d32.using_table(TABLE32):
        args = parse(d32.build_parser(), ["dispose", *shlex.split(text),
                                          "--out", "/dev/null"],
                     "TASK32")
        a.require(args.table == TABLE32, "the TASK32 replay is not under "
                  "table " + TABLE32)
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
    a.require(doc.get("table") == TABLE33,
              "the TASK33 disposition is of table %s, not of TASK37's "
              "table %s" % (doc.get("table"), TABLE33))
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
    `dispose` command (`text`, without --out) under the TASK37 table
    (`task37-t33`, which fixes the TASK37 declaration; a contradicting
    --declared is refused) and require the file to be it, but for the
    `code` record, which must be that of the code now or of its history."""
    import task33_storage as storage
    held = a.load(Path(path))
    with tempfile.TemporaryDirectory(prefix="task37-t33-") as scratch, \
            storage.using_storage_table(TABLE33), d32.using_table(TABLE33):
        out = Path(scratch) / "disposition.json"
        args = parse(storage.build_parser(), ["dispose", *shlex.split(text),
                                              "--out", str(out)], "TASK33")
        a.require(args.table == TABLE33 and
                  d32.TABLES[args.table].declared is not None,
                  "the TASK33 replay is not under a TASK37 table")
        check_repo(args, lineage, "TASK33")
        d32.check_code(held.get("code"))
        quiet(storage.dispatch, args)
        check_declared(held, d32.TABLES[TABLE33].declared, lineage)
        found = a.load(out)
    a.require(d32.same(dict(found, code=None), dict(held, code=None)),
              "the TASK33 disposition is not the one its stages derive")


def check_declared(held, path, lineage):
    """The declaration the TASK33 disposition was judged under is valid
    and filled (no placeholder) and is for the baseline and the candidate
    of the disposition: the same one, or one whose tree outside the
    performance area is the same (`lineage.equivalent`, whose refusal
    stands: the stages are measured at a stream clone's head, the
    declaration names the final candidate)."""
    import task33_offline as offline
    declared = offline.load_declared(path)
    problems = offline.shape_problems(declared)
    a.require(not problems, "the declaration %s is not valid: %s" % (
        Path(path).name, "; ".join(problems)))
    a.require(declared["base"] == a.BASE,
              "the declaration is for another baseline than %s" % a.BASE)
    if declared["cand"] != held.get("candidate"):
        lineage.equivalent("the declaration's candidate (the TASK33 "
                           "disposition's is %s)" % held.get("candidate"),
                           declared["cand"])


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


DECLARED_SCHEMA = "task37-startup-declared-v1"
LOAD_KINDS = ("load-simpLib", "load-congLib")
SHA256 = re.compile(r"[0-9a-f]{64}")
# The sentences of the record text (fill_record.py) that declare the totals
# and name their archive.
TEXT_TOTALS = re.compile(r"Ds = ([0-9,]+), Dc = ([0-9,]+)")
TEXT_ARCHIVE = re.compile(r"sha256 of its decisions\.json ([0-9a-f]{64})")


def archive_totals(decisions, label):
    """{kind: R2 `load.total`} of a gate archive's decisions (the figures
    `fill_record.py` declares), each equal on every image."""
    r2 = decisions.get("R2") if isinstance(decisions, dict) else None
    found = {}
    for kind in LOAD_KINDS:
        images = r2.get(kind) if isinstance(r2, dict) else None
        a.require(isinstance(images, dict) and images,
                  "%s has no R2 %s" % (label, kind))
        totals = {((row or {}).get("load") or {}).get("total")
                  for row in images.values()}
        a.require(len(totals) == 1 and type(next(iter(totals))) is int,
                  "%s: the R2 %s total is not one integer on every image"
                  % (label, kind))
        found[kind] = totals.pop()
    return found


def read_declared(path, header, record=None):
    """The sidecar of the record (`fill_record.py`): the load totals Ds and
    Dc the record declares, per kind, with the archive they come from. It
    is bound to the record the gate is sealed to, and to its content:

    - the archive named is a gate archive whose `decisions.json` has the
      sha256 the sidecar states, and the totals recomputed from it (the R2
      `load.total` of each kind) are the sidecar's;
    - the record text (`record`, a path; its sha256 is the header's, see
      `check_record`) states the same Ds and Dc and names the same archive
      sha256.

    Returns (document, seal)."""
    doc = read(path, "the startup declared deltas")
    a.require(doc.get("schema") == DECLARED_SCHEMA and
              doc.get("record_sha256") == header.get("record_sha256"),
              "the startup declared deltas are not those of the record "
              "the gate is sealed to")
    totals = doc.get("totals")
    a.require(isinstance(totals, dict) and set(totals) == set(LOAD_KINDS)
              and all(type(v) is int for v in totals.values()) and
              isinstance(doc.get("archive"), str) and doc["archive"] and
              isinstance(doc.get("archive_sha256"), str) and
              SHA256.fullmatch(doc["archive_sha256"]),
              "malformed startup declared deltas")
    archive = Path(doc["archive"]) / "decisions.json"
    a.require(archive.is_file(), "the archive the declared deltas come "
              "from is missing: %s" % archive)
    a.require(hashlib.sha256(archive.read_bytes()).hexdigest() ==
              doc["archive_sha256"], "the archive %s is not the one the "
              "declared deltas name (sha256 differs)" % archive)
    a.require(archive_totals(a.load(archive), str(archive)) == totals,
              "the declared totals are not the R2 load totals of their "
              "archive %s" % archive)
    a.require(record is not None, "the declared deltas are checked "
              "against the record text: pass the record")
    text = Path(record).read_text()
    found = TEXT_TOTALS.findall(text)
    a.require(len(found) == 1 and found[0] == tuple(
        format(totals[k], ",") for k in LOAD_KINDS),
        "the record text does not declare Ds = %s, Dc = %s" % tuple(
            format(totals[k], ",") for k in LOAD_KINDS))
    a.require(TEXT_ARCHIVE.findall(text) == [doc["archive_sha256"]] and
              doc["archive"] in text,
              "the record text does not name the archive %s with sha256 "
              "%s" % (doc["archive"], doc["archive_sha256"]))
    return doc, a.seal(Path(path))


def declared_problems(declared, decisions):
    """What differs between the load totals the record declares and the R2
    `load.total` of the gate on every image (empty when they agree)."""
    problems = []
    r2 = decisions.get("R2")
    r2 = r2 if isinstance(r2, dict) else {}
    for kind in LOAD_KINDS:
        images = r2.get(kind)
        if not isinstance(images, dict) or not images:
            problems.append("the gate has no R2 %s" % kind)
            continue
        for image, row in sorted(images.items()):
            got = ((row or {}).get("load") or {}).get("total")
            if got != declared["totals"][kind]:
                problems.append(
                    "%s on image %s is %s, not the %s the record declares "
                    "(from %s)" % (kind, image, got,
                                   declared["totals"][kind],
                                   declared["archive"]))
    return problems


# The close status of a startup attempt (run_startup_gate.sh): 0, every
# step passed; 2, the run completed (`done` is written) but a soft step
# failed (gate, null gate, check_deltas); anything else (a failing step or
# `die` 1, a signal 129/130/143) is an incomplete run.
EXIT_COMPLETE = (0, 2)


def read_ledger(ledger):
    """The attempts of the startup-gate runner in `ledger` (JSON lines
    `open`/`close` of `run_startup_gate.sh`: {event, attempt, output,
    exit}), oldest first, as [{attempt, output, exit, status}] with
    status `open` (no close yet), `ok` (closed with exit 0), `soft`
    (closed with exit 2) or `failed` (closed otherwise)."""
    path = Path(ledger) if ledger is not None else None
    a.require(path is not None and path.is_file(),
              "no startup attempts ledger: %s" % ledger)
    order, rows = [], {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        try:
            record = json.loads(line)
        except ValueError:
            raise ValueError("the startup ledger %s line %d is not JSON"
                             % (path, number)) from None
        a.require(isinstance(record, dict) and
                  record.get("event") in ("open", "close") and
                  isinstance(record.get("attempt"), str) and
                  record["attempt"] and
                  isinstance(record.get("output"), str),
                  "malformed startup ledger line %d" % number)
        key = record["attempt"]
        if record["event"] == "open":
            a.require(key not in rows, "the startup attempt %s is opened "
                      "twice" % key)
            rows[key] = dict(attempt=key, output=record["output"],
                             status="open", exit=None)
            order.append(key)
        else:
            a.require(key in rows and rows[key]["status"] == "open" and
                      rows[key]["output"] == record["output"] and
                      type(record.get("exit")) is int,
                      "the startup attempt %s is closed without a single "
                      "matching open" % key)
            rows[key].update(exit=record["exit"],
                             status="ok" if record["exit"] == 0 else
                             "soft" if record["exit"] == 2 else "failed")
    a.require(order, "the startup ledger %s has no attempt" % path)
    return [rows[k] for k in order]


def completed(row):
    """The runner of the attempt reached its end: it closed with 0 or 2 and
    wrote `done` (a step that failed with 2 wrote none)."""
    return row["exit"] in EXIT_COMPLETE and (
        Path(row["output"]) / "done").is_file()


def bound_sidecar(out):
    """The sidecar `declared-deltas.json` of the earlier attempt `out`,
    bound as `read_declared` binds the current one: to the record of the
    attempt (its `not-client-visible.md` has the sha256 the gate's
    `header.json` seals, which is the sidecar's `record_sha256`) and to the
    run's sealed `inputs.txt` (its `DECLARED_DELTAS_SHA256`). Returns the
    sidecar, or None when the attempt has none."""
    side = out / "declared-deltas.json"
    if not side.is_file():
        return None
    where = "the earlier attempt " + str(out)
    doc = a.load(side)
    header = out / "gate" / "header.json"
    a.require(header.is_file(), "%s has a sidecar and no gate header.json"
              % where)
    want = a.load(header).get("record_sha256")
    record = out / "not-client-visible.md"
    a.require(want and doc.get("record_sha256") == want and
              record.is_file() and
              hashlib.sha256(record.read_bytes()).hexdigest() == want,
              "the sidecar of %s is not that of its record (swapped or "
              "edited)" % where)
    inputs = out / "inputs.txt"
    a.require(inputs.is_file() and
              "DECLARED_DELTAS_SHA256=%s" % hashlib.sha256(
                  side.read_bytes()).hexdigest() in
              inputs.read_text().splitlines(),
              "the sidecar of %s is not the one its sealed inputs.txt "
              "records" % where)
    return doc


def classify(row):
    """What the gate of the attempt `row` shows, by its decision whenever
    `gate/decisions.json` exists, complete or not (a crash or a signal
    after a decided gate does not undo it). Returns the row with `kind`:
    `void` (no gate decision), `pass` (decided pass or attributed, no
    reasons, the R2 load totals the record declared), `delta-only` (the
    same, but the totals differ from the totals its own record declared,
    the sidecar being bound to the record and the sealed inputs: the
    disposition fails it on the declared deltas alone) or `fail` (any
    other decision or reasons: fail, blocked, a smoke), with `decision`,
    `reasons`, `problems` and `complete`."""
    out = Path(row["output"])
    found = dict(row, decision=None, reasons=[], problems=[],
                 complete=completed(row), kind="void")
    path = out / "gate" / "decisions.json"
    if not path.is_file():
        return found
    decisions = a.load(path)
    found.update(decision=decisions.get("decision"),
                 reasons=list(decisions.get("reasons", [])) + list(
                     decisions.get("blockers", [])))
    declared = bound_sidecar(out)
    if declared is not None and isinstance(
            declared.get("totals"), dict) and set(
                declared["totals"]) == set(LOAD_KINDS) and isinstance(
                    declared.get("archive"), str):
        found["problems"] = declared_problems(declared, decisions)
    clean = not found["reasons"] and found["decision"] in (
        "pass", "attributed")
    found["kind"] = ("fail" if not clean else
                     "delta-only" if found["problems"] else "pass")
    return found


def earlier_attempt(row):
    """What an attempt before the judged one shows, and whether a redraw
    after it is allowed (decisions 21, 25, 26). A redraw is blocked only
    by a draw that stays judged: a COMPLETE attempt whose gate passed
    (superseded), or an attempt, complete or not, whose gate decided fail
    or blocked on grounds other than the declared deltas. It is allowed
    after an attempt that left no gate decision (void), one whose gate
    failed on the declared deltas alone, and one that is incomplete with a
    passing gate (it owed the redraw). Returns the row with `verdict`
    (`void`, `declared-deltas`, `incomplete-pass`), `decision`, `reasons`,
    `problems` and `complete`; the disposition is refused when the redraw
    is not allowed."""
    found = classify(row)
    kind = found.pop("kind")
    if kind == "void":
        return dict(found, verdict="void")
    if kind == "delta-only":
        return dict(found, verdict="declared-deltas")
    if kind == "pass" and not found["complete"]:
        return dict(found, verdict="incomplete-pass")
    raise ValueError(
        "the earlier startup attempt %s (%s) has gate decision %s%s%s: a "
        "redraw is allowed only after a gate that failed on the declared "
        "deltas alone, an incomplete attempt with a passing gate or an "
        "attempt with no gate decision, so that attempt is a draw that "
        "stays judged (design decisions 21, 25, 26)" % (
            row["attempt"],
            "complete" if found["complete"] else "incomplete",
            found["decision"],
            " (%s)" % "; ".join(found["reasons"])
            if found["reasons"] else "",
            "" if found["problems"] else ", which declared deltas it "
            "matched"))


def startup_attempts(ledger, judged):
    """Every attempt of the startup-gate runner in `ledger`, oldest first:
    [{attempt, output, exit, status, judged, verdict, decision, reasons,
    problems}]. The judged gate directory `judged` must lie in the output
    of the LAST attempt, which is closed. Its verdict is `judged` when it
    completed (`completed`: exit 0 or 2 and `done`). An incomplete last
    attempt with no gate decision is void and cannot be judged (the lead
    redraws); one with a gate decision is judged by it (decision 26):
    `judged-incomplete` when the gate decided fail or blocked on grounds
    other than the declared deltas (the gate's result), `owes-redraw` when
    it passed or failed on the declared deltas alone (incomplete, a redraw
    is owed). Every earlier attempt is judged by `earlier_attempt` (R-1:
    it stays in the record with its decision) and a redraw that was not
    allowed refuses."""
    rows = read_ledger(ledger)
    last = rows[-1]
    a.require(last["status"] != "open",
              "the last startup attempt %s is not closed" % last["attempt"])
    inside = Path(judged).resolve().parent == Path(
        last["output"]).resolve()
    a.require(inside, "the judged startup gate %s is not in the last "
              "attempt of the ledger (%s): a later attempt exists, or this "
              "is an earlier one" % (judged, last["output"]))
    found = [dict(earlier_attempt(row), judged=False) for row in rows[:-1]]
    if completed(last):
        return found + [dict(last, judged=True, verdict="judged",
                             decision=None, reasons=[], problems=[])]
    seen = classify(last)
    a.require(seen["kind"] != "void",
              "the last startup attempt %s is void (exit %s, `done` %s, no "
              "gate decision): the runner did not complete, so it cannot "
              "be judged; the lead redraws (R-1)" % (
                  last["attempt"], last["exit"],
                  "written" if (Path(last["output"]) / "done").is_file()
                  else "missing"))
    verdict = "judged-incomplete" if seen.pop("kind") == "fail" \
        else "owes-redraw"
    return found + [dict(seen, judged=True, verdict=verdict)]


def owe_redraw(record, attempt):
    """The startup gate record of a last attempt that owes a redraw
    (`startup_attempts`): incomplete, whatever the gate showed, owing
    `redraw`."""
    why = ("the last startup attempt %s is incomplete (exit %s, gate "
           "decision %s%s) and owes a redraw" % (
               attempt["attempt"], attempt["exit"], attempt["decision"],
               "; declared deltas: " + "; ".join(attempt["problems"])
               if attempt["problems"] else ""))
    return dict(record, source="inconclusive", failed=[],
                missing=["%s: %s" % (STARTUP, why)], owed=["redraw"],
                exit=EXITS["inconclusive"],
                reasons=list(record["reasons"]) + [why])


def replay_startup(out, record):
    import startup_gate as sg
    import argparse
    code = quiet(sg.replay, argparse.Namespace(output=Path(out),
                                               record=record))
    a.require(code == 0, "the startup gate in %s did not replay" % out)


def startup_gate(header, decisions, null_decisions, problems=()):
    """The gate record of the startup gate: its status is that of its
    decision (`pass`, `attributed` with the notes as the attribution,
    `fail`; anything else, a blocked or a smoke run, is inconclusive), and
    a null control that did not pass makes it inconclusive. `problems`
    (`declared_problems`) make it `fail`: the record's declared deltas are
    not the gate's, and nothing is transferred."""
    decision = decisions.get("decision")
    status = decision if decision in ("pass", "attributed", "fail") \
        else "inconclusive"
    reasons = list(decisions.get("reasons", [])) + list(
        decisions.get("blockers", []))
    if problems:
        status = "fail"
        reasons += ["declared deltas: " + p for p in problems]
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
    for gate, report in reports.items():
        check_audit_receipt(gate, report["semantic_gate"])
    return next(iter(reports.values()))["semantic_gate"]["seal"]


def check_audit_receipt(gate, found):
    """The api-audit receipt a loading report names exists, is the sealed
    one and passed with its eight cases (`loading.replay_gate` checks it
    only when the file is there, which a disposition must not allow)."""
    path = Path(str(found.get("receipt")))
    a.require(path.is_file(), "%s: the api-audit receipt is missing: %s"
              % (gate, path))
    a.require(a.seal(path) == found["seal"], "%s: the api-audit receipt "
              "differs from its seal: %s" % (gate, path))
    doc = a.load(path)
    a.require(doc.get("pass") is True and len(doc.get("cases", [])) == 8,
              "%s: the api-audit receipt did not pass: %s" % (gate, path))


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

def same_rev(one, other):
    """Two revisions of at least ten hex digits that are one (either may
    abbreviate the other)."""
    return (isinstance(one, str) and isinstance(other, str) and
            min(len(one), len(other)) >= 10 and
            (one.startswith(other) or other.startswith(one)))


BUILDS_SCHEMA = "task37-builds-v1"


def check_builds_reports(candidate, reports):
    """The sealed reports of the D7 receipt are JSON, and every one that
    carries `pins` or a `task37-builds-v1` schema (the build timing and
    its attribution, `task37-builds-v1-attribution`) names the baseline
    and the candidate of the receipt (`candidate` may abbreviate its
    pin); at least one is a build-timing receipt itself."""
    receipts = 0
    for report in reports:
        name = Path(report).name
        try:
            doc = json.loads(Path(report).read_text())
        except (OSError, ValueError) as error:
            raise ValueError("the %s report %s is not readable JSON: %s" %
                             (D7, name, error))
        if not isinstance(doc, dict):
            continue
        schema = doc.get("schema")
        if not ("pins" in doc or (isinstance(schema, str) and
                                  schema.startswith(BUILDS_SCHEMA))):
            continue
        receipts += schema == BUILDS_SCHEMA
        pins = doc.get("pins")
        a.require(isinstance(pins, dict),
                  "the %s report %s has no pins" % (D7, name))
        a.require(pins.get("base") == a.BASE,
                  "the %s report %s measured baseline %s, not %s" % (
                      D7, name, pins.get("base"), a.BASE))
        a.require(same_rev(candidate, pins.get("cand")),
                  "the %s receipt names candidate %s, the build timing %s "
                  "measured %s" % (D7, candidate, name, pins.get("cand")))
    a.require(receipts, "none of the %s reports is a %s build-timing "
              "receipt" % (D7, BUILDS_SCHEMA))


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
    check_builds_reports(candidate, reports)
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
    check_builds_reports(doc["candidate"],
                         [held["path"] for held in doc["reports"]])
    return dict(doc, seal=a.seal(Path(path)))
