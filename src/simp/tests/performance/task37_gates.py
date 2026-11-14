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
  by the runner at its end; it is not a ledger line), whatever its close
  status (decision 31: a signal after `done` leaves it complete); a
  complete attempt always has a replayed null control, which
  `--startup-null` names (it must be the attempt's own `gate-null`). An
  incomplete last attempt (a failing step, `die`, a signal before `done`,
  or never closed) with no gate decision is void (refused); with one it
  is judged by it (decision 26): a fail or blocked decision, on any
  grounds, the declared deltas alone included, is the gate's result
  (`fail` or inconclusive; a delta-only failure allows a redraw), and
  only a pass leaves it incomplete owing a `redraw`. The null control of
  a failed or blocked incomplete attempt is neither read nor replayed
  (recorded as not applicable). That of one owing a redraw is read and
  replayed when its own `gate-null` holds a complete archive that
  replays, and is otherwise recorded as absent (it cannot change that
  verdict); it is found by itself, and an explicit `--startup-null` there
  must be that complete archive and replay, else it refuses (omit the
  flag). The null of a complete attempt must replay (refused otherwise).
  A gate decision counts iff the sha256 rows of its `gate/receipt.json`
  (which lists `header.json` and `decisions.json`) all match the files
  (`gate_decision`) AND `replay` of the archive, with the attempt's own
  record, returns 0 (`replays`; design decision 28). The
  runner's progress files never decide that: a signal or crash after a
  decided, replayable gate does not undo it. An archive that is absent,
  cut or does not replay gives no decision, and the attempt is void
  (a redraw is allowed) unless it shows progress past `replay-gate`
  (`past_replay_gate`: `done`, `replay-gate.exit` reading `exit=0`, or a
  later step file), when it was damaged after the run and is refused,
  never read as void (`classify`); the reason the replay failed is in the
  message and in the attempt row (`replay`). So is an attempt that closed
  with exit 0 and no `done`, or with exit 2 and no `done` although no hard
  step failed with 2 (`damaged_runner`).
  An attempt is judged by its own harness (decisions 33, 36, 38;
  `harness_tree`, `attempt_harness`, `run_harness`): a temporary tree holds
  the whole performance area (`allocator-counter/` included) as blobs at
  the commit in its `harness-head.txt`, every other path being the
  checkout's through symlinks, and a child process (`python3 -B -E -s`,
  fd 1 kept for its JSON answer) over that tree computes the replay, the
  null, the late replays and the `SCHEMA` and `PAIRS` checks of
  `read_startup`; every judgement goes through a harness handle. The tree
  is refused unless its tree outside the performance area equals the
  checkout HEAD's, and an attempt unless its `harness-head.txt` is the
  harness head of its gate header. The checkout's interpreter never
  imports harness code, and the trees are removed when dispose ends
  (`harness_scope`). A later fix to any harness file therefore never
  locks a disposition out. A replay that returns nonzero or raises is a
  failed replay; anything that keeps the harness from answering (no
  harness commit, a tree that cannot be built, a child that cannot start,
  fails, prints malformed output or lacks `replay`, `SCHEMA` or `PAIRS`)
  is a refusal (the message names the attempt, the commit and the cause).
  A gate not sealed to a record gives no decision. Every
  earlier attempt is judged by
  its gate decision when it has one, complete or not, and recorded; it
  blocks a redraw only when it is complete and passed, or decided fail
  or blocked on grounds other than the declared deltas (void attempts,
  delta-only failures and incomplete passing attempts do not block); a
  sidecar is bound to its record and
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
import collections
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
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
    rows, seen = {}, set()
    for x in doc.get("decisions", []):
        a.require(isinstance(x, dict) and "case" in x and "kind" in x and
                  x.get("decision") in rules.GATES + (
                      rules.REPORTED, rules.UNSUPPORTED),
                  "malformed TASK33 decision: %r" % (x,))
        key = "%s:%s" % (x["case"], x["kind"])
        source = x.get("source", "")
        a.require((key, source) not in seen,
                  "repeated TASK33 decision: %s (source %s)" % (
                      key, source))
        seen.add((key, source))
        rows.setdefault(key, []).append(x)
    found, reported = {}, []
    for key, group in rows.items():
        # Design decision 48: a check decided by several offline
        # sources (one offline check id is decided in every offline
        # report that runs it) is one record, under the key `case:kind`.
        a.require(len(group) == 1 or all(
            x.get("source", "").startswith("offline:") for x in group),
            "repeated TASK33 decision: " + key)
        group = sorted(group, key=lambda x: x.get("source", ""))
        listed = [dict(origin=x.get("source", ""),
                       decision=x["decision"],
                       reason=x.get("reason", "")) for x in group]
        shown = {} if len(group) == 1 else dict(origins=listed)
        reason = "; ".join(dict.fromkeys(
            x["reason"] for x in listed if x["reason"]))
        gated = [x for x in group if x["decision"] in rules.GATES]
        a.require(not gated or len(gated) == len(group),
                  "inconsistent TASK33 decisions (gated and reported "
                  "from different sources): " + key)
        if not gated:
            kinds = sorted({x["decision"] for x in group})
            reported.append(dict(
                key=key, decision=kinds[0] if len(kinds) == 1 else
                rules.UNSUPPORTED, reason=reason, **shown))
            found[key] = None
            continue
        decision = rules.worst([x["decision"] for x in gated])
        owed = set()
        for x in gated:
            if x.get("owed"):
                owed.add(OWED_NAMES.get(x["owed"], x["owed"]))
            elif x["decision"] not in (rules.PASS, rules.FAIL):
                owed.add("attribution")

        def named(x, text):
            return text if not shown else "%s (%s)" % (
                text, x.get("source", ""))
        record = dict(
            key=key, source=decision, owed=sorted(owed), reason=reason,
            failed=[named(x, "TASK33: fail") for x in gated
                    if x["decision"] == rules.FAIL],
            missing=[named(x, "TASK33: " + x["decision"]) for x in gated
                     if x["decision"] not in (rules.PASS, rules.FAIL)],
            **shown)
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

def read_startup(out, null, lineage, harness, label=STARTUP):
    """The startup gate archive `out` (a gate, or with `null` its null
    control): its header and decisions, with the candidate and harness it
    names accepted. The schema and the pair count it must have are those of
    `harness` (the attempt's, `attempt_harness`). Returns (header,
    decisions)."""
    schema, pairs = harness_constants(harness)
    out = Path(out)
    header = read(out / "header.json", label + " header")
    decisions = read(out / "decisions.json", label + " decisions")
    a.require(header.get("schema") == schema and
              bool(header.get("null")) == null,
              "%s is not a%s startup gate archive" % (
                  label, " null" if null else ""))
    a.require(isinstance(header.get("pairs"), int) and
              header["pairs"] >= pairs, "%s has fewer than %d pairs" % (
                  label, pairs))
    lineage.harness(label, header.get("harness"), clean=True)
    a.require(header["harness"].get("head") == harness.head,
              "%s was made by harness commit %s, not the attempt's %s" % (
                  label, header["harness"].get("head"), harness.head))
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


# The steps of the runner (run_startup_gate.sh). A SOFT step that fails
# does not stop the run: its status is recorded and the run goes on, to
# `done` and an exit 2 (only who_pays_s1 returns 2 itself; gate and
# gate-null return 1, check_deltas 1). A HARD step that fails stops it,
# with its own status as the exit status (which may be 2) and no `done`.
# Design decision 33.
SOFT_STEPS = ("who_pays_s1", "gate", "gate-null", "check_deltas")
HARD_STEPS = ("build", "who_pays", "fill_record", "replay-gate",
              "replay-null", "cell-o1-19", "cell-o1-24", "cell-o1-33",
              "cell-o2-24")


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
    """The runner of the attempt ran every step: it wrote `done` (design
    decision 31), whatever its close status (a signal after `done`, or no
    close, leaves the attempt complete)."""
    return (Path(row["output"]) / "done").is_file()


def step_exit(out, name):
    """The text of the step status file `name` of the attempt directory
    `out` (`exit=<status>`), or None when it is not there."""
    try:
        return (Path(out) / name).read_text().strip()
    except OSError:
        return None


# The files of the steps that follow `replay-gate` (run_startup_gate.sh).
LATER_STEPS = ("check_deltas.*", "replay-null.*", "cell-*.exit")


def past_replay_gate(row):
    """The attempt `row` shows progress past `replay-gate` (design decisions
    28, 31): it wrote `done`, `replay-gate.exit` reads `exit=0`, or a later
    step left a file (`LATER_STEPS`). A gate archive that does not replay
    then cannot be a gate that died before its replay: it was damaged."""
    out = Path(row["output"])
    return ((out / "done").is_file() or
            step_exit(out, "replay-gate.exit") == "exit=0" or
            any(next(out.glob(g), None) is not None for g in LATER_STEPS))


def damaged_runner(row):
    """Why the closing status of the attempt `row` contradicts its files,
    or "" (design decision 33). The runner exits 0 only after it wrote
    `done`, so exit 0 without `done` is damage. Any soft step that failed
    leads to `done` and exit 2, so exit 2 without `done` comes only from a
    hard step that failed with 2 (`HARD_STEPS`; its `.exit` reads
    `exit=2`): it is damage unless one does. Of the soft steps' `.exit`
    files only who_pays_s1's can read `exit=2`; the soft steps are left
    out of the test, as a conservative choice. Any other close without
    `done` (a failing step, `die`, a signal) is an incomplete attempt, not
    damage."""
    out = Path(row["output"])
    if (out / "done").is_file():
        return ""
    if row["exit"] == 0 or (row["exit"] == 2 and not any(
            step_exit(out, step + ".exit") == "exit=2"
            for step in HARD_STEPS)):
        return ("the startup attempt %s closed with exit %d and wrote no "
                "`done`%s: it was damaged after the run (R-1)" % (
                    row["attempt"], row["exit"], "" if row["exit"] == 0
                    else ", and no hard step failed with 2"))
    return ""


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


def gate_decision(out):
    """The decisions of the gate archive `out` (`startup_gate.
    write_archive`), or None when the attempt has no gate decision: it
    counts only when `receipt.json` exists, lists `header.json` and
    `decisions.json`, and the sha256 of EVERY file it lists is that of the
    file (a gate cut short, or a truncated, edited or missing file, decided
    nothing)."""
    out = Path(out)
    try:
        receipt = json.loads((out / "receipt.json").read_text())
        if not (isinstance(receipt, dict) and
                {"header.json", "decisions.json"} <= set(receipt) and
                all(isinstance(d, str) and
                    d == hashlib.sha256((out / n).read_bytes()).hexdigest()
                    for n, d in receipt.items())):
            return None
        decisions = json.loads((out / "decisions.json").read_text())
    except (OSError, ValueError):
        return None
    return decisions if isinstance(decisions, dict) else None


def archive_complete(out):
    """The gate archive `out` is a complete one (`gate_decision`)."""
    return gate_decision(out) is not None


def replays(out, record=None, null=False, *, harness):
    """(ok, reason): the startup gate archive `out` replays (the `replay`
    of the `harness` of the attempt, run by a child process over its tree,
    returns 0); `reason` says why not. A gate (not `null`) must be sealed to
    a record (`record_sha256`), which is passed to the replay; a null
    control has none. An archive that cannot be read, or that the harness's
    replay reports as not replaying (a code, or an error it raised), does
    not replay. A harness that could not be run is refused
    (`HarnessRefused`), never read as a replay that failed."""
    out = Path(out)
    try:
        sealed = bool(a.load(out / "header.json").get("record_sha256"))
    except Exception as error:
        return False, "%s: %s" % (type(error).__name__, error)
    if sealed == null:
        return False, ("the archive %s a null control and is sealed to "
                       "%s record" % ("is" if null else "is not",
                                      "a" if sealed else "no"))
    result = run_harness(harness, dict(
        op="replay", output=out,
        record=Path(record) if sealed and record is not None else None))
    if "error" in result:
        return False, result["error"]
    code = result["code"]
    return (True, "") if code == 0 else (
        False, "the replay returned %s" % code)


class HarnessRefused(ValueError):
    """The harness of an attempt cannot be built or run (decision 38)."""


# The harness trees made for this process, by (commit, entry file), and the
# temporary directories that hold them (`release_harness_trees`).
HARNESS_TREES, HARNESS_TMP = {}, []

# What a harness is, for an attempt: its name, its commit, the performance
# directory of its tree and the repository path of its `startup_gate.py`.
Harness = collections.namedtuple("Harness",
                                 "attempt head directory where")


def harness_prefix(path):
    """The path of the directory of the file `path` in its repository, with
    a trailing slash ("" at the top): where the performance area is."""
    return subprocess.run(
        ("git", "-C", str(Path(path).resolve().parent), "rev-parse",
         "--show-prefix"), capture_output=True, check=True,
        stdin=subprocess.DEVNULL, text=True).stdout.strip()


def release_harness_trees():
    """Remove the harness trees made so far."""
    HARNESS_TREES.clear()
    while HARNESS_TMP:
        shutil.rmtree(HARNESS_TMP.pop(), ignore_errors=True)


@contextlib.contextmanager
def harness_scope():
    """The harness trees made inside the block are removed when it ends,
    also by an error or an interrupt."""
    try:
        yield
    finally:
        release_harness_trees()


def harness_tree(head, entry=None):
    """The performance directory of the harness tree of the commit `head`
    (design decision 38), made once per commit under TMPDIR. The tree holds
    every blob of the performance area (the directory of `entry`, by
    default this checkout's `startup_gate.py`) at `head`, at its repository
    path, modes and symlinks kept; at each ancestor level, symlinks to the
    checkout's siblings (`.git` included), so every other path resolves to
    the checkout. Refused (HarnessRefused, a ValueError) when the tree
    outside the area differs from the checkout HEAD's (not a harness of this
    lineage), or when `head` or a blob cannot be read."""
    import startup_gate as sg
    entry = Path(entry or sg.__file__).resolve()
    key = (head, str(entry))
    if key in HARNESS_TREES:
        return HARNESS_TREES[key]

    def git(*argv, **kw):
        return subprocess.run(("git", "-C", str(kw.pop("cwd", entry.parent))
                               ) + argv,
                              capture_output=True, check=True,
                              stdin=kw.pop("stdin", subprocess.DEVNULL),
                              **kw).stdout
    where, base = "", None
    try:
        where = harness_prefix(entry)
        root = Path(git("rev-parse", "--show-toplevel",
                        text=True).strip())
        outside = {}
        for rev in (head, "HEAD"):
            outside[rev] = {}
            for e in git("ls-tree", "-r", "-z", rev, cwd=root).split(b"\0"):
                if e and not e.split(b"\t", 1)[1].decode().startswith(where):
                    meta, name = e.split(b"\t", 1)
                    outside[rev][name.decode()] = meta
        differ = sorted(n for n in set(outside[head]) | set(outside["HEAD"])
                        if outside[head].get(n) != outside["HEAD"].get(n))
        if differ:
            raise ValueError(
                "its tree outside %s differs from the checkout HEAD's, so "
                "it is not a harness of this lineage (%d path%s, first: %s)"
                % (where, len(differ), "" if len(differ) == 1 else "s",
                   ", ".join(differ[:5])))
        listing = [e.split(b"\t", 1) for e in git(
            "ls-tree", "-r", "-z", head, "--", where,
            cwd=root).split(b"\0") if e]
        base = Path(tempfile.mkdtemp(prefix="task37-harness-"))
        HARNESS_TMP.append(base)
        here, there = root, base
        for part in where.strip("/").split("/") if where else ():
            for sibling in sorted(here.iterdir()):
                if sibling.name != part:
                    (there / sibling.name).symlink_to(sibling)
            here, there = here / part, there / part
            there.mkdir()
        blobs = [(m.split(), Path(p.decode())) for m, p in listing]
        blobs = [(m, p) for m, p in blobs if m[1] == b"blob"]
        if not blobs or Path(where, entry.name) not in [p for _, p in blobs]:
            raise ValueError("it has no %s%s" % (where, entry.name))
        data = git("cat-file", "--batch", stdin=None, cwd=root,
                   input=b"".join(m[2] + b"\n" for m, _ in blobs))
        at = 0
        for (mode, _, sha), path in blobs:
            end = data.index(b"\n", at)
            fields = data[at:end].split()
            if fields[:2] != [sha, b"blob"]:
                raise ValueError("blob %s is missing" % sha.decode())
            size = int(fields[2])
            content = data[end + 1:end + 1 + size]
            at = end + 2 + size
            dest = base / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            if mode == b"120000":
                dest.symlink_to(content.decode())
            else:
                dest.write_bytes(content)
                if mode == b"100755":
                    dest.chmod(0o755)
    except (OSError, subprocess.CalledProcessError, ValueError,
            IndexError) as error:
        if base is not None:
            shutil.rmtree(base, ignore_errors=True)
            HARNESS_TMP.remove(base)
        said = getattr(error, "stderr", None) or str(error)
        if isinstance(said, bytes):
            said = said.decode(errors="replace")
        raise HarnessRefused("cannot build the harness tree of %s at the "
                             "harness commit %s: %s" % (
                                 where + entry.name, head,
                                 " ".join(said.split()))) from None
    HARNESS_TREES[key] = base / where
    return base / where


def attempt_harness(row, entry=None):
    """The harness of the attempt `row` (design decision 38): its commit
    (`harness-head.txt`) and the tree made for it (`harness_tree`). Refused
    (ValueError naming the attempt) when the attempt records no harness
    commit, its gate header (`gate/header.json`) does not record that same
    commit as its harness (the gate and the null are tied to one harness
    in `read_startup`), or the tree cannot be built."""
    import startup_gate as sg
    entry = Path(entry or sg.__file__).resolve()
    out = Path(row["output"])
    head = step_exit(out, "harness-head.txt") or ""
    a.require(re.fullmatch(r"[0-9a-f]{40}", head) is not None,
              "the startup attempt %s records no harness commit "
              "(harness-head.txt)" % row["attempt"])
    header = out / "gate" / "header.json"
    who = "the startup attempt %s" % row["attempt"]
    try:
        held = json.loads(header.read_text())
    except OSError:
        raise HarnessRefused("%s ran at harness commit %s, but its gate "
                             "header is missing (%s)" % (who, head, header)
                             ) from None
    except ValueError:
        raise HarnessRefused("%s ran at harness commit %s, but its gate "
                             "header is not JSON (%s)" % (who, head, header)
                             ) from None
    held = held.get("harness") if isinstance(held, dict) else None
    if not isinstance(held, dict):
        raise HarnessRefused("%s ran at harness commit %s, but its gate "
                             "header records no harness" % (who, head))
    if held.get("head") != head:
        raise HarnessRefused("%s ran at harness commit %s "
                             "(harness-head.txt), but its gate header "
                             "records %s" % (who, head, held.get("head")))
    try:
        directory = harness_tree(head, entry)
    except HarnessRefused as error:
        raise HarnessRefused("the startup attempt %s: %s" % (
            row["attempt"], error)) from None
    return Harness(row["attempt"], head, directory,
                   harness_prefix(entry) + entry.name)


# The child of `run_harness`: it runs in the performance directory of a
# harness tree, imports that tree's `startup_gate` and prints one JSON
# object. The contract with the harness is `replay(args)` (args.output and
# args.record, absolute paths or None), `SCHEMA` and `PAIRS`. Fd 1 is
# pointed at stderr first, and the JSON is written to a saved duplicate of
# the original fd 1, so nothing the harness writes can corrupt it.
DRIVER = r"""
import argparse, json, os, pathlib, sys
saved = os.dup(1)
os.dup2(2, 1)
request = json.loads(sys.argv[1])
sys.path.insert(0, os.getcwd())
import startup_gate as sg
missing = [n for n in ("replay", "SCHEMA", "PAIRS") if not hasattr(sg, n)]
result = {"missing": missing}
if not missing:
    result = {"SCHEMA": sg.SCHEMA, "PAIRS": sg.PAIRS}
    if request["op"] == "replay":
        record = request["record"]
        try:
            result["code"] = sg.replay(argparse.Namespace(
                output=pathlib.Path(request["output"]),
                record=None if record is None else pathlib.Path(record)))
        except Exception as error:
            result["error"] = "%s: %s" % (type(error).__name__, error)
sys.stdout.flush()
with os.fdopen(saved, "w") as stream:
    stream.write(json.dumps(result))
"""


def run_harness(harness, request):
    """The result (a dict) of `request` ({"op": "replay", "output",
    "record"} or {"op": "constants"}) run by the child process of the
    `harness`: `SCHEMA` and `PAIRS`, and for a replay `code` or `error`
    (the replay failed). The paths of the request are made absolute. The
    child is `python3 -B -E -s` with this environment (no `PYTHON*`
    variable is honoured), no stdin, and runs in the harness tree. Output is
    read as bytes and decoded with replacement. Anything that keeps the
    harness from answering is a refusal (`HarnessRefused`) naming the
    attempt, the commit and the cause or the child's stderr tail: failing
    to start it, a missing tree, a non-zero exit, malformed output, a
    missing `replay`, `SCHEMA` or `PAIRS`. An interrupt kills the child
    and propagates."""
    who = "the startup attempt %s (harness commit %s)" % (
        harness.attempt, harness.head)
    request = dict(request)
    for key in ("output", "record"):
        if request.get(key) is not None:
            request[key] = str(Path(request[key]).resolve())

    def refuse(cause):
        return HarnessRefused("%s: cannot run its harness: %s: %s" % (
            who, type(cause).__name__, " ".join(str(cause).split())))
    try:
        child = subprocess.Popen(
            (sys.executable, "-B", "-E", "-s", "-c", DRIVER,
             json.dumps(request)),
            cwd=str(harness.directory), stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=dict(os.environ), start_new_session=True)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        raise refuse(error) from None
    try:
        out, err = child.communicate()
    except BaseException as error:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except OSError:
            pass
        child.wait()
        child.stdout.close()
        child.stderr.close()
        if isinstance(error, (OSError, ValueError)):
            raise refuse(error) from None
        raise
    out, err = (x.decode("utf-8", errors="replace") for x in (out, err))
    tail = " ".join(err.split())[-400:]
    if child.returncode != 0:
        raise HarnessRefused("%s: its harness exited %s: %s" % (
            who, child.returncode, tail))
    try:
        result = json.loads(out)
        a.require(isinstance(result, dict), "not an object")
    except ValueError:
        raise HarnessRefused("%s: its harness printed malformed output "
                             "(%s)" % (who, " ".join(out.split())[-200:]
                                       or tail)) from None
    if "missing" in result:
        raise HarnessRefused("%s: %s lacks %s" % (
            who, harness.where, ", ".join(result["missing"])))
    if request["op"] == "replay" and \
            ("code" in result) == ("error" in result):
        raise HarnessRefused("%s: its replay gave neither a code nor an "
                             "error" % who)
    return result


def harness_constants(harness):
    """(SCHEMA, PAIRS) of the harness of an attempt."""
    result = run_harness(harness, dict(op="constants"))
    return result["SCHEMA"], result["PAIRS"]


def judge_gate(row):
    """(decisions, damage, reason) of the gate of the attempt `row`: its
    decisions when they count (`classify`, else None), the message that
    says why the attempt is damaged (else "") and why the archive did not
    replay (else "")."""
    out = Path(row["output"])
    damage = damaged_runner(row)
    decisions = gate_decision(out / "gate")
    reason = ""
    if decisions is not None:
        ok, reason = replays(out / "gate", out / "not-client-visible.md",
                             harness=attempt_harness(row))
        if not ok:
            decisions = None
    if decisions is None and not damage and past_replay_gate(row):
        damage = ("the startup attempt %s got past replay-gate and its "
                  "gate archive shows no gate decision now (a receipt row "
                  "differs, a file is missing or it does not replay%s): it "
                  "was damaged after the run, which a redraw would hide "
                  "(R-1)" % (row["attempt"],
                             ": " + reason if reason else ""))
    return decisions, damage, reason


def classify(row):
    """What the gate of the attempt `row` shows, by its decision whenever
    the attempt has one, complete or not (design decision 28). A gate
    decision counts iff all the receipt rows of `<output>/gate` match
    (`gate_decision`) AND the archive replays (`replays`, with the
    attempt's own `not-client-visible.md` as the record). The runner's
    progress files never decide that, so a signal or crash after a decided,
    replayable gate does not undo the decision. Returns the row with
    `kind`: `void` (no gate decision), `pass` (decided pass or attributed,
    no reasons, the R2 load totals the record declared), `delta-only` (the
    same, but the totals differ from the totals its own record declared,
    the sidecar being bound to the record and the sealed inputs: the
    disposition fails it on the declared deltas alone) or `fail` (any
    other decision or reasons: fail, blocked, a smoke), with `decision`,
    `reasons`, `problems`, `complete` and `damaged`: a message, or "" when
    the attempt is not damaged. An archive that is absent, cut or does not
    replay gives no decision: the attempt is void (a redraw is allowed)
    unless it shows progress past `replay-gate` (`past_replay_gate`), in
    which case it was damaged after the run and is refused (R-1); `replay`
    is the reason the replay failed. An attempt whose closing status
    contradicts its files is damaged too (`damaged_runner`)."""
    out = Path(row["output"])
    decisions, damage, reason = judge_gate(row)
    found = dict(row, decision=None, reasons=[], problems=[],
                 complete=completed(row), kind="void", damaged=damage,
                 replay=reason)
    if decisions is None:
        return found
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
    after it is allowed (decisions 21, 25, 26). A damaged attempt
    (`classify`) is refused outright. A redraw is blocked only
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
    damage = found.pop("damaged")
    a.require(not damage, damage)
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
    problems}]. The judged gate directory `judged` must be the `gate` of
    the output of the LAST attempt, which may be open (never closed). Its
    verdict is `judged` when it completed (`completed`: it wrote `done`,
    whatever its close status; its gate must replay, else it is damaged).
    A damaged attempt
    (`classify`) is refused. An incomplete last
    attempt with no gate decision is void and cannot be judged (the lead
    redraws); one with a gate decision is judged by it (decision 26):
    `judged-incomplete` when the gate failed or was blocked, on any
    grounds, the declared deltas alone included (the gate's result, a
    `fail`; a redraw is allowed), `owes-redraw` only when it passed
    (incomplete, a redraw is owed). Every earlier attempt is judged by
    `earlier_attempt` (R-1: it stays in the record with its decision) and
    a redraw that was not allowed refuses."""
    rows = read_ledger(ledger)
    last = rows[-1]
    inside = Path(judged).resolve() == Path(
        last["output"]).resolve() / "gate"
    a.require(inside, "the judged startup gate %s is not the gate of the "
              "last attempt of the ledger (%s): a later attempt exists, "
              "or this is an earlier one" % (judged, last["output"]))
    found = [dict(earlier_attempt(row), judged=False) for row in rows[:-1]]
    if completed(last):
        damage = judge_gate(last)[1]
        a.require(not damage, damage)
        return found + [dict(last, judged=True, verdict="judged",
                             decision=None, reasons=[], problems=[],
                             replay="")]
    seen = classify(last)
    damage = seen.pop("damaged")
    a.require(not damage, damage)
    a.require(seen["kind"] != "void",
              "the last startup attempt %s is void (exit %s, `done` %s, no "
              "gate decision%s): the runner did not complete, so it cannot "
              "be judged; the lead redraws (R-1)" % (
                  last["attempt"], last["exit"],
                  "written" if (Path(last["output"]) / "done").is_file()
                  else "missing",
                  ": " + seen["replay"] if seen["replay"] else ""))
    verdict = "owes-redraw" if seen.pop("kind") == "pass" \
        else "judged-incomplete"
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


def replay_startup(out, record, harness):
    """The late replay of the archive `out` (design decision 28), by the
    attempt's `harness`: refused unless the replay returns 0."""
    result = run_harness(harness, dict(op="replay", output=out,
                                       record=record))
    a.require(result.get("code") == 0,
              "the startup gate in %s did not replay%s" % (
                  out, ": " + result["error"] if "error" in result
                  else " (returned %s)" % result.get("code")))


def startup_gate(header, decisions, null_decisions, problems=()):
    """The gate record of the startup gate: its status is that of its
    decision (`pass`, `attributed` with the notes as the attribution,
    `fail`; anything else, a blocked or a smoke run, is inconclusive), and
    a null control that did not pass makes it inconclusive (`null_decisions`
    is None when the null is not read: a judged-incomplete attempt, whose
    gate failed or was blocked, or an attempt owing a redraw whose null is
    absent or does not replay, which `task37_dispose.py` accepts for an
    incomplete attempt only). `problems`
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
    if status != "fail" and null_decisions is not None and \
            null_decisions.get("decision") != "pass":
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

# The build bases D7 accepts besides the baseline a.BASE: the full sha of
# a commit, mapped to its declaration. The commit is the baseline's child
# that changes exactly `paths` (and nothing else), each to the candidate's
# own blob, so that the baseline builds from a fresh tree. It need not be
# in any branch, only readable in the repository the report names
# (`pins["repo"]`); `check_builds_reports` verifies all of this there.
BUILD_BASES = {
    "cc64561e81e19167427c0e2a89067e2894ad3b50": dict(
        parent=a.BASE,
        paths=("src/portableML/rawtheory/mktool.ML",),
        why="the baseline does not build from a fresh tree (upstream "
        "1a3864f654 moved the directory scan of theorystats into "
        "theoryfiles but left mktool.ML without it); the candidate's "
        "fix (cf1f863b4e)"),
}


# What would redirect git away from the repository a report names.
GIT_REDIRECTS = ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
                 "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES")


def git_out(repo, *argv):
    """The output of `git -C repo argv` (replacement objects ignored, the
    environment's repository redirections removed), or None when it
    fails."""
    env = {k: v for k, v in os.environ.items() if k not in GIT_REDIRECTS}
    try:
        done = subprocess.run(
            ("git", "--no-replace-objects", "-C", str(repo)) + argv,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True, env=env)
    except OSError:
        return None
    return done.stdout.strip() if done.returncode == 0 else None


def check_build_base(name, pins, base, fallback=None):
    """The declared build base `base` of the report `name`, verified in
    the repository the report names (`pins["repo"]`, else `fallback`, the
    disposition's own): the commit exists there, its only parent is the
    declared parent (which is the baseline), it differs from the parent in
    exactly the declared paths, and each of them is the candidate's own
    (same mode and object)."""
    declared = BUILD_BASES[base]
    a.require(declared["parent"] == a.BASE,
              "the %s build base %s is declared over %s, not the baseline "
              "%s" % (D7, base, declared["parent"], a.BASE))
    repos = [r for r in (pins.get("repo"), fallback)
             if isinstance(r, (str, Path)) and Path(r).is_dir()]
    a.require(repos, "the %s report %s names build base %s, declared, but "
              "its repository %s is not readable, so it cannot be "
              "verified" % (D7, name, base, pins.get("repo")))
    found = [r for r in repos
             if git_out(r, "cat-file", "-t", base) == "commit"]
    a.require(found, "the %s build base %s is not a commit of %s; "
              "recreate it as PROTOCOL.md, D7 build base, says" % (
                  D7, base, " or ".join(str(r) for r in repos)))
    repo = found[0]
    commits = {}
    for label, rev in (("parent", declared["parent"]),
                       ("candidate", pins.get("cand"))):
        commits[label] = git_out(
            repo, "rev-parse", "--verify", "--quiet",
            "%s^{commit}" % rev) if isinstance(rev, str) else None
        a.require(commits[label],
                  "the %s build base check of %s: the %s %s is not a "
                  "commit of %s" % (D7, name, label, rev, repo))
    raw = (git_out(repo, "cat-file", "commit", base) or "").split("\n\n")[0]
    parents = [x.split()[1] for x in raw.splitlines()
               if x.startswith("parent ") and len(x.split()) == 2]
    a.require(parents == [commits["parent"]],
              "the %s build base %s has parents %s, not only %s" % (
                  D7, base, parents, commits["parent"]))
    changed = (git_out(repo, "diff-tree", "-r", "--no-renames",
                       "--name-only", commits["parent"], base)
               or "").splitlines()
    a.require(sorted(changed) == sorted(declared["paths"]),
              "the %s build base %s changes %s, not exactly %s" % (
                  D7, base, sorted(changed), sorted(declared["paths"])))
    for path in declared["paths"]:
        mine, theirs = (
            (git_out(repo, "ls-tree", rev, "--", path) or "").split("\t")[0]
            for rev in (base, commits["candidate"]))
        a.require(mine and mine == theirs,
                  "the %s build base %s has %s as [%s], not the "
                  "candidate's [%s]" % (D7, base, path, mine, theirs))
    return dict(commit=base, parent=declared["parent"],
                paths=list(declared["paths"]), why=declared["why"])


def check_builds_reports(candidate, reports, fallback=None):
    """The sealed reports of the D7 receipt are JSON, and every one that
    carries `pins` or a `task37-builds-v1` schema (the build timing and
    its attribution, `task37-builds-v1-attribution`) names the candidate
    of the receipt (`candidate` may abbreviate its pin) and one baseline:
    a.BASE or one build base of BUILD_BASES (verified, see
    `check_build_base`; `fallback` is a repository to look in when the
    report's own has gone), the same in every report; at least one is a
    build-timing receipt itself. Returns the declaration of the build base
    timed, or None when it is a.BASE."""
    receipts = 0
    bases = []
    build = None
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
        base = pins.get("base")
        a.require(base == a.BASE or base in BUILD_BASES,
                  "the %s report %s measured baseline %s, not %s or a "
                  "declared build base (%s)" % (
                      D7, name, base, a.BASE, ", ".join(BUILD_BASES)))
        bases.append((str(Path(report).resolve()), base))
        a.require(same_rev(candidate, pins.get("cand")),
                  "the %s receipt names candidate %s, the build timing %s "
                  "measured %s" % (D7, candidate, name, pins.get("cand")))
        if base != a.BASE:
            build = check_build_base(name, pins, base, fallback)
    a.require(receipts, "none of the %s reports is a %s build-timing "
              "receipt" % (D7, BUILDS_SCHEMA))
    a.require(len({b for _, b in bases}) == 1,
              "the %s reports name different baselines: %s" % (
                  D7, ", ".join("%s: %s" % kv for kv in bases)))
    return build


def make_receipt(gate, candidate, status, exit_status, reports=(),
                 attribution=(), note=""):
    """The receipt of the D7 build timing, which is reported and never a
    gate: its status and exit are typed, so the exit must be that of the
    status, and at least one sealed report must back it. `baseline` is the
    gate's; a declared build base that was timed instead is recorded as
    `build_base`."""
    a.require(gate == D7, "a receipt is made for %s only; the other gates "
              "are replayed" % D7)
    a.require(status in RECEIPT_STATUS, "unknown status " + status)
    a.require(exit_status == EXITS[status],
              "exit %d is not that of %s (%d)" % (
                  exit_status, status, EXITS[status]))
    a.require(reports, "a receipt needs at least one sealed --report")
    build = check_builds_reports(candidate, reports)
    made = dict(schema=RECEIPT_SCHEMA, gate=gate, candidate=candidate,
                baseline=a.BASE, status=status, exit=exit_status,
                attribution=list(attribution), note=note,
                reports=[dict(path=str(Path(p).resolve()),
                              seal=a.seal(Path(p))) for p in reports])
    if build is not None:
        made["build_base"] = build
    return made


def same_build_base(recorded, found):
    """The recorded build base is the one verified: the commit, its parent
    and its paths (the prose `why` is recorded, not checked)."""
    if recorded is None or found is None:
        return recorded is None and found is None
    return (isinstance(recorded, dict) and
            all(recorded.get(k) == found[k] for k in ("commit", "parent"))
            and sorted(recorded.get("paths") or ()) == sorted(found["paths"]))


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
    build = check_builds_reports(
        doc["candidate"], [held["path"] for held in doc["reports"]],
        getattr(lineage, "repo", None))
    a.require(same_build_base(doc.get("build_base"), build),
              "the %s receipt records build base %s, its reports timed %s"
              % (D7, doc.get("build_base"), build))
    return dict(doc, seal=a.seal(Path(path)))
