"""The attempts ledger of the TASK37 allocation tasks (rule R-1).

Every `run` (and `run --resume`) of `task37-matrix`, `task37-client` and
`task37-downstream` appends to one ledger per task and clone,
`<repo>/.agent-files/evidence/<task>/attempts.jsonl` (excluded from git, as
the timing ledger is), with the machinery of the timing ledger:
`timing_grid.Ledger` (the hash chain, the torn-line rule, `attempts()`)
and `timing_grid.ledger_append`. Its lines are `open` (stage `first`)
once the output exists and the grid is about to measure, `resume` for a
`--resume`, and `close` with a status: the status of the decisions
(`pass`, `fail`, `inconclusive`), or `failed` when the run raised. Each
line names `table` (the task), `attempt`, `candidate` (the full sha),
`output`, `checkout`, `counts_file` and `counts` (its sha256), and a close
`failure` (the error) when it is `failed`. The attempt is of one output:
`attempt_id(output)`.

An attempt is void, and its settings may be drawn again as a new attempt,
only if it admitted no measurement (design decision 30, as the TASK32 rule
"every archived measuring process rejected"): exactly one close, `failed`;
no resume; its output directory exists and holds no decisions; and every
cell archive it holds (`*.json.xz`) is rejected on replay: `rejections`
replays each with `allocation_matrix.replay_cell` and the binding of its
inventory row, which must raise the archive's refusal (so it admitted no
record), and the row, if any, must agree (`rejected` set, status
`unresolved`). Replay decides, never the inventory alone: a row that says
rejected over an archive that replays to a record leaves the attempt
judged. A `.partial` archive counts as a cell not shown rejected, and so
does an archive that is not replayable (no inventory row for it, or a
failure that is not a refusal). Everything else, an attempt left open,
resumed, closed twice, closed with another status, whose output is missing
or holds decisions or a cell that is not shown rejected, is judged: it
cannot be redrawn, and `attempts_of` refuses it unless it is the judged
one. The rejections of a void attempt (archive and reason) are in its entry
and listed in the disposition. The legacy tasks write no ledger.

One output, one attempt: an `open` (a run that is not a `--resume`) whose
attempt is already in the ledger is refused before anything is built, so
an earlier measured failure of the output cannot be hidden behind a later
attempt; a redraw after a void attempt uses a new output path and must not
delete the void attempt's output (which `attempts_of` needs to see void).
`attempts_of` also refuses an attempt with more than one `open`.

A run that is not a judged attempt is an information run, recorded as
`info` and `info-end` lines (the timing grids' information runs, which
R-1 does not judge) and never as `open`, `resume` or `close`: `check-jobs`,
any run with `--only`, and any run with fewer pairs than the task's (a
smoke). It cannot take the output of a judged attempt, and a judged one
cannot take the output of an information run.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
import acceptance as a
import allocation_schema as sc
import timing_grid as tg

TASKS = ("task37-matrix", "task37-client", "task37-downstream")
STAGE = "first"
JUDGED = {"open", "resume", "close"}
FAILED = "failed"


def check_task(task):
    name = getattr(task, "name", task)
    sc.require(name in TASKS, "no attempts ledger for task %r" % (name,))
    return name


def ledger_path(repo, task):
    return (Path(repo).resolve() / ".agent-files" / "evidence" /
            check_task(task) / "attempts.jsonl")


def attempt_id(output):
    """The attempt of an output directory: its resolved path, so that a
    resumption is the same attempt and a copy is another."""
    return hashlib.sha256(
        str(Path(output).resolve()).encode()).hexdigest()[:16]


def status_of(code):
    """The close status of a run that ended with exit status `code`."""
    return {0: "pass", 1: "fail"}.get(code, "inconclusive")


class Attempt:
    """The ledger lines of one run: open or resume, then one close."""

    def __init__(self, task, repo, output, counts_file, resume, info=False):
        self.task, self.repo = check_task(task), Path(repo).resolve()
        self.output, self.resume = Path(output).resolve(), resume
        self.counts_file, self.info = Path(counts_file), bool(info)
        self.path = ledger_path(self.repo, self.task)
        self.header = None
        self.closed = False

    def check_ignored(self):
        if not self.path.resolve().is_relative_to(self.repo):
            return
        found = subprocess.run(
            ["git", "-C", str(self.repo), "check-ignore", "-q",
             str(self.path)], stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL)
        sc.require(found.returncode == 0, "the attempts ledger would be "
                  "tracked by git: exclude .agent-files first: %s"
                  % self.path)

    def line(self, candidate, event, **more):
        tg.ledger_append(
            self.path, event=event, stage=STAGE, table=self.task,
            attempt=attempt_id(self.output), candidate=candidate,
            counts_file=self.counts_file.name,
            counts=hashlib.sha256(self.counts_file.read_bytes()).hexdigest(),
            output=str(self.output), checkout=str(self.repo), **more)

    def events(self):
        """The events of this attempt already in the ledger."""
        if not self.path.is_file():
            return []
        me = attempt_id(self.output)
        return [r["event"] for r in tg.Ledger(self.path).records
                if r.get("table") == self.task and r.get("attempt") == me]

    def check_new(self):
        """The output has no attempt of the other kind, and a fresh
        (non-resume) judged run has none at all: one output, one attempt.
        Refused before anything is built."""
        seen = self.events()
        sc.require(not (self.info and set(seen) & JUDGED),
                   "the output %s is that of a judged attempt of %s: use "
                   "a new output path" % (self.output, self.task))
        sc.require(self.info or self.resume or not seen,
                   "the attempts ledger of %s already has the output %s "
                   "(one output, one attempt): use a new output path, "
                   "keeping the old output" % (self.task, self.output))
        sc.require(self.info or "info" not in seen,
                   "the output %s was an information run of %s: use a new "
                   "output path" % (self.output, self.task))

    def start(self, header):
        """Before the first process: the opening (or the resumption), or
        the `info` line of an information run. It must be written, so a
        failure refuses the run (and the attempt stays unopened)."""
        candidate = a.git(self.repo, "rev-parse", "--verify",
                          header["candidate"] + "^{commit}")
        self.check_ignored()
        self.check_new()
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.line(candidate, "info" if self.info else
                  "resume" if self.resume else "open",
                  **(dict(mode="allocation") if self.info else {}))
        self.header = dict(header, candidate=candidate)

    def close(self, status, **note):
        """The close; when it cannot be written the attempt stays open in
        the ledger (so judged) and the line printed carries it. An
        information run ends with `info-end` and whether it passed.
        Returns whether the line was written (False when the attempt was
        never opened)."""
        if self.header is None:
            return False
        if self.closed:
            return True
        try:
            if self.info:
                self.line(self.header["candidate"], "info-end",
                          success=status == "pass", status=status, **note)
            else:
                self.line(self.header["candidate"], "close", status=status,
                          **note)
            self.closed = True
        except Exception as error:
            print("ATTEMPT-NOT-CLOSED %s (outcome %s): %s" % (
                attempt_id(self.output), status, error), file=sys.stderr,
                flush=True)
            return False
        return True


def rejections(output):
    """([(archive, reason)], None) when every cell archive of `output`
    (`*.json.xz`) is rejected on replay, else ([], the condition it fails).
    Replay decides: each archive is replayed (`allocation_matrix.
    replay_cell`, with the binding of its inventory row) and must raise the
    archive's refusal, so that it admitted no record; the reason is that
    refusal. An archive that replays to a record, a `.partial` one, one with
    no inventory row to replay it by, one whose row does not agree
    (`rejected` set, status `unresolved`), a row with no archive, and an
    archive that fails otherwise than by a refusal, are cells not shown
    rejected. No archive at all is vacuously rejected."""
    import allocation_matrix as am
    output = Path(output)
    held = sorted(p.name for p in output.iterdir() if ".json.xz" in p.name)
    partial = [n for n in held if not n.endswith(".json.xz")]
    if partial:
        return [], ("its output holds an archive not shown rejected: %s"
                    % ", ".join(partial[:3]))
    inventory, rows = None, {}
    if (output / "inventory.json").is_file():
        inventory = a.load(output / "inventory.json")
        runs = inventory.get("runs")
        if not isinstance(runs, list):
            return [], "its inventory has no list of cells"
        rows = {r.get("archive"): r for r in runs if isinstance(r, dict)}
        if len(rows) != len(runs):
            return [], "its inventory has malformed or repeated cells"
        missing = sorted(set(rows) - set(held))
        if missing:
            return [], ("its inventory has a cell with no archive: %s" %
                        ", ".join(map(str, missing[:3])))
    elif held:
        return [], ("its output holds cell archives and no inventory to "
                    "replay them by: %s" % ", ".join(held[:3]))
    found = []
    for name in held:
        row = rows.get(name)
        if row is None:
            return [], "no inventory row for the archive %s" % name
        if not row.get("rejected") or row.get("status") != "unresolved":
            return [], ("the inventory does not show the cell %s rejected "
                        "(rejected and status unresolved)" % name)
        try:
            am.replay_cell(output / name, am.row_binding(inventory, row))
        except sc.InvalidAllocation as error:
            # the refusal of the replay, and the reason the run recorded
            found.append((name, "%s (recorded: %s)" % (
                error, row["rejected"])))
        except Exception as error:
            return [], ("the archive %s does not replay to a refusal: %r" %
                        (name, error))
        else:
            return [], ("the archive %s admitted a record on replay" %
                        name)
    return found, None


def void_failure(output, row):
    """None when the attempt whose ledger output is `output` and whose
    ledger row (`Ledger.attempts`) is `row` is void, else the condition it
    fails (the module docstring)."""
    if output is None or not Path(output).is_dir():
        return "its output directory is missing"
    output = Path(output)
    if list(output.glob("decisions*.json")):
        return "its output holds decisions"
    status = row["status"] if row else None
    if status is None or status == "interrupted":
        return "its ledger has no close (it was left open)"
    if row["resumed"]:
        return ("it was resumed: a resumed attempt may have measured "
                "cells before")
    if row["statuses"] != [FAILED]:
        if len(row["statuses"]) > 1:
            return ("it closed more than once, as %s" %
                    ", ".join(row["statuses"]))
        return "its ledger closes it %s, not %s" % (status, FAILED)
    return rejections(output)[1]


def attempts_of(task, ledger, judged=None):
    """Every attempt of `task` in `ledger` (a path, as a clone's
    `ledger_path` or another's, read-only): the judged ones (`judged`:
    {attempt id: output directory} of the runs a disposition is given) and
    the others, which must be void. [{attempt, status, output, judged,
    void}, and for a void one `rejections`: [{archive, reason}] of the
    cells it held], in the order the ledger names them. Refused: no ledger, an
    attempt of more than one output, a judged attempt in another output
    than the one given, a judged id the ledger does not know, and any other
    attempt that is not void (it may have measured: it needs a new policy
    decision), and an attempt that was opened more than once. The `info`
    lines of information runs are not attempts and are ignored."""
    name = check_task(task)
    judged = {k: Path(v).resolve() for k, v in (judged or {}).items()}
    sc.require(Path(ledger).is_file(), "no attempts ledger: %s" % ledger)
    state = tg.Ledger(ledger)
    where, opens = {}, {}
    for record in state.records:
        if record["event"] in JUDGED and record.get("table") == name:
            outputs = where.setdefault(record.get("attempt"), [])
            if record.get("output") not in outputs:
                outputs.append(record.get("output"))
            if record["event"] == "open":
                key = record.get("attempt")
                opens[key] = opens.get(key, 0) + 1
    rows = {k[0]: r for k, r in state.attempts(name).items()}
    unknown = sorted(set(judged) - set(rows))
    sc.require(not unknown, "judged attempt not in the ledger of %s: %s"
              % (name, ", ".join(unknown)))
    found = []
    for key, row in rows.items():
        outputs = where.get(key, [])
        sc.require(len(outputs) == 1,
                  "attempt %s of %s ran in %s output: %s; one attempt is "
                  "of one output" % (key, name, "more than one"
                                     if outputs else "no",
                                     ", ".join(map(str, outputs))))
        sc.require(opens.get(key, 0) <= 1,
                  "attempt %s of %s was opened %d times: an earlier "
                  "attempt of the output may be hidden; one output, one "
                  "attempt" % (key, name, opens[key]))
        output = outputs[0]
        entry = dict(attempt=key, status=row["status"], output=output,
                     judged=key in judged, void=False)
        if entry["judged"]:
            sc.require(output is not None and
                      Path(output).resolve() == judged[key],
                      "attempt %s of %s is judged, from %s, but the "
                      "ledger has it in %s" % (key, name, judged[key],
                                               output))
        else:
            failed = void_failure(output, row)
            sc.require(failed is None,
                      "attempt %s of %s (status %s, output %s) is not "
                      "void: %s; only a void attempt (no admitted "
                      "measurement) may stand beside the judged one" % (
                          key, name, row["status"], output, failed))
            entry["void"] = True
            entry["rejections"] = [
                dict(archive=n, reason=r) for n, r in rejections(output)[0]]
        found.append(entry)
    return found
