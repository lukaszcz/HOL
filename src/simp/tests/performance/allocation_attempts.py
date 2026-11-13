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
only if it admitted no measurement, as `void_attempts.void_failure` says
for the timing grids and here shown from its own output: exactly one close,
`failed`; no resume; its output directory exists and holds no cell archive
(`*.json.xz`, also a `.partial` one), no decisions and no inventory row.
Everything else, an attempt left open, resumed, closed twice, closed with
another status, or whose output is missing or holds a cell, is judged: it
cannot be redrawn, and `attempts_of` refuses it unless it is the judged one.
The legacy tasks write no ledger.
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

    def __init__(self, task, repo, output, counts_file, resume):
        self.task, self.repo = check_task(task), Path(repo).resolve()
        self.output, self.resume = Path(output).resolve(), resume
        self.counts_file = Path(counts_file)
        self.path = ledger_path(self.repo, self.task)
        self.header = None

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

    def line(self, event, **more):
        tg.ledger_append(
            self.path, event=event, stage=STAGE, table=self.task,
            attempt=attempt_id(self.output),
            candidate=self.header["candidate"],
            counts_file=self.counts_file.name,
            counts=hashlib.sha256(self.counts_file.read_bytes()).hexdigest(),
            output=str(self.output), checkout=str(self.repo), **more)

    def start(self, header):
        """Before the first process: the opening (or the resumption). It
        must be written, so a failure refuses the run."""
        self.header = dict(header, candidate=a.git(
            self.repo, "rev-parse", "--verify", header["candidate"] +
            "^{commit}"))
        self.check_ignored()
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.line("resume" if self.resume else "open")

    def close(self, status, **note):
        """The close; when it cannot be written the attempt stays open in
        the ledger (so judged) and the line printed carries it."""
        if self.header is None:
            return
        try:
            self.line("close", status=status, **note)
        except Exception as error:
            print("ATTEMPT-NOT-CLOSED %s (outcome %s): %s" % (
                attempt_id(self.output), status, error), file=sys.stderr,
                flush=True)


def void_failure(output, row):
    """None when the attempt whose ledger output is `output` and whose
    ledger row (`Ledger.attempts`) is `row` is void, else the condition it
    fails (the module docstring)."""
    if output is None or not Path(output).is_dir():
        return "its output directory is missing"
    output = Path(output)
    cells = sorted(p.name for p in output.iterdir()
                   if ".json.xz" in p.name)
    if cells:
        return "its output holds cell archives: %s" % ", ".join(cells[:3])
    if list(output.glob("decisions*.json")):
        return "its output holds decisions"
    if (output / "inventory.json").is_file():
        runs = a.load(output / "inventory.json").get("runs")
        if runs != []:
            return "its inventory records cells"
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
    return None


def attempts_of(task, ledger, judged=None):
    """Every attempt of `task` in `ledger` (a path, as a clone's
    `ledger_path` or another's, read-only): the judged ones (`judged`:
    {attempt id: output directory} of the runs a disposition is given) and
    the others, which must be void. [{attempt, status, output, judged,
    void}], in the order the ledger names them. Refused: no ledger, an
    attempt of more than one output, a judged attempt in another output
    than the one given, a judged id the ledger does not know, and any other
    attempt that is not void (it may have measured: it needs a new policy
    decision)."""
    name = check_task(task)
    judged = {k: Path(v).resolve() for k, v in (judged or {}).items()}
    sc.require(Path(ledger).is_file(), "no attempts ledger: %s" % ledger)
    state = tg.Ledger(ledger)
    where = {}
    for record in state.records:
        if record["event"] in ("open", "resume", "close") and \
                record.get("table") == name:
            outputs = where.setdefault(record.get("attempt"), [])
            if record.get("output") not in outputs:
                outputs.append(record.get("output"))
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
        found.append(entry)
    return found
