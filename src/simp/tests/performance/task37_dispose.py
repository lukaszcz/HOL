#!/usr/bin/env python3
"""The TASK37 disposition: one decision for every required workload.

TASK37 reruns the final performance gate at the final candidate. This
command joins what the measurement stages produced into ONE disposition
(`disposition.json`, with a short `SUMMARY.txt`), the way `task31_dispose.py`
joins TASK31's three gates. Every input is named by an explicit path
option, and the streams of the measurement may live in different clones
(each timing table has its own ledger). A missing input is a refusal, never
a pass. The one thing it looks up is git: the commits the inputs name are
looked up in the checkout that holds this code.

TASK37 protocol (the decision rule is design decision 11)
---------------------------------------------------------

Cells. The matrix (every MatrixPerformance case at every size: the TASK29
and TASK30 families, 306 cells), the client cells (the TASK31 cells, 278)
and the downstream cells (11): `task37_cases.py`, the one place the cell
sets, samples and policy lists are defined. A cell passes if and only if

- identity: its row in the identity table of its kind is `identical` or
  `attributed` (`different` fails; anything else is not a decision);
- allocation: the allocation task of its kind decided `pass` with a work
  row `equal`, from at least the task's own number of pairs
  (`allocation_matrix.task_named(task).pairs`, which its inventory must
  record, never a constant here);
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
- D4 (design decision 16): the 31 cells of `task37_cases.D4` (13 TASK29A
  control-limited, 5 TASK29A attributed, 13 TASK30 attributed) get a fresh
  decision. The only carry-over: a timing chain whose decisive stage (its
  final class, after stage 2 or the follow-up if one ran) is
  control-limited is not owed a second stage, and the cell is a pass with
  policy `D4` when its identity is identical or attributed and its exact
  allocation passes with its work rows `equal`. The policy is recorded on a
  cell that passes by it, and on no other. A pass or a fail of any stage
  decides as for any cell; any other control-limited cell is owed stage 2.
  The user extended D4 to `D4_TASK37` (design decision 46: `frag_named-10000`,
  control-limited after stage 2, identity attributed, exact allocation and
  work equal): D4 is `task37_cases.D4` and `D4_TASK37`.
- A fail of any stage of a cell's timing chain decides: a first stage, a
  second stage or an earlier grid that failed is not undone by a later stage
  or follow-up that passed (D4 cannot dispose it). The owed stage 2 of a cell
  is the engine's rule (`owes_stage2`: `Grid.extension_pairs`: protocol
  succeeded, no gated metric failed, a gated metric's B/B control is
  invalid); a protocol-failed cell owes a `redraw` and is not inspected for
  one. "Decisive stage" is the chain's final class.
- R-1: every attempt of a timing table in its ledger is judged or void
  (`void_attempts.attempts_of`, through the shard's engine), the
  follow-up's table (when one is declared) whether or not it is named, and
  the allocation tasks' (`--alloc-ledger`: see ALLOCATION LEDGER below).
  User amendment (design decision 45): a timing attempt whose cell archives
  show the pair runner's environment-integrity refusal after pairs were
  admitted (`void_attempts.ENVIRONMENT_REFUSALS`) selects nothing: it is
  void, and the settings are redrawn into a new output (the void output
  stays). Such an attempt needs `--environment-event FILE` (the system
  record of the change; sealed and recorded with the attempts it voids), and
  an event with no such attempt is refused.

Inconclusive never passes. A cell with no decision is `incomplete`, and
what is owed is listed explicitly on it and in the top-level `owed`:
`stage2`, `followup`, `attribution`, `redraw`, `identity-rerun`,
`allocation-rerun`, `retained-slope`. TASK33's `second` is `stage2` here. A
control-limited or inconclusive cell with no stage left is `blocked` (still
incomplete, owing an attribution).

Retained slope (design decision 44): a shard owes `retained-slope` only
where it samples it. A slope blocked for exactly the sizes of `storage_graph`
its part does not hold is `not-sampled` and takes the state of the TASK33 S1
records and the `storage_graph` allocation case that decide it exactly (any
failed: fail; any absent or not pass: incomplete; else pass); a blocked slope
missing a size of the part is a measurement gap and stays owed.

Lineage (design decision 17). Dispose runs in the checkout that holds this
code (`--repo` is that checkout or is refused). Every input records the
candidate it was measured at; each is accepted only when it is a commit of
that checkout, an ancestor of its HEAD, and has the tree outside the
performance area of `--candidate` (`task37_lineage.Lineage`). Every
checkout or harness an input records (identity and timing `checkout`,
allocation `harness`, the startup gate's) must be clean and have that tree
too, and an identity row's head is its own inventory's candidate. Every
accepted revision is recorded per input (`candidates`).

Timing inputs. The client sample (39 cells) runs as 2 shards and the matrix
sample (87 cells) as 4 (`task37_grid.SHARDS`; design decision 14), each with
its own ledger, in its own clone. Every shard is required, with the final
stage directory (`--timing SHARD=DIR`: an extension names its first stage by
`grid`, whose seals it carries and which is read too), its ledger
(`--ledger SHARD=FILE`) and its pilot (`--pilot SHARD=DIR`: a table with
fixed seconds is replayed with its pilot, the second stage too). The cells of
a shard's decisions are exactly its part of the sample
(`task37_grid.PARTS`), and the union of the shards' decisions is exactly the
sample. A declared follow-up of a shard (its declaration file
`task37_<kind>_<n>_followup_cells.json`, read by task37_followup.py; the
engines `followup_engines` names) is judged for R-1 whether or not it is
given; given
(`--followup SHARD=DIR --followup-pilot SHARD=DIR`) it must replace exactly
the shard's `--timing` output, and its cells replace the shard's. The further
rounds of a follow-up (task37_rounds.py, decision 47; `--followup
SHARD.R=DIR --followup-pilot SHARD.R=DIR`, R >= 2) are required where
declared and none is accepted undeclared: round R's cells are exactly the
cells the round before left inconclusive, its declaration precedes its
counts and follows every counts file of the round before, and its declared
pairs are the rule's from the replay of the round before's decisive stage
(checked with the replays); a cell is judged by its last round's chain. The
record cites each round's entry (`followup_rounds`: table, cells, pairs and
the recorded user decision its declaration names; a round declared without
one is out of protocol). A shard's ledger holds no attempt of a follow-up
table that is not round 1 or a declared round (a deleted declaration of a
measured round is refused). The counts
file an inventory names must be one the shard's table names (its counts
file or a revision of it, `Table.file_named`), and every
inventory, resumption and first stage carries the pins of the committed
`task37_attributed.json` for the shard's sources (the table's seal is
recorded). A stage whose `source_identity.differing` is not empty is
incomplete.

Replays (everything is replayed; a failed replay refuses). All reads, ties
and checks come first, the replays last. Identity tables:
`task37_identity.identity_replay`, with the opening in
`--identity-ledger KIND=FILE` (never a fixed path) and the attempts
recorded; timing shards and follow-ups: the engine's `replay` with its
pilot (a follow-up with its own and the shard's: `engine.replay`'s
provenance check refuses a fixed-seconds table without one); allocation:
`allocation_matrix.replay`. The statuses of TASK32, TASK33, the startup gate
and loading are those of their archives, whose replays recompute them
(`task37_gates.py` says what each re-derives and what it cannot):

    --task32 FILE --task32-replay ARGS   the disposition and the arguments of
        its `task32_downstream.py dispose` (without --out)
    --task33 FILE --task33-replay ARGS   the same for `task33_storage.py
        dispose` (under --declared task37_declared.json)
    --startup-gate DIR [--startup-null DIR] --startup-record FILE
    --startup-declared FILE --startup-ledger FILE
    --loading-simplib DIR --loading-conglib DIR
    --loading-ledger GATE=FILE (GATE simplib or conglib: one for each, no
        fallback: each shard runs in its own clone with its own ledger;
        run_loading.sh names its shard `SHARD=simplib|conglib` likewise)

The startup gate: `--startup-declared` is the sidecar `fill_record.py`
wrote with the record (the load totals Ds, Dc the record declares and the
archive they come from, bound to the record by its sha256). It is bound to
the record's content too (`gates.read_declared`): the archive must be the
one named (sha256 of its `decisions.json`), its R2 load totals must be the
sidecar's, and the record text must state the same Ds, Dc and archive sha256.
The gate's R2 load totals must equal them on every image or the gate FAILS
(design decision 21; nothing is transferred); the sidecar is sealed in the
record's inputs. `--startup-ledger` is the runner's attempts ledger: every
attempt is listed in the record (R-1). The judged gate (and its null
control) must be the last attempt; its `inputs.txt` is sealed in the
record. A COMPLETED last attempt (its `done` file is written, whatever its
close status: design decision 31) is judged by its gate and always has a
null control, so `--startup-null` is required; it must be exactly the
attempt's `gate-null`, as the null of every attempt. An
incomplete last attempt (a failing step, `die`, a signal before `done`, or
never closed: ledger status `open`) with no gate decision is void and
refuses (the lead redraws); one with a gate decision is judged by it
(design decision 26): a fail or blocked decision, on any grounds
(a failure on the declared deltas alone included: a `fail`, a redraw
allowed), is the gate's result (`judged-incomplete`), and only a pass
leaves the attempt incomplete owing a `redraw` (`owes-redraw`). Its
null control is neither read nor replayed (not applicable; the
`--startup-null` flag is refused there), except for an attempt owing a
redraw: its own `gate-null` is read and replayed when it holds a complete
archive that replays, and is otherwise recorded as absent (it cannot
change that verdict); an explicit `--startup-null` there must be that
archive and replay (refused otherwise). The null of a complete attempt must
replay (refused otherwise).
The judged gate is the `gate` of the last attempt and `--startup-declared`
its `declared-deltas.json`. A gate decision counts iff the sha256 rows of
its `gate/receipt.json` all match the files it lists AND the archive,
sealed to a record, replays with the attempt's own record (design decisions
28, 33; the runner's progress files never decide it, so a signal after a
decided, replayable gate does not undo the decision). The replay is made
with the attempt's own harness (design decisions 33, 36, 38): the whole
performance area as blobs at the commit in its `harness-head.txt`, in a
temporary tree (every other path being the checkout's), run by a child
process; it also checks the header (`SCHEMA`, `PAIRS`) and replays the
null and the late replays, so a later fix to any harness file never locks
a disposition out. The checkout's interpreter never imports harness code;
the trees are removed when dispose ends. A harness that cannot be built or
run is refused, naming the attempt, the commit and the child's stderr
tail. An archive that
gives no decision makes the attempt void (a redraw is allowed; the reason
is in the attempt row) unless the attempt shows progress past
`replay-gate` (`done`, `replay-gate.exit` reading `exit=0`, a later step
file): it is then damaged and refused, as is an attempt that closed with
exit 0 and no `done`, or with exit 2 and no `done` although no hard step
failed with 2.
Each
earlier attempt is judged by its gate decision when it has one, complete
or not: it is recorded
with its gate decision, reasons and declared-delta problems (the sidecar
bound to the attempt's record and sealed `inputs.txt`). A redraw is
accepted after an attempt with no gate decision (void), a gate that
failed on the declared deltas alone, or an incomplete attempt with a
passing gate (`gates.earlier_attempt`); it is refused after a complete
attempt that passed and after any attempt that decided fail or blocked on
other grounds. The api-audit receipt must be present and
passing.
The record holds D's HEAD (`head`), which must have no uncommitted change
to a tracked file outside .agent-files, and `--candidate` must be
equivalent to `task37_cases.COMPILED_REF` (same tree outside the
performance area). A later `--check` accepts the recorded `head` when it is
an ancestor of the HEAD then with the same tree outside the performance
area (`Lineage.recorded_head`: a later performance-only commit leaves the
record checkable; a later commit outside it refuses), and substitutes it as
it substitutes the recorded code seals.

Allocation grid. For each task: the grid's `status`, `nondeterminism` and
`unresolved` are recorded, and one record per (task, case) decides the
slopes and the size-zero constants from `decisions["cases"][CASE]["slopes"]`
and `["constants"]` (each: {phase: {metric: [row] / row}} with a `decision`;
`constants` is None for a case with no size-0 cell, which is `n/a`: not a
gate, never a failure, and the slopes are still gated; the slopes of a case
of one size, with no adjacent pair, are `n/a` likewise);
a grid that is not `pass` with nothing that explains it (no row that is not
pass/equal, no case record, no nondeterminism, no unresolved cell) is
refused. The 3-pair TASK37 tasks keep these keys (part C).

ALLOCATION LEDGER. `--alloc-ledger TASK=FILE` (one for each task) is judged
by `allocation_attempts.attempts_of(task, ledger, judged)` with the output
named by `--alloc-<task>` as the judged attempt ({attempt, status, output,
judged, void}, as `void_attempts.attempts_of` returns, and for a void
attempt its `rejections`, [{archive, reason}], listed in the record's lines);
an attempt is void only if every cell archive it holds is rejected on replay
(design decision 30: replay decides, never the inventory alone). Its refusal
(`InvalidAllocation`) refuses the disposition. The pairs a passing row needs
are `allocation_matrix.task_named(task).pairs`.

Host load. `--load STREAM=FILE` (repeatable, optional) names a recording of
`task37_load.py record`; its summary (`task37_load.summarize`) is copied into
the record under `host_load` and printed, reported only and never a gate. The
D7 build timing receipt (`receipt`, with at least one sealed report) is
reported only.

Commands

    task37_dispose.py --candidate REV [--repo CHECKOUT]
        --identity-{client,matrix,downstream} DIR
        --identity-ledger KIND=FILE (three)
        --alloc-{matrix,client,downstream} DIR
        --alloc-ledger TASK=FILE (three)
        --timing SHARD=DIR --ledger SHARD=FILE --pilot SHARD=DIR (6 each)
        [--followup SHARD[.R]=DIR --followup-pilot SHARD[.R]=DIR]
        [--load STREAM=FILE ...] [--environment-event FILE ...]
        --task32 FILE --task32-replay ARGS --task33 FILE
        --task33-replay ARGS --startup-gate DIR --startup-null DIR
        --startup-record FILE --startup-declared FILE --startup-ledger FILE
        --loading-simplib DIR --loading-conglib DIR
        --loading-ledger GATE=FILE (simplib, conglib; both) [--d7-build FILE]
        (--record OUTDIR | --check OUTDIR)
    task37_dispose.py receipt --gate d7-build --candidate REV --status S
        --exit N --out FILE --report FILE [--report FILE ...]

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
import re
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task31_dispose as d31
import task31_pins as reviewed
import task37_cases as cases
import task37_gates as gates
import task37_followup as followup
import task37_rounds as rounds
import task37_grid as grid
import task37_lineage as lineage_of
import task37_load as load
import timing_grid as tg
from void_attempts import ENVIRONMENT_REFUSALS, attempts_of

SCHEMA = "task37-disposition-v1"
SCOPE = ("aarch64 Linux only; Poly/ML 5.9.2; allocation only with the "
         "private counter; RSS reported only")
GATES = gates.GATES
D7 = gates.D7
# Where the committed counts files are (tests point this elsewhere).
COUNTS_DIR = a.HERE
KINDS = ("client", "matrix", "downstream")
TASKS = dict(client="task37-client", matrix="task37-matrix",
             downstream="task37-downstream")
# Every module whose decision or seal the record depends on: the modules
# this one, the gates, the lineage, the cell sets and the tables import (a
# test pins it, function-local imports included).
CODE = ("task37_dispose.py", "task37_gates.py", "task37_lineage.py",
        "task37_cases.py", "task37_identity.py", "task37_grid.py",
        "task37_followup.py", "task37_rounds.py", "task37_sources.py",
        "task37_load.py", "task31_dispose.py", "task31_identity_grid.py",
        "task31_identity.py", "task31_attribution.py", "task31_cases.py",
        "task31_followup.py", "task31_grid.py", "task31_pins.py",
        "task30_cases.py", "task30_grid.py", "task29_gate.py",
        "task29a_grid.py", "task32_downstream.py", "task32_cases.py",
        "task33_dispose.py", "task33_rules.py", "task33_storage.py",
        "startup_gate.py", "loading.py", "timing_grid.py", "acceptance.py",
        "void_attempts.py", "allocation_matrix.py", "allocation_schema.py",
        "allocation_analysis.py", "allocation_attempts.py",
        "client_dependencies.py", "matrix_schema.py", "evidence_bundle.py",
        "allocation_boundary.py", "audit_evidence.py", "path_schema.py",
        "performance_schema.py", "runtime_metrics.py", "summarize.py",
        "task30_pins.py", "task31_snapshot.py", "task32_dat.py",
        "task32_snapshots.py", "task33_cases.py", "task33_offline.py",
        "task33_records.py")
HISTORY = {}
# Cells the user added to `task37_cases.D4` for this disposition (2026-11-14,
# design decision 46): `frag_named-10000` (matrix-3) is control-limited after
# stage 2 with identity attributed and exact allocation and work equal.
# task37_cases.py is sealed by every TASK37 measurement and is not edited.
D4_TASK37 = ("frag_named-10000",)

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


def read(path, label):
    a.require(path is not None, "no %s given" % label)
    path = Path(path)
    a.require(path.is_file(), "%s is missing: %s" % (label, path))
    return a.load(path)


def tie(label, document, lineage, baseline=True):
    """The document is of an equivalent candidate (and of the pinned
    baseline); returns the candidate it records."""
    found = document.get("candidate") if isinstance(document, dict) else None
    a.require(found is not None, "%s records no candidate" % label)
    full = lineage.candidate_of(label, found)
    if baseline and "baseline" in document:
        a.require(document["baseline"] == a.BASE,
                  "%s is against another baseline (%s)" % (
                      label, document["baseline"]))
    return found


# ------------------------------------------------------- command inputs

def keyed(values, label, allowed=None):
    """{key: Path} of repeated `KEY=PATH` options; `allowed` limits the keys
    (and the message names them)."""
    found = {}
    for value in values or []:
        key, sep, path = str(value).partition("=")
        a.require(sep and key and path and (allowed is None or
                                            key in allowed),
                  "--%s needs KEY=PATH%s, not %r" % (
                      label, "" if allowed is None else " with KEY one of "
                      + ", ".join(allowed), value))
        a.require(key not in found, "--%s names %s twice" % (label, key))
        found[key] = Path(path)
    return found


def keyed_rounds(values, label, shards):
    """`keyed` for the follow-up options, whose key is a shard (round 1) or
    `SHARD.R` (round R >= 2, task37_rounds.parse_key)."""
    for value in values or []:
        key = str(value).partition("=")[0]
        try:
            shard, _ = rounds.parse_key(key)
        except ValueError:
            shard = None
        a.require(shard in shards, "--%s needs KEY=PATH with KEY a shard "
                  "(%s) or SHARD.R for a round R >= 2, not %r" % (
                      label, ", ".join(shards), value))
    return keyed(values, label)


def replayed(code, label):
    """A replay ended in a decision (any status), not by a refusal."""
    a.require(code in (0, 1, 2), "%s did not replay (exit %r)" % (
        label, code))


# ------------------------------------------------------------- identity

IDENTITY_OK = ("identical", "attributed")


def replay_identity(kind, root, repo, ledger):
    """Replay the identity grid of table `kind` in `root` offline
    (task37_identity.identity_replay: the archives, the decisions, the code
    seals, the reviewed table and the opening in `ledger`); a refusal
    refuses the disposition."""
    import task37_identity
    code = gates.quiet(task37_identity.identity_replay, argparse.Namespace(
        table=kind, output=Path(root).resolve(), repo=repo,
        attributed=None, ledger=ledger))
    replayed(code, "the %s identity grid" % kind)


def identity_attempts(kind, ledger, candidate):
    """(attempts of the identity table in the ledger, those of the
    candidate)."""
    import task37_identity
    return list(task37_identity.attempt_counts(
        task37_identity.tables()[kind], ledger, candidate))


def identity_binding(held, label):
    """The reviewed table the identity grid was judged by is the committed
    task37_attributed.json (by sha256), as every gate's."""
    now = reviewed.load(cases.REVIEWED_FILE)["seal"]
    a.require(isinstance(held, dict) and held.get("sha256"),
              "%s records no reviewed table" % label)
    a.require(held["sha256"] == now["sha256"],
              "%s was judged by the reviewed table %s, not the committed "
              "%s: run it again" % (label, held["sha256"], now["sha256"]))


def read_identity(root, label, names, lineage, kind, ledger, repo, late):
    """The identity table of `names` in directory `root` (inventory.json and
    decisions.json of task31_identity_grid.identity, through
    task37_identity.py): {cells, status, unaccounted, attributed, seals,
    attempts}. Its replay is added to `late`."""
    root = Path(root)
    inventory = read(root / "inventory.json", label + " inventory")
    decisions = read(root / "decisions.json", label + " decisions")
    found = tie(label + " inventory", inventory, lineage)
    a.require(tie(label + " decisions", decisions, lineage) == found,
              "%s: the inventory and the decisions are of different "
              "candidates" % label)
    a.require(not decisions.get("diagnostic") and
              not inventory.get("diagnostic"),
              "%s is a diagnostic, not the whole table" % label)
    lineage.harness(label + " checkout", inventory.get("checkout"))
    identity_binding((inventory.get("attributed") or {}).get("file"), label)
    for run in inventory.get("runs", []):
        row = run.get("row") or {}
        a.require(row.get("head") == found and not row.get("dirty"),
                  "%s: the cell %s-%s ran in another checkout than the "
                  "candidate's, or a dirty one" % (
                      label, run.get("case"), run.get("size")))
    cells = decisions.get("cells")
    a.require(isinstance(cells, dict) and set(cells) == set(names),
              "%s has not exactly the cells of its kind (%d expected)" % (
                  label, len(names)))
    for name, row in cells.items():
        a.require(isinstance(row, dict) and isinstance(
            row.get("status"), str), "malformed %s row: %s" % (label, name))
    a.require(ledger is not None and Path(ledger).is_file(),
              "no attempts ledger for %s: %s" % (label, ledger))
    held = dict(cells=cells, status=decisions.get("status"),
                unaccounted=decisions.get("unaccounted", []),
                attributed=decisions.get("attributed", []),
                candidate=found, attempts=None,
                seals={"inventory": a.seal(root / "inventory.json"),
                       "decisions": a.seal(root / "decisions.json"),
                       "ledger": a.seal(Path(ledger))})

    def replay():
        replay_identity(kind, root, repo, ledger)
        held["attempts"] = identity_attempts(kind, ledger, found)
    late.append((label, replay))
    return held


# ----------------------------------------------------------- allocation

WORK = ("equal", "differs", "inconclusive", None)
DECISIONS = ("pass", "fail", "inconclusive")


def required_pairs(task):
    """The pairs a passing row of allocation task `task` needs: the task's
    own (`allocation_matrix.Task.pairs`), never the legacy constant."""
    import allocation_matrix as am
    return am.task_named(task).pairs


def replay_allocation(root):
    """Replay the allocation grid in `root` (allocation_matrix.replay: the
    archives, the decisions and the results table, from the inventory's own
    task)."""
    import allocation_matrix as am
    code = gates.quiet(am.replay, argparse.Namespace(
        output=Path(root).resolve()))
    replayed(code, "the allocation grid in %s" % root)


def allocation_attempts(task, ledger, root):
    """The attempts of an allocation task in its ledger, each judged or
    void (R-1), in the shape of `void_attempts.attempts_of` ({attempt,
    status, output, judged, void}): `allocation_attempts.attempts_of`,
    with the output `root` named by `--alloc-<task>` as the judged
    attempt. Its refusal is a refusal of the disposition."""
    import allocation_attempts as aa
    import allocation_schema as sc
    try:
        return aa.attempts_of(
            task, ledger, judged={aa.attempt_id(root): root})
    except sc.InvalidAllocation as error:
        raise ValueError("the attempts ledger of %s is refused: %s" % (
            task, error)) from None


def words(found):
    """fail over pass over inconclusive of the decisions of a list."""
    return ("fail" if "fail" in found else
            "pass" if found and set(found) == {"pass"} else
            "inconclusive")


def slope_word(record):
    """The word of the adjacent-size slopes of a case: `n/a` when the case
    has one size, so no adjacent pair (every row list is empty), `missing`
    when the grid computed no slopes."""
    slopes = record.get("slopes")
    if slopes is None:
        return "missing"
    found = [r["decision"] for phase in slopes.values()
             for rows in phase.values() for r in rows]
    return words(found) if found else "n/a"


def constant_word(record):
    """The word of the size-zero constants of a case: `n/a` when the grid
    has no size-0 cell (`constants` is None), `missing` when the record has
    no such key."""
    if "constants" not in record:
        return "missing"
    constants = record["constants"]
    if constants is None:
        return "n/a"
    return words([m["decision"] for phase in constants.values()
                  for m in phase.values()])


def case_decisions(record):
    """{slope, constant}: the words of the slope and the size-zero constant
    decisions of one case of an allocation grid
    (`decisions["cases"][CASE]`), `missing` where the grid computed none."""
    return dict(
        slope=slope_word(record),
        constant=constant_word(record))


def case_records(task, decisions):
    """One record per case of the grid for its slope and constant
    decisions."""
    found = {}
    for case, record in sorted(decisions["cases"].items()):
        words_ = case_decisions(record)
        failed = ["allocation %s: fail" % k for k, v in words_.items()
                  if v == "fail"]
        missing = ["allocation %s: %s" % (k, v) for k, v in words_.items()
                   if v not in ("pass", "fail", "n/a")]
        found["%s:%s" % (task, case)] = dict(
            words_, failed=failed, missing=missing,
            owed=["allocation-rerun"] if missing else [])
    return found


def read_allocation(root, task, names, infeasible, lineage, ledger, late):
    """{rows: {name: {decision, work, pairs}}, pairs, cases, state, seals,
    attempts} of an allocation task (inventory.json and decisions.json of
    allocation_matrix, `rows` of `cell_rows`); the pairs a passing row needs
    are the task's own, which the inventory must record. Its replay and
    ledger judgement are added to `late`."""
    root = Path(root)
    inventory = read(root / "inventory.json", task + " inventory")
    a.require(root.joinpath("decisions.json").is_file(),
              "the %s allocation is partial: it has no decisions" % task)
    decisions = read(root / "decisions.json", task + " decisions")
    a.require(inventory.get("task") == task,
              "the allocation grid is not a %s grid (%s)" % (
                  task, inventory.get("task")))
    found = tie(task + " inventory", inventory, lineage)
    a.require(tie(task + " decisions", decisions, lineage) == found,
              "the %s inventory and decisions are of different "
              "candidates" % task)
    lineage.harness(task + " harness", inventory.get("harness"),
                    clean=True)
    pairs = inventory.get("pairs")
    a.require(isinstance(pairs, int) and not isinstance(pairs, bool) and
              pairs >= 1, "the %s inventory has no pair count" % task)
    a.require(pairs == required_pairs(task),
              "the %s allocation was run with %s pairs, not the task's %s"
              % (task, pairs, required_pairs(task)))
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
        name = cases.name(row["case"], row["size"])
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
    a.require(isinstance(decisions.get("cases"), dict),
              "the %s allocation decisions have no cases" % task)
    records = case_records(task, decisions)
    state = dict(status=decisions.get("status"),
                 nondeterminism=len(decisions.get("nondeterminism", [])),
                 unresolved=list(decisions.get("unresolved", [])),
                 work_status=decisions.get("work_status"))
    explained = (any(r["decision"] != "pass" or r["work"] != "equal"
                     for r in rows.values()) or
                 any(r["failed"] or r["missing"] for r in records.values())
                 or state["nondeterminism"] or state["unresolved"])
    a.require(state["status"] == "pass" or explained,
              "the %s allocation grid is %s, but no row, case or list "
              "explains it" % (task, state["status"]))
    a.require(ledger is not None and Path(ledger).is_file(),
              "no allocation attempts ledger for %s: %s" % (task, ledger))
    held = dict(rows=rows, pairs=pairs, cases=records, state=state,
                attempts=None,
                seals={"inventory": a.seal(root / "inventory.json"),
                       "decisions": a.seal(root / "decisions.json"),
                       "ledger": a.seal(Path(ledger))})

    def replay():
        replay_allocation(root)
        held["attempts"] = allocation_attempts(task, ledger, root)
    late.append((task, replay))
    return held


# --------------------------------------------------------------- timing

def class_map(decisions):
    """({cell: class}, retained-slope class or None) of a grid decision
    (`decisions.json` of timing_grid, classified by timing_grid.classify)."""
    found, scaling = {}, None
    for kind, names in tg.classify(decisions).items():
        for name in names:
            if name == "retained_scaling":
                scaling = kind
            else:
                found[name] = kind
    return found, scaling


def raw_scaling(decisions):
    """The status and missing sizes of a grid decision's retained slope
    where it is not measured (None where it is, or where there is none):
    what `dispose` needs to tell a slope the shard does not sample from a
    measurement gap."""
    found = decisions.get("retained_scaling")
    if not isinstance(found, dict) or found.get("status") == "measured":
        return None
    return dict(status=found.get("status"),
                missing_sizes=list(found.get("missing_sizes", [])))


def differing_of(decisions, label):
    found = decisions.get("source_identity")
    a.require(isinstance(found, dict) and isinstance(
        found.get("differing"), list),
        "%s records no source identity" % label)
    return list(found["differing"])


def owes_stage2(row):
    """The cell of a decisions row is one the engine plans a second stage
    for if it has not had one: `Grid.extension_pairs`' rule, read from the
    row. Its protocol succeeded (a row of a failed protocol has no metrics:
    it owes a `redraw`, not a stage), no gated metric failed (a first-stage
    fail stays final) and a gated metric's B/B control is invalid; the row
    shows an invalid control as the metric's reason `tg.CONTROL`
    (`acceptance.apply_control` sets it, with `control_valid` false, unless
    the metric failed). The gated metrics are the policy's own. A test
    checks the rule against `Grid.extension_pairs`."""
    if not row.get("protocol"):
        return False
    gated = a.EQUIVALENCE_POLICY["gated_timing"]
    metrics = row["metrics"]
    if any(metrics[m]["decision"] == "fail" for m in gated):
        return False
    return any(metrics[m]["reason"] == tg.CONTROL and
               metrics[m]["decision"] not in ("pass", "reported")
               for m in gated)


def read_stage(root, label, lineage):
    """One timing output: its inventory (`inventory.json` of timing_grid),
    its cell classes, its retained slope (`scaling`, and `scaling_raw`: the
    status and missing sizes where it is not measured), its first stage's
    classes (read and sealed through
    the engine's schema for an extension) and the cells its second stage
    remeasured, with the sources that differ in any stage."""
    root = Path(root).resolve()
    inventory = read(root / "inventory.json", label + " inventory")
    decisions = read(root / "decisions.json", label + " decisions")
    tie(label + " inventory", inventory, lineage)
    lineage.harness(label + " checkout", inventory.get("checkout"))
    final, scaling = class_map(decisions)
    differing = differing_of(decisions, label)
    control_open = sorted(
        "%s-%d" % (w["case"], w["size"]) for w in decisions["workloads"]
        if owes_stage2(w))
    first, plan, first_root = final, {}, root
    if str(inventory.get("schema", "")).endswith("-extension-v1"):
        first_root = (root / inventory["grid"]).resolve()
        a.require(first_root.joinpath("decisions.json").is_file() and
                  a.seal(first_root / "inventory.json") ==
                  inventory.get("grid_inventory") and
                  a.seal(first_root / "decisions.json") ==
                  inventory.get("grid_decisions"),
                  "%s: the first stage is not the one sealed" % label)
        first_decisions = a.load(first_root / "decisions.json")
        first, _ = class_map(first_decisions)
        differing += differing_of(first_decisions, label + " first stage")
        plan = {cases.name(c, s): p for c, s, p in
                decisions["remeasured"]["plan"]}
    first_inventory = a.load(first_root / "inventory.json")
    tie(label + " first stage inventory", first_inventory, lineage)
    lineage.harness(label + " first stage checkout",
                    first_inventory.get("checkout"))
    seal_files = [root / "inventory.json", root / "decisions.json"]
    if first_root != root:
        seal_files += [first_root / "inventory.json",
                       first_root / "decisions.json"]
    return dict(root=root, first_root=first_root, inventory=inventory,
                first_inventory=first_inventory, final=final,
                scaling=scaling, scaling_raw=raw_scaling(decisions),
                first=first, plan=plan,
                control_open=control_open,
                differing=sorted(set(differing)),
                seals={str(p): a.seal(p) for p in seal_files})


def check_counts(stage, label, table):
    """The counts file the stage names is one of the table's own committed
    files (`Table.file_named`: its counts file or a revision of it, made by
    `predeclare --revises`), unchanged."""
    for inventory in (stage["inventory"], stage["first_inventory"]):
        name = inventory.get("counts_file")
        a.require(isinstance(name, str) and name and any(
            name == p.name for p in table.files()),
            "%s names the counts file %r, not one of %s" % (
                label, name, ", ".join(p.name for p in table.files())))
        path = COUNTS_DIR / name
        a.require(path.is_file(), "%s: the counts file %s is missing"
                  % (label, path))
        a.require(a.seal(path) == inventory.get("iterations_seal"),
                  "%s: the counts file %s is not the one the grid used "
                  "(stale counts file)" % (label, name))
    return a.seal(COUNTS_DIR / stage["inventory"]["counts_file"])


def check_declaration(key, stage, repo):
    """The follow-up's declaration file precedes each counts file of the
    follow-up the stage used (`task37_followup.check_declaration_order`,
    which the follow-up's engine checks too)."""
    for inventory in (stage["inventory"], stage["first_inventory"]):
        a.require(isinstance(inventory.get("counts_commit"), str),
                  "the follow-up of %s records no counts commit" % key)
        followup.check_declaration_order(
            repo, inventory["candidate"], key, inventory["counts_commit"])


def pins_binding(engine, label, root, document):
    """The pins a timing output (and each resumption and first stage of it)
    was judged by must be the committed table's projection onto the sources
    the table measures (`task31_pins.pins`, the function the table uses).
    The seal of the file may be an earlier one, if its history keeps it:
    adding an entry that is no source of the table changes no pin, while any
    change to the entry of a measured source does. Returns the pins."""
    expected = reviewed.pins(document["entries"], engine.t.sources)
    for code in d31.pin_codes(engine, root):
        found = engine.h.pins_for(code)
        a.require(found == expected,
                  "the %s was judged by pins that are not the committed "
                  "table's for the sources it measures (%s against %s): "
                  "a measured source's reviewed entry changed, so the "
                  "grid is void" % (label, json.dumps(found, sort_keys=True),
                                    json.dumps(expected, sort_keys=True)))
    return expected


def ledger_attempts(engine, judged, repo, ledger):
    """Every attempt of `engine`'s table in `ledger`: those of `judged`
    ({attempt: output}) and the others, which must be void (R-1), an
    environment-integrity refusal included (decision 45)."""
    return attempts_of(argparse.Namespace(repo=repo, ledger=ledger),
                       engine, judged, ENVIRONMENT_REFUSALS)


def replay_timing(engine, root, repo, ledger, pilot=None,
                  replaces_pilot=None):
    """Replay a timing output with its engine (`timing_grid.Grid.replay`:
    every archive, the decisions, the code, the counts, the ledger, and the
    counts derived again from the pilot, which a table with fixed seconds
    needs: its second stage too); a follow-up names its own pilot and the
    replaced grid's."""
    a.require(pilot is not None or not engine.t.fixed_seconds,
              "%s needs its pilot to replay" % engine.t.name)
    code = gates.quiet(engine.replay, argparse.Namespace(
        output=Path(root).resolve(), partial=False, repo=repo,
        ledger=ledger, pilot=pilot, replaces_pilot=replaces_pilot))
    replayed(code, "the timing output %s" % root)


def timing_engine(key):
    """The engine of a shard's table."""
    return grid.GRIDS[grid.name_of(key)]


def followup_engines():
    """{follow-up table name: engine} of the declared follow-ups: the one
    place that knows where they are declared (`task37_followup.GRIDS`)."""
    return dict(followup.GRIDS)


def followup_of(key):
    """The engine of the declared follow-up of a shard, or None."""
    return followup_engines().get(followup.name_of(key))


def round_engines():
    """{table name: engine} of the declared follow-up rounds 2.. (decision
    47; `task37_rounds.GRIDS`)."""
    return dict(rounds.GRIDS)


def declared_rounds(key):
    """The rounds >= 2 declared for a shard, in order."""
    engines = round_engines()
    return [n for n in range(2, rounds.MAX_ROUND + 1)
            if rounds.name_of(key, n) in engines]


def round_declaration(key, number):
    """The declaration of round `number` >= 2 of a shard (`task37_rounds.
    DECLARED`): {cells, pairs, decision}."""
    return rounds.DECLARED[key][number]


def check_ledger_tables(key, state, allowed):
    """The ledger of a shard holds no attempt of a follow-up table this
    disposition did not judge: a table `task37-<shard>-followup<digits>`
    other than `allowed` (round 1 and the declared rounds) is a measured
    round whose declaration was deleted, or one not given."""
    pattern = re.compile(r"%s-followup[0-9]*" % re.escape(
        grid.name_of(key)))
    found = sorted({r["table"] for r in state.records
                    if isinstance(r.get("table"), str) and
                    pattern.fullmatch(r["table"]) and
                    r["table"] not in allowed})
    a.require(not found, "the attempts ledger of %s holds attempts of "
              "follow-up tables this disposition does not judge: %s (a "
              "round that was measured is judged, so its declaration "
              "stays)" % (key, ", ".join(found)))


def check_round_declaration(key, number, stage, repo):
    """The declaration of round `number` precedes each counts file of the
    round the stage used (`task37_rounds.check_declaration_order`, which
    the round's engine checks too)."""
    for inventory in (stage["inventory"], stage["first_inventory"]):
        a.require(isinstance(inventory.get("counts_commit"), str),
                  "round %d of the follow-up of %s records no counts "
                  "commit" % (number, key))
        rounds.check_declaration_order(
            repo, inventory["candidate"], key, number,
            inventory["counts_commit"])


def read_shard(key, options, lineage, repo, document, late):
    """One timing shard: {cells: {name: row}, scaling, scaling_raw (status and
    missing sizes of an unmeasured retained slope, else None), differing,
    attempts,
    seals, pins}. A cell's row: class, first (its decisive chain's first
    stage), stage2 and followup (whether they ran), earlier (the classes the
    follow-up replaced). The replays and the ledger judgement are added to
    `late`."""
    table = grid.name_of(key)
    root, ledger = options["timing"].get(key), options["ledger"].get(key)
    a.require(root is not None, "no timing output for the shard %s" % key)
    a.require(ledger is not None and Path(ledger).is_file(),
              "no attempts ledger for %s: %s" % (table, ledger))
    pilot = options["pilot"].get(key)
    a.require(pilot is not None, "no --pilot for the shard %s (a table with "
              "fixed seconds is replayed with its pilot)" % key)
    engine, expected = timing_engine(key), grid.PARTS[key]
    main = read_stage(root, table, lineage)
    check_counts(main, table, engine.t)
    a.require(set(main["final"]) == set(expected),
              "the %s table is not its part of the sample (%d cells)" % (
                  table, len(expected)))
    pins = pins_binding(engine, table, main["root"], document)
    rows = {n: dict(cls=c, first=main["first"][n], stage2=n in main["plan"],
                    followup=False, earlier=[],
                    control_open=n in main.get("control_open", ()))
            for n, c in main["final"].items()}
    seals = dict(main["seals"])
    differing = list(main["differing"])
    entries = []
    pending = [(engine, main["root"], pilot, None)]
    judged = [(engine, d31.judged_attempts(engine, main["root"]))]
    follow = followup_of(key)
    given = options["followup"].get(key)
    after = []
    chain = [n for n in range(2, rounds.MAX_ROUND + 1)
             if rounds.key_text(key, n) in options["followup"]]
    for n in declared_rounds(key):
        a.require(rounds.key_text(key, n) in options["followup"],
                  "round %d of the follow-up of %s is declared and has no "
                  "--followup %s=DIR" % (n, key, rounds.key_text(key, n)))
    for n in chain:
        a.require(n in declared_rounds(key), "round %d of the follow-up of "
                  "%s is not declared (see task37_rounds)" % (n, key))
        a.require(given is not None and (n == 2 or n - 1 in chain),
                  "--followup %s needs the rounds before it (--followup "
                  "%s ...)" % (rounds.key_text(key, n), rounds.key_text(
                      key, n - 1)))
    if given is not None:
        name = followup.name_of(key)
        a.require(follow is not None, "no follow-up is declared for %s "
                  "(see followup_engines)" % table)
        followup_pilot = options["followup-pilot"].get(key)
        a.require(followup_pilot is not None, "a follow-up of %s needs "
                  "--followup-pilot" % key)
        stage = read_stage(given, "%s follow-up" % table, lineage)
        check_counts(stage, name, follow.t)
        check_declaration(key, stage, repo)
        a.require(set(stage["final"]) == set(follow.t.names()),
                  "the %s cells are not the declared follow-up's" % name)
        a.require(stage["scaling"] is None,
                  "a %s follow-up has a retained slope" % table)
        pins_binding(follow, name, stage["root"], document)
        # each inventory's `replaces.grid` is relative to its own root
        # (the extension's to the extension, the first stage's to the
        # first stage), which need not be siblings
        replaced = [(inv["replaces"], root) for inv, root in (
            (stage["inventory"], stage["root"]),
            (stage["first_inventory"], stage["first_root"]))
            if inv.get("replaces")]
        a.require(replaced and all(
            isinstance(r.get("grid"), str) and
            (Path(root) / r["grid"]).resolve() == main["root"]
            for r, root in replaced),
            "the %s follow-up does not replace the shard's --timing "
            "output %s" % (table, main["root"]))
        pending.append((follow, stage["root"], Path(followup_pilot
                                                    ).resolve(),
                        Path(pilot).resolve()))
        judged.append((follow, d31.judged_attempts(follow, stage["root"])))
        differing += stage["differing"]
        for n, c in stage["final"].items():
            rows[n] = dict(cls=c, first=stage["first"][n],
                           stage2=n in stage["plan"], followup=True,
                           control_open=n in stage.get("control_open", ()),
                           earlier=rows[n]["earlier"] + [rows[n]["cls"]])
        seals.update(stage["seals"])
        previous = follow
        for n in chain:
            previous = read_round(
                key, n, previous, options, lineage, repo, document, rows,
                seals, differing, pending, judged, after, entries)
    else:
        a.require(key not in options["followup-pilot"],
                  "--followup-pilot names a shard with no --followup: %s"
                  % key)
        if follow is not None:
            judged.append((follow, {}))
    seals["ledger"] = a.seal(Path(ledger))
    held = dict(cells=rows, scaling=main["scaling"],
                scaling_raw=main["scaling_raw"],
                differing=sorted(set(differing)), attempts=[], seals=seals,
                pins=pins, counts=None, rounds=entries)
    allowed = {followup.name_of(key)} | {
        rounds.name_of(key, n) for n in declared_rounds(key)}

    def replay():
        for each, where, pilot_, replaced_ in pending:
            replay_timing(each, where, repo, ledger, pilot=pilot_,
                          replaces_pilot=replaced_)
        for check in after:
            check()
        state = tg.Ledger(ledger)
        check_ledger_tables(key, state, allowed)
        for each, found in judged:
            held["attempts"] += ledger_attempts(each, found, repo, ledger)
        held["counts"] = list(engine.h.attempt_counts(
            state, main["inventory"]["candidate"]))
    late.append((table, replay))
    return held


def read_round(key, number, previous, options, lineage, repo, document,
               rows, seals, differing, pending, judged, after, entries):
    """Round `number` >= 2 of the follow-up of shard `key` (decision 47),
    chained to the engine `previous` of the round before: its cells are the
    declared ones and exactly the cells the round before left inconclusive
    (`rows` holds that round's classes and takes this one's), the
    declaration precedes its counts and follows every counts file of the
    round before, and its pairs are the rule's from the sealed decisive
    stage of the round before (checked after the replays, from the replay of
    that stage). Its entry (round, table, cells, pairs and the recorded user
    decision of the declaration) is added to `entries`. Returns the
    engine."""
    option = rounds.key_text(key, number)
    name = rounds.name_of(key, number)
    engine = round_engines()[name]
    fpilot = options["followup-pilot"].get(option)
    a.require(fpilot is not None, "round %d of the follow-up of %s needs "
              "--followup-pilot %s=DIR" % (number, key, option))
    stage = read_stage(options["followup"][option], name, lineage)
    check_counts(stage, name, engine.t)
    check_round_declaration(key, number, stage, repo)
    a.require(set(stage["final"]) == set(engine.t.names()),
              "the %s cells are not the declared round's" % name)
    a.require(all(rows[n]["cls"] == "inconclusive" for n in stage["final"]),
              "the cells of round %d of %s are not all inconclusive in the "
              "round before: %s" % (number, key, ", ".join(sorted(
                  n for n in stage["final"]
                  if rows[n]["cls"] != "inconclusive"))))
    opened = sorted(n for n in previous.t.names()
                    if rows[n]["cls"] == "inconclusive")
    a.require(sorted(engine.t.names()) == opened,
              "the cells of round %d of %s (%s) are not exactly the cells "
              "round %d left inconclusive (%s)" % (
                  number, key, ", ".join(sorted(engine.t.names())),
                  number - 1, ", ".join(opened) or "none"))
    a.require(stage["scaling"] is None,
              "a %s follow-up has a retained slope" % name)
    pins_binding(engine, name, stage["root"], document)
    entries.append(dict(
        round=number, table=name, cells=sorted(engine.t.names()),
        pairs=engine.t.pairs,
        decision=round_declaration(key, number)["decision"]))
    pending.append((engine, stage["root"], Path(fpilot).resolve(), None))
    judged.append((engine, d31.judged_attempts(engine, stage["root"])))
    differing += stage["differing"]
    for n, c in stage["final"].items():
        rows[n] = dict(cls=c, first=stage["first"][n],
                       stage2=n in stage["plan"], followup=True,
                       control_open=n in stage.get("control_open", ()),
                       earlier=rows[n]["earlier"] + [rows[n]["cls"]])
    seals.update(stage["seals"])
    after.append(lambda: rounds.check_pairs(
        previous, previous.replayed, engine.t.names(), engine.t.pairs))
    return engine


def read_timing(kind, sample, options, lineage, repo, document, late):
    """The shards of a sample, each required, joined: {table name: shard}.
    The union of the shards' final decisions is exactly `sample`."""
    found, union = {}, set()
    for key in grid.shards(kind):
        a.require(key in options["timing"], "no timing output for the "
                  "shard %s (every shard is required)" % key)
        shard = read_shard(key, options, lineage, repo, document, late)
        a.require(not union & set(shard["cells"]),
                  "the %s shards overlap" % kind)
        union |= set(shard["cells"])
        found[grid.name_of(key)] = shard
    a.require(union == set(sample), "the %s shards do not join to the "
              "sample (%d cells)" % (kind, len(sample)))
    return found


def load_loads(paths):
    """{stream: summary} of the host-load recordings (task37_load.py), and
    their seals; reported only, never a gate."""
    found, seals = {}, {}
    for stream, path in paths.items():
        a.require(path.is_file(), "the load recording of %s is missing: %s"
                  % (stream, path))
        try:
            found[stream] = load.summarize(path)
        except (KeyError, TypeError, IndexError) as error:
            raise ValueError("malformed load recording %s: %r" % (
                path, error))
        seals["load-" + stream] = a.seal(path)
    return found, seals


# ------------------------------------------------------------- the rule

def family_of(name):
    return d31.family_of(name)


def measured_by(name, identity, allocated, timed):
    """What measured the attribution of a D2 cell: its family's feasible
    cells of at most 1000 assumptions that passed allocation with an
    attributed identity, and its family's passing cells of the timing
    sample."""
    family = d31.family_of(name)
    cells = [n for n in identity if family and d31.family_of(n) == family
             and n not in cases.INFEASIBLE]
    return dict(
        allocation=sorted(
            n for n in cells if d31.size_of(n) <= d31.ALLOCATION_LIMIT and
            d31.allocation_passed(allocated.get(n)) and
            identity[n]["status"] == "attributed"),
        timing=sorted(n for n in cells if n in timed and
                      timed[n]["cls"] == "pass"))


def judge_identity(identity, failed, missing, owed):
    if identity["status"] == "different":
        failed.append("identity: the loaded closure or the work differs")
    elif identity["status"] not in IDENTITY_OK:
        missing.append("identity: " + str(identity["status"]))
        owed.append("identity-rerun")


def judge_allocation(row, failed, missing, owed):
    if row is None:
        missing.append("allocation: no decision")
        owed.append("allocation-rerun")
        return
    if row["decision"] == "fail":
        failed.append("allocation: fail")
    if row["work"] == "differs":
        failed.append("allocation: the work row differs")
    if row["decision"] == "inconclusive":
        missing.append("allocation: inconclusive")
        owed.append("allocation-rerun")
    elif row["decision"] == "pass" and row["work"] not in (
            "equal", "differs"):
        missing.append("allocation: the work row is %s" % (
            row["work"] or "missing"))
        owed.append("allocation-rerun")


def judge_timing(name, row, d4, failed, missing, owed):
    """The timing decision of a sampled cell; true when the cell's chain is
    one policy D4 disposes: the cell is in D4 and its decisive timing stage
    (the chain's final class, after stage 2 or the follow-up if one ran) is
    control-limited (design decision 16; the other gates still decide). A
    control-limited cell outside D4 owes stage 2, then an attribution. An
    inconclusive cell whose control is invalid and whose stage 2 has not
    run owes `stage2` (the control sizes it), else the `followup`, then an
    attribution."""
    cls = row["cls"]
    if cls == "fail":
        failed.append("timing: fail")
        return False
    if "fail" in row["earlier"] or row["first"] == "fail":
        # a fail of any stage decides: a follow-up or a second stage that
        # passed does not undo it, and D4 can never dispose it
        failed.append("timing: an earlier stage failed")
        return False
    if cls == "pass":
        return False
    if cls == "control_limited" and name in d4:
        return True
    elif cls == "protocol":
        missing.append("timing: no admitted measurement")
        owed.append("redraw")
    elif cls == "control_limited":
        missing.append("timing: control-limited")
        owed.append("attribution" if row["stage2"] else "stage2")
    else:
        missing.append("timing: inconclusive")
        owed.append("attribution" if row["followup"] else
                    "stage2" if row.get("control_open") and
                    not row["stage2"] else "followup")
    return False


def chain_text(row):
    """The timing chain of a cell in words: the stage the first class
    belongs to, whether stage 2 and the follow-up ran, and the classes the
    follow-up replaced; the last class is the decisive stage's."""
    steps = ["first stage %s" % row["first"]]
    steps.append("stage 2 ran" if row["stage2"] else "no stage 2")
    if row["followup"]:
        steps.append("follow-up ran, replacing %s" % (
            ", ".join(row["earlier"]) or "nothing"))
    steps.append("final class %s" % row["cls"])
    return "; ".join(steps)


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
    by_d4 = False
    judge_identity(identity, failed, missing, owed)
    if infeasible:
        found["policy"] = "D2"
        found["note"] = "heavy size-10000 tactic cell: identity only"
        if identity["status"] == "attributed":
            found["measured_by"] = groups
            if not (groups["allocation"] and groups["timing"]):
                missing.append("attribution not measured in its family")
                owed.append("attribution")
    else:
        judge_allocation(allocated, failed, missing, owed)
        if timed is not None:
            by_d4 = judge_timing(name, timed, d4, failed, missing, owed)
        else:
            found["policy"] = "stratified"
            found["note"] = "unsampled: identity and exact allocation"
    found["failed"], found["missing"], found["owed"] = failed, missing, owed
    found["blocked"] = bool(missing) and owed == ["attribution"]
    found["status"] = (STATUS_FAIL if failed else
                       STATUS_INCOMPLETE if missing else STATUS_PASS)
    if by_d4 and found["status"] == STATUS_PASS:
        found["policy"] = "D4"
        found["policy_note"] = (
            "decisive timing stage control-limited (%s): disposed by "
            "policy D4 with identity and exact allocation (work rows "
            "equal)" % chain_text(timed))
        if name in D4_TASK37:
            found["policy_note"] += " (user extension, design decision 46)"
    return found


def status_of(records):
    kinds = {r["status"] for r in records}
    return (STATUS_FAIL if STATUS_FAIL in kinds else
            STATUS_INCOMPLETE if STATUS_INCOMPLETE in kinds else
            STATUS_PASS)


def finish(record):
    """Status of an auxiliary record from its failures and omissions; an
    incomplete one must say what it owes."""
    record["status"] = (STATUS_FAIL if record["failed"] else
                        STATUS_INCOMPLETE if record["missing"]
                        else STATUS_PASS)
    a.require(record["status"] != STATUS_INCOMPLETE or record["owed"],
              "internal error: an incomplete record owes nothing: %s" %
              "; ".join(record["missing"]))
    return record


def grid_record(failed, missing, owed, **more):
    return finish(dict(more, failed=failed, missing=missing, owed=owed))


# the TASK33 S1 kinds that decide the retained graph size and its slopes
RETAINED_CASE = "S1"
RETAINED_KINDS = ("fragment", "compiled", "compiled_bool", "merge",
                  "projection", "conversion")
RETAINED_ALLOCATION = "storage_graph"


def unsampled_sizes(table):
    """The retained slope's sizes the shard of `table` does not sample (the
    six sizes less the `storage_graph` sizes of its part), or None where
    `table` is no shard."""
    for key, part in grid.PARTS.items():
        if grid.name_of(key) == table:
            held = {s for n in part for c_, s in [cases.split(n)]
                    if c_ == RETAINED_ALLOCATION}
            return key, sorted(set(a.SIZES) - held)
    return None, None


def retained_record(table, s, raw, t33, allocation_cases):
    """The retained-slope record of a shard. A slope the shard does not
    sample (blocked, missing exactly the sizes of the six its part does not
    hold) is `not-sampled` and takes the state of the records that decide
    the retained graph size and every adjacent slope exactly: the TASK33
    S1 records and the shard's allocation case of `storage_graph`, each
    named and looked up directly. One that fails fails it; a missing
    decider makes it incomplete, never a pass. Any other blocked slope is a
    measurement gap, and a measured one is judged as measured: both as
    before."""
    key, absent = unsampled_sizes(table)
    if not (raw and raw.get("status") == "blocked" and absent and
            sorted(raw.get("missing_sizes", [])) == absent):
        return grid_record(
            ["retained slope: fail"] if s == "fail" else [],
            [] if s in ("pass", "fail") else ["retained slope: " + s],
            [] if s in ("pass", "fail") else ["retained-slope"], class_=s)
    named = [("%s:%s" % (RETAINED_CASE, k), t33) for k in RETAINED_KINDS]
    named.append(("%s:%s" % (TASKS[grid.KIND[key]], RETAINED_ALLOCATION),
                  allocation_cases))
    state = {k: (src.get(k) or dict(status="absent"))["status"]
             for k, src in named}
    failed = ["retained slope: decided by %s, which failed" % k
              for k, v in sorted(state.items()) if v == STATUS_FAIL]
    missing = ["retained slope: decided by %s, which is %s" % (k, v)
               for k, v in sorted(state.items())
               if v not in (STATUS_PASS, STATUS_FAIL)]
    return grid_record(failed, [] if failed else missing,
                       ["retained-slope"] if missing and not failed else [],
                       class_="not-sampled", decided_by=sorted(state))


def d4_cells():
    """The cells policy D4 disposes: `task37_cases.D4` and `D4_TASK37`,
    each of which must be a cell of the matrix sample outside D4."""
    extra = list(D4_TASK37)
    a.require(len(set(extra)) == len(extra) and all(
        n in cases.MATRIX_SAMPLE and n not in cases.D4 for n in extra),
        "D4_TASK37 is not a set of matrix sample cells outside "
        "task37_cases.D4: %s" % ", ".join(extra))
    return set(cases.D4) | set(extra)


def dispose(identity, allocation, timing, units, decisions33, receipts,
            d4=None):
    """Every workload's record, the status of the whole. `identity`,
    `allocation` map their kind (client, matrix, downstream) to the loaded
    tables, `timing` maps a table to its loaded rows, `receipts` maps a gate
    to its record."""
    d4 = d4_cells() if d4 is None else set(d4)
    ident = {n: row for k in identity.values() for n, row in
             k["cells"].items()}
    alloc = {n: row for k in allocation.values() for n, row in
             k["rows"].items()}
    timed = {n: row for k in timing.values() for n, row in
             k["cells"].items()}
    order = (cases.MATRIX_CELLS + cases.CLIENT_CELLS +
             cases.DOWNSTREAM_CELLS)
    a.require(set(order) == set(ident) and len(order) == len(ident),
              "the identity tables are not the cells of TASK37")
    records = {}
    for n in order:
        groups = measured_by(n, identity["client"]["cells"], alloc, timed) \
            if n in cases.INFEASIBLE else None
        records[n] = judge(n, ident[n], alloc.get(n), timed.get(n), d4,
                           groups)
    unit_records = {u: finish(dict(r)) for u, r in units.items()}
    t33 = {k: finish(dict(r)) for k, r in decisions33.items()}
    gate_records = {g: finish(dict(r)) for g, r in receipts.items()}
    identity_grids = {}
    for kind, found in identity.items():
        bad = found["status"] == "different" or bool(found["unaccounted"])
        open_ = found["status"] not in IDENTITY_OK
        identity_grids[kind] = grid_record(
            ["identity grid %s: %s" % (kind, found["status"])] if bad
            else [],
            ["identity grid %s: %s" % (kind, found["status"])]
            if open_ and not bad else [],
            ["identity-rerun"] if open_ and not bad else [],
            status_text=found["status"])
    allocation_cases = {k: finish(dict(r)) for t in allocation.values()
                        for k, r in t["cases"].items()}
    timing_grids = {}
    for table, found in timing.items():
        diff = found["differing"]
        timing_grids[table] = grid_record(
            [], ["source identity: %s differ without a reviewed pin" %
                 ", ".join(diff)] if diff else [],
            ["attribution"] if diff else [], differing=diff)
    scaling_records = {
        t: retained_record(t, v["scaling"], v["scaling_raw"], t33,
                           allocation_cases)
        for t, v in timing.items() if v["scaling"] is not None}
    auxiliary = [("identity_grid", identity_grids),
                 ("allocation_case", allocation_cases),
                 ("timing_grid", timing_grids),
                 ("retained_slope", scaling_records)]
    every = (list(records.values()) + list(unit_records.values()) +
             list(t33.values()) + list(gate_records.values()) +
             [r for _, rows in auxiliary for r in rows.values()])
    counts = {k: sum(r["status"] == k for r in every)
              for k in (STATUS_PASS, STATUS_FAIL, STATUS_INCOMPLETE)}
    owed = [dict(workload=w, owed=o) for w, r in (
        list(records.items()) + list(unit_records.items()) +
        list(t33.items()) + list(gate_records.items()) +
        [("%s:%s" % (label, k), r) for label, rows in auxiliary
         for k, r in rows.items()]) for o in r["owed"]]
    policies = {p: sorted(n for n, r in records.items()
                          if r["policy"] == p)
                for p in ("D2", "D4", "stratified")}
    return dict(
        schema=SCHEMA, status=status_of(every), counts=counts,
        kinds=dict(matrix=len(cases.MATRIX_CELLS),
                   client=len(cases.CLIENT_CELLS),
                   downstream=len(cases.DOWNSTREAM_CELLS),
                   task32_units=len(unit_records),
                   task33_decisions=len(t33), gates=len(gate_records)),
        identity_status={k: v["status"] for k, v in identity.items()},
        identity_unaccounted={k: v["unaccounted"] for k, v in
                              identity.items()},
        cells=records, task32=unit_records, task33=t33, gates=gate_records,
        identity_grid=identity_grids, allocation_case=allocation_cases,
        timing_grid=timing_grids, retained_slope=scaling_records,
        policies=policies, owed=owed)


# ------------------------------------------------------------- the command

def environment_events(paths, timing):
    """The environment events (`--environment-event`, resolved paths) and
    the void attempts of the timing tables they account for: {events:
    [{path, seal}], attempts: [{table, attempt, refusals}]}. At least one
    event is needed when an attempt is void by the environment rule, and an
    event needs such an attempt (decision 45)."""
    voided = [dict(table=t, attempt=x["attempt"],
                   refusals=x["environment"])
              for t, found in timing.items() for x in found["attempts"]
              if x.get("environment")]
    names = ", ".join("%s %s" % (v["table"], v["attempt"])
                      for v in voided)
    a.require(not voided or paths, "no --environment-event for the "
              "attempt(s) void by an environment refusal: %s" % names)
    a.require(not paths or voided, "an environment event with no attempt "
              "it voids")
    return dict(events=[dict(path=str(p), seal=a.seal(p)) for p in paths],
                attempts=voided)


def timing_options(args):
    """The per-shard options of the command, by option name."""
    keys = grid.SHARD_KEYS
    found = dict(
        timing=keyed(args.timing, "timing", keys),
        ledger=keyed(args.ledger, "ledger", keys),
        followup=keyed_rounds(args.followup, "followup", keys),
        pilot=keyed(args.pilot, "pilot", keys))
    found["followup-pilot"] = keyed_rounds(args.followup_pilot,
                                           "followup-pilot", keys)
    return found


LOADING_KEYS = {gate: module.lower() for gate, module in
                gates.LOADING.items()}


NO_NULL = ("absent (the attempt ended before the null gate, or its null "
           "does not replay)")
NULL_NA = ("not applicable (the gate failed or was blocked: the null "
           "control is neither read nor replayed)")


def startup_null(args, verdict, harness):
    """The null control archive of the judged startup attempt (its
    `verdict`, `gates.startup_attempts`), or None when it is not read. The
    null of every attempt is exactly `<attempt>/gate-null`. A complete
    attempt (`judged`) always has a replayed null control, so
    `--startup-null` is required (and it is replayed late). A
    `judged-incomplete` one (the gate failed or was blocked) is never read,
    so the flag is refused there. One owing a redraw (`owes-redraw`) may
    have ended before the null gate: its own `gate-null` is read when it
    holds a complete archive that replays and is otherwise absent (design
    decisions 28, 31); the flag, when given, must be that complete archive
    and it must replay (refused otherwise)."""
    own = Path(args.startup_gate).resolve().parent / "gate-null"
    if verdict == "judged":
        a.require(args.startup_null is not None,
                  "a complete startup attempt needs --startup-null")
        a.require(Path(args.startup_null).resolve() == own,
                  "--startup-null %s is not the gate-null of the judged "
                  "attempt (%s)" % (args.startup_null, own))
        return own
    a.require(verdict in ("owes-redraw", "judged-incomplete"),
              "unexpected startup verdict " + verdict)
    if verdict == "judged-incomplete":
        a.require(args.startup_null is None,
                  "--startup-null is for a complete attempt only: the null "
                  "control of an incomplete attempt whose gate failed or "
                  "was blocked is not read (omit the flag)")
        return None
    ok, reason = gates.replays(own, null=True, harness=harness) \
        if gates.archive_complete(own) else (False, "")
    if args.startup_null is not None:
        a.require(Path(args.startup_null).resolve() == own and
                  gates.archive_complete(own),
                  "--startup-null %s is not the complete gate-null archive "
                  "of the incomplete attempt (%s): omit the flag, the null "
                  "of an incomplete attempt is found by itself" % (
                      args.startup_null, own))
        a.require(ok, "--startup-null %s does not replay (%s): omit the "
                  "flag, the null of an incomplete attempt is then "
                  "recorded absent" % (args.startup_null, reason))
    return own if ok else None


def read_gates(args, lineage, inputs, late, extra):
    """The gate records and the receipt of the D7 timing: the startup gate
    and the two loading runs are read (their statuses are those of their
    archives) and their replays added to `late`. `extra` receives the
    startup attempts and the declared deltas for the record."""
    found = {}
    ledgers = keyed(args.loading_ledger, "loading-ledger",
                    tuple(LOADING_KEYS.values()))
    a.require(set(ledgers) == set(LOADING_KEYS.values()),
              "--loading-ledger GATE=FILE is needed for each loading gate "
              "(%s): each shard has its own clone and ledger" %
              ", ".join(sorted(LOADING_KEYS.values())))
    a.require(args.startup_gate is not None,
              "the startup gate needs --startup-gate")
    attempts = gates.startup_attempts(args.startup_ledger,
                                      args.startup_gate)
    harness = gates.attempt_harness(attempts[-1])
    header, decisions = gates.read_startup(args.startup_gate, False,
                                           lineage, harness)
    record_seal = gates.check_record(header, args.startup_record, lineage)
    inputs[gates.STARTUP] = {
        n: a.seal(Path(d) / f) for n, d, f in (
            ("header", args.startup_gate, "header.json"),
            ("decisions", args.startup_gate, "decisions.json"))}
    inputs[gates.STARTUP]["record"] = record_seal
    declared, inputs[gates.STARTUP]["declared"] = gates.read_declared(
        args.startup_declared, header, args.startup_record)
    problems = gates.declared_problems(declared, decisions)
    attempt = Path(args.startup_gate).resolve().parent
    a.require(Path(args.startup_declared).resolve() ==
              attempt / "declared-deltas.json",
              "--startup-declared %s is not the declared-deltas.json of "
              "the judged attempt (%s)" % (args.startup_declared, attempt))
    verdict = attempts[-1]["verdict"]
    null = startup_null(args, verdict, harness)
    null_decisions = None
    if null is None:
        why = NULL_NA if verdict == "judged-incomplete" else NO_NULL
        inputs[gates.STARTUP]["null-header"] = why
        inputs[gates.STARTUP]["null-decisions"] = why
    else:
        a.require(Path(args.startup_gate).resolve().parent == Path(
            null).resolve().parent,
            "the startup gate and its null control are not of one attempt")
        _, null_decisions = gates.read_startup(
            null, True, lineage, harness, "startup-gate null control")
        inputs[gates.STARTUP]["null-header"] = a.seal(
            Path(null) / "header.json")
        inputs[gates.STARTUP]["null-decisions"] = a.seal(
            Path(null) / "decisions.json")
    found[gates.STARTUP] = gates.startup_gate(header, decisions,
                                              null_decisions, problems)
    inputs[gates.STARTUP]["ledger"] = a.seal(Path(args.startup_ledger))
    a.require((attempt / "inputs.txt").is_file(),
              "the judged startup attempt has no sealed inputs.txt: %s" %
              attempt)
    inputs[gates.STARTUP]["attempt-inputs"] = a.seal(attempt / "inputs.txt")
    inputs[gates.STARTUP]["done"] = a.seal(attempt / "done") \
        if (attempt / "done").is_file() else "absent"
    if verdict == "judged-incomplete":
        a.require(found[gates.STARTUP]["source"] in ("fail", "inconclusive"),
                  "the incomplete startup attempt's gate failed or was "
                  "blocked and its status is %s, not fail or inconclusive"
                  % found[gates.STARTUP]["source"])
    if verdict == "owes-redraw":
        found[gates.STARTUP] = gates.owe_redraw(found[gates.STARTUP],
                                                attempts[-1])
    extra["startup_attempts"] = attempts
    extra["startup_declared"] = dict(
        totals=declared["totals"], archive=declared["archive"],
        archive_sha256=declared["archive_sha256"], problems=problems)
    late.append((gates.STARTUP, lambda: (
        gates.replay_startup(args.startup_gate, args.startup_record,
                             harness),
        None if null is None else gates.replay_startup(null, None,
                                                       harness))))
    reports = {}
    for gate, root in zip(sorted(gates.LOADING),
                          (args.loading_conglib, args.loading_simplib)):
        a.require(root is not None, "no loading run for " + gate)
        report, status = gates.read_loading(root, gate, lineage)
        reports[gate] = report
        found[gate] = gates.loading_gate(gate, report, status)
        ledger = ledgers[LOADING_KEYS[gate]]
        a.require(ledger.is_file(), "the %s ledger is missing: %s" % (
            gate, ledger))
        inputs[gate] = dict(loading=a.seal(Path(root) / "loading.json"),
                            ledger=a.seal(ledger))
        late.append((gate, lambda root=root, ledger=ledger:
                     gates.replay_loading(root, ledger)))
    inputs["api-audit"] = gates.check_one_audit(reports)
    d7 = None
    if args.d7_build is not None:
        d7 = gates.load_receipt(args.d7_build, lineage)
        inputs[D7] = d7["seal"]
    return found, d7


def derive(args, held=None):
    """The record derived from the inputs. `held`, the recorded
    disposition of a `--check`, may hold an earlier HEAD of the checkout
    (a later commit touched only the performance area): that is accepted
    by `Lineage.recorded_head` and substituted, as the code seals are."""
    lineage = lineage_of.Lineage(args.repo, args.candidate)
    repo = lineage.repo
    head = lineage.head()
    if held is not None and held.get("head") != head:
        head = lineage.recorded_head(held.get("head"))
    compiled_ref = lineage.compiled_ref(cases.COMPILED_REF)
    options = timing_options(args)
    identity_ledgers = keyed(args.identity_ledger, "identity-ledger", KINDS)
    alloc_ledgers = keyed(args.alloc_ledger, "alloc-ledger",
                          tuple(TASKS.values()))
    loads, load_seals = load_loads(keyed(args.load, "load"))
    events = sorted({Path(p).resolve()
                     for p in args.environment_event or ()})
    for p in events:
        a.require(p.is_file(), "the environment event is missing: %s" % p)
    document = reviewed.load(cases.REVIEWED_FILE)
    inputs = dict(load_seals, reviewed=document["seal"])
    late = []
    # All reads, ties, joins and cheap checks come first.
    identity = {}
    for kind, root, names in (
            ("client", args.identity_client, cases.CLIENT_CELLS),
            ("matrix", args.identity_matrix, cases.MATRIX_CELLS),
            ("downstream", args.identity_downstream,
             cases.DOWNSTREAM_CELLS)):
        a.require(root is not None, "no identity table for %s cells" % kind)
        identity[kind] = read_identity(
            root, "identity " + kind, names, lineage, kind,
            identity_ledgers.get(kind), repo, late)
        inputs["identity-" + kind] = identity[kind]["seals"]
    allocation = {}
    for kind, root, names, skipped in (
            ("matrix", args.alloc_matrix, cases.MATRIX_CELLS, ()),
            ("client", args.alloc_client, cases.CLIENT_ALLOCATED,
             cases.INFEASIBLE),
            ("downstream", args.alloc_downstream, cases.DOWNSTREAM_CELLS,
             ())):
        task = TASKS[kind]
        a.require(root is not None, "no allocation output for " + task)
        allocation[kind] = read_allocation(
            root, task, names, skipped, lineage, alloc_ledgers.get(task),
            late)
        inputs["allocation-" + kind] = allocation[kind]["seals"]
    timing = {}
    for kind, sample in (("client", cases.CLIENT_SAMPLE),
                         ("matrix", cases.MATRIX_SAMPLE)):
        timing.update(read_timing(kind, sample, options, lineage, repo,
                                  document, late))
    extra = set(options["followup-pilot"]) - set(options["followup"])
    a.require(not extra, "--followup-pilot names a shard with no "
              "--followup: %s" % ", ".join(sorted(extra)))
    for table, found in timing.items():
        inputs[table] = found["seals"]
        inputs[table + "-pins"] = found["pins"]
    units, inputs["task32"], _ = gates.read_task32(args.task32, lineage)
    a.require(args.task32_replay, "no --task32-replay arguments")
    t33, reported33, carried33, inputs["task33"], _ = gates.read_task33(
        args.task33, lineage)
    a.require(args.task33_replay, "no --task33-replay arguments")
    inputs["task32-replay"], inputs["task33-replay"] = (
        args.task32_replay, args.task33_replay)
    extra = {}
    receipts, d7 = read_gates(args, lineage, inputs, late, extra)
    # The replays come last: they are the expensive part.
    late.append(("task32", lambda: gates.replay_task32(
        args.task32, args.task32_replay, lineage)))
    late.append(("task33", lambda: gates.replay_task33(
        args.task33, args.task33_replay, lineage)))
    for _, replay in late:
        replay()
    events = environment_events(events, timing)
    record = dispose(identity, allocation, timing, units, t33, receipts)
    record.update(
        candidate=lineage.candidate, baseline=a.BASE, head=head,
        compiled_ref=compiled_ref,
        startup_attempts=extra["startup_attempts"],
        startup_declared=extra["startup_declared"],
        candidates=dict(sorted(lineage.recorded.items())),
        tree_outside_performance=lineage.tree,
        scope=SCOPE, inputs=inputs, code=seals(),
        allocation_pairs={k: v["pairs"] for k, v in allocation.items()},
        allocation_status={TASKS[k]: v["state"] for k, v in
                           allocation.items()},
        attempts=dict(
            identity={k: v["attempts"] for k, v in identity.items()},
            allocation={TASKS[k]: v["attempts"] for k, v in
                        allocation.items()},
            timing_ledger={t: v["counts"] for t, v in timing.items()}),
        timing_attempts={t: v["attempts"] for t, v in timing.items()},
        environment_events=events, d4_extension=list(D4_TASK37),
        shards={t: sorted(v["cells"]) for t, v in timing.items()},
        followup_rounds={t: v["rounds"] for t, v in timing.items()},
        host_load=loads,
        reported=dict(
            task33=reported33, task33_carried=carried33,
            d7_build=None if d7 is None else dict(
                status=d7["status"], exit=d7["exit"],
                note=d7.get("note", ""), gate=False,
                **({"build_base": d7["build_base"]}
                   if d7.get("build_base") is not None else {}))))
    return record


def lines(record):
    out = []
    for table, found in record["timing_attempts"].items():
        for x in found:
            out.append("TIMING-ATTEMPT %s %s status %s: %s" % (
                table, x["attempt"], x["status"],
                "void (environment: %s)" % "; ".join(x["environment"])
                if x.get("environment") else
                "void (no measurement admitted)" if x["void"]
                else "judged"))
    for task, found in record["attempts"]["allocation"].items():
        for x in found or ():
            out.append("ALLOCATION-ATTEMPT %s %s status %s: %s" % (
                task, x["attempt"], x["status"],
                "void (every cell archive rejected on replay)"
                if x["void"] else "judged"))
            out += ["ALLOCATION-ATTEMPT %s %s rejected %s: %s" % (
                task, x["attempt"], r["archive"], r["reason"])
                for r in x.get("rejections", ())]
    for x in record["startup_attempts"]:
        out.append("STARTUP-ATTEMPT %s %s: %s" % (
            x["attempt"], x["status"], "judged" if x["judged"] else
            "earlier attempt, kept in the ledger (R-1): %s%s" % (
                x["verdict"], "; gate %s: %s" % (
                    x["decision"], "; ".join(x["problems"]))
                if x["decision"] else "")
            + ("; replay: %s" % x["replay"] if x.get("replay") else "")))
    for kind, paths in record["identity_unaccounted"].items():
        out += ["FAIL identity %s: unaccounted difference %s" % (kind, p)
                for p in paths]
    groups = [("cell", record["cells"]), ("task32", record["task32"]),
              ("task33", record["task33"]), ("gate", record["gates"]),
              ("identity-grid", record["identity_grid"]),
              ("allocation-case", record["allocation_case"]),
              ("timing-grid", record["timing_grid"]),
              ("retained-slope", record["retained_slope"])]
    for label, rows in groups:
        for name, r in rows.items():
            slope = r.get("class_") == "not-sampled"
            if r["status"] == STATUS_PASS and not slope and \
                    not r.get("policy") in ("D2", "D4"):
                continue
            why = r["failed"] + r["missing"] or (
                ["not-sampled, decided by " + ", ".join(r["decided_by"])]
                if slope else [
                    "policy %s: %s" % (r["policy"], r.get("policy_note")
                                       or r.get("note"))])
            out.append("%s %s %s: %s%s" % (
                r["status"].upper(), label, name, "; ".join(why),
                " [owed: %s]" % ", ".join(r["owed"]) if r["owed"] else ""))
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
        "not provided" if d7 is None else "%s, exit %s %s%s" % (
            d7["status"], d7["exit"], d7["note"],
            "" if d7.get("build_base") is None else
            " [timed base %s, child of %s changing %s: %s]" % (
                d7["build_base"]["commit"], d7["build_base"]["parent"],
                ", ".join(d7["build_base"]["paths"]),
                d7["build_base"]["why"]))))
    return "\n".join(text) + "\n"


def disposition(args):
    if args.check:
        held_path = Path(args.check) / "disposition.json"
        held = read(held_path, "the recorded disposition")
        check_code(held.get("code"))
    record = derive(args, held if args.check else None)
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
    add("--gate", required=True, choices=(D7,))
    add("--candidate", required=True)
    add("--status", required=True, choices=gates.RECEIPT_STATUS)
    add("--exit", type=int, required=True, dest="exit_status")
    add("--out", type=Path, required=True)
    add("--report", type=Path, action="append", default=[])
    add("--attribution", action="append", default=[])
    add("--note", default="")
    args = p.parse_args(argv)
    a.save(args.out, gates.make_receipt(
        args.gate, args.candidate, args.status, args.exit_status,
        args.report, args.attribution, args.note))
    return 0


def parser():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    add = p.add_argument
    add("--candidate", required=True)
    for name in KINDS:
        add("--identity-" + name, type=Path, help="identity table")
        add("--alloc-" + name, type=Path, help="allocation output")
    add("--identity-ledger", action="append", metavar="KIND=FILE",
        help="the attempts ledger of the identity grid of KIND (client, "
        "matrix, downstream); one for each kind")
    add("--alloc-ledger", action="append", metavar="TASK=FILE",
        help="the attempts ledger of an allocation task (task37-matrix, "
        "task37-client, task37-downstream); one for each")
    add("--timing", action="append", metavar="SHARD=DIR",
        help="the final stage of a timing shard (client-1, client-2, "
        "matrix-1 ... matrix-4); every shard is required")
    add("--ledger", action="append", metavar="SHARD=FILE",
        help="the attempts ledger of a shard; one for each shard")
    add("--pilot", action="append", metavar="SHARD=DIR",
        help="the pilot of a shard; one for each shard")
    add("--followup", action="append", metavar="SHARD[.R]=DIR",
        help="the declared follow-up of a shard (SHARD=DIR) and of each "
        "further declared round (SHARD.R=DIR)")
    add("--followup-pilot", action="append", metavar="SHARD[.R]=DIR",
        help="the pilot of the follow-up (round R) of a shard")
    add("--environment-event", action="append", metavar="FILE",
        help="the system record (an apt/dpkg log excerpt) of an environment "
        "change that voided a timing attempt (decision 45); required for "
        "such an attempt, refused without one")
    add("--load", action="append", metavar="STREAM=FILE",
        help="a host-load recording of a stream (task37_load.py), "
        "reported only")
    add("--task32", type=Path)
    add("--task32-replay", metavar="ARGS", help="the arguments of "
        "`task32_downstream.py dispose`, without --out, in one string")
    add("--task33", type=Path)
    add("--task33-replay", metavar="ARGS", help="the arguments of "
        "`task33_storage.py dispose`, without --out, in one string")
    add("--startup-gate", type=Path, help="the startup gate archive")
    add("--startup-null", type=Path, help="its null control's archive "
        "(required unless the attempt is incomplete)")
    add("--startup-record", type=Path, help="the record the gate is "
        "sealed to")
    add("--loading-simplib", type=Path, help="the loading run of simpLib")
    add("--loading-conglib", type=Path, help="the loading run of congLib")
    add("--loading-ledger", action="append", metavar="GATE=FILE",
        help="the attempts ledger of a loading shard's clone, one for each "
        "gate (simplib, conglib); both are required")
    add("--startup-ledger", type=Path, help="the startup-gate attempts "
        "ledger of run_startup_gate.sh; the judged gate is its last attempt")
    add("--startup-declared", type=Path, help="the declared load deltas "
        "(declared-deltas.json) fill_record.py wrote beside the record")
    add("--d7-build", type=Path, help="D7 build receipt (reported only)")
    add("--repo", type=Path, default=a.HERE.parents[3],
        help="the checkout that holds this code (the only one accepted)")
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--record", type=Path, help="write to this new dir")
    mode.add_argument("--check", type=Path, help="require this recorded "
                      "disposition to be derived again")
    return p


def main(argv=None):
    """The status of the disposition, or REFUSED (3) with one line on the
    standard error."""
    argv = sys.argv[1:] if argv is None else argv
    with tg.terminating_as_interrupt(), gates.harness_scope():
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
