#!/usr/bin/env python3
"""Task-independent paired timing grid under the equivalence policy.

The machinery TASK29A confirmed, parameterized by a `Table` that names a
task's cases, batch seconds, predeclared counts and code seals:

- develop-only pilot and predeclared batch counts (`pilot`, `predeclare`),
  so neither side can select its own count;
- layout-randomized paired cells, a first stage and a second stage whose
  pair counts come from the develop/develop control alone (`run`, `extend`);
- lossless archives, offline replay of every decision (`replay`), and
  resume after an infrastructure failure (`--resume`).

Policy: acceptance.EQUIVALENCE_POLICY (3% margin on inclusive CPU and wall,
B/B validity window, GC reported and not gated). Nothing here decides that a
non-passing cell is acceptable: `classify` reports pass, fail, inconclusive,
control-limited and protocol-failed cells separately, and the exit status is
zero only when every cell passes. A task that needs a disposition supplies its
own explicit, separately reviewed table (see task29a_grid.py).

Every step of `Grid` is looked up on its `hooks` object (the grid itself by
default), so a task module can wrap or replace a step by defining it.

A table with `fixed_seconds` keeps its predeclaration in one committed counts
file: the batch counts, the seconds of each cell, the headroom, the layout
seed, the pairs and samples, the target and cap of the second stage (all
fields of the table), the seals of the files the counts are bound to, and the
seals of the pilot that produced them. `run`
takes them from that file, refuses other values, refuses a candidate whose
history does not hold the file as exactly one commit, and re-derives the file
from its pilot (`--pilot`, the same check as `verify-counts`). It measures
only in a clean checkout at the candidate in which `prepare` built (the
tree outside the performance area and the shared products, bin/hol,
bin/hol.state0, bin/Holmake, sigobj, and the theory data files and sources,
are those it stamped, and the grid records their digest; `prepare` runs
configure and then the build, Holmake judges what a build must redo, the
driver only compares contents). Every run appends to the table's
attempts ledger, one hash-chained file below the checkout that git excludes,
and a replay needs the grid's opening line in it and prints every attempt of
the table. The ledger is a discipline and not a proof. A counts file is
never edited: a revision is a new file named in the table, derived from the
file before it, by rescaling cells or by a fresh pilot.

A table declares its fixed-count schedule, `warmup` by default. `warmup`
runs one recorded warm-up batch of N and then the samples of N, N any
integer: the largest over the pilot's processes of ceil(HEADROOM * seconds *
n / wall) of the final calibration batch (`warmup_count`), the headroom being
1 for a new table. `ramp` (the counts file names no schedule) is the
historical one: every process calibrates 1, 2, 4, ..., N and then takes its
samples of N, N a power of two, HEADROOM times the largest final calibration
count of the pilot; a table without fixed seconds, and the TASK30 and
TASK29A tables, whose counts and archives are ramp, declare it. The counts
file records the schedule and the rule, and a replay derives both again; a
counts revision of a warmup table rescales a cell whose warm-up or batch was
too short by the same factor. The default follows the TASK30A validation
(2026-11-03, 12 cells, 20 pairs, 5 samples): the median ratio of the B/B
interval widths, warmup over ramp, was 1.005 (CPU) and 1.004 (wall) at 0.38
of the time, so "R <= 1.10: adopt warmup with unchanged pairs".

A table may be a follow-up (`replaces`, `cells`): it takes over the cells
of an earlier grid that ended inconclusive and measures only those, as a
complete table of its own, under the same ledger (`family`). Its pairs per
cell come from the replaced grid's first-stage develop/develop control by the
second-stage rule. It decides its own cells only; combining its decision
with the replaced grid's is the disposition step's (PROTOCOL.md). See the
Follow-up section of `Grid`.
"""
import argparse
import contextlib
import copy
import datetime
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import traceback
import uuid

sys.dont_write_bytecode = True
import acceptance as a
sys.path.insert(0, str(a.HERE / "allocator-counter"))
import evidence_bundle as bundle
import matrix_schema as ms
import private_runtime as pr
import task29_gate as gate
from performance_schema import batch_iterations, batch_schedule, layout_seed

# The B/B control for a metric is outside the equivalence window.
CONTROL = "baseline-control outside equivalence window"
# Second stage, predeclared with the first-stage grid.
TARGET = 0.015
MAX_PAIRS = 120
CLASSES = ("pass", "fail", "inconclusive", "control_limited", "protocol")
# A counts revision multiplies the counts of the cells it names by this
# factor, for the one reason the protocol allows.
REVISION_FACTOR = 4
REVISION_REASON = "fixed calibration too short"
# The same for a table of the warmup schedule, whose too short batch is the
# warm-up or a sample ("batch too short").
WARMUP_REVISION_REASON = "fixed batch too short"
# How the counts are made. `ramp` (the historical schedule): a power of two,
# HEADROOM times the largest final calibration count of the develop-only
# pilot. `warmup`: one batch of N iterations, N any integer, large enough
# that a batch lasts about the target seconds of the pilot's final batch.
RAMP_RULE = "HEADROOM * max develop calibration count in B/B"
WARMUP_RULE = ("max over develop processes of ceil(HEADROOM * seconds * n / "
               "wall), (n, wall) the final calibration batch of a pilot "
               "process, in exact decimal arithmetic")


def schedule_of(counts):
    """`ramp` or `warmup`, as a counts file (or an inventory) says it. The
    field names only `warmup`: a ramp record has none, and a record that
    names `ramp` is refused."""
    return batch_schedule(counts.get("schedule"))


def warmup_count(headroom, seconds, finals):
    """The count of one cell under the warmup rule: the largest, over the
    develop-only processes, of ceil(headroom * seconds * n / wall) for the
    final calibration batch of n iterations that took wall seconds. The
    arithmetic is exact on the shortest decimal each float is written as
    (a JSON number read again is the same float, so the same decimal), so
    that a replay derives the same integer on every host and no product
    rounds across an integer."""
    a.require(type(headroom) is int and headroom >= 1 and finals and
              all(type(n) is int and n >= 1 and type(w) is float and
                  math.isfinite(w) and w > 0 for n, w in finals) and
              type(seconds) in (int, float) and math.isfinite(seconds) and
              seconds > 0, "invalid warm-up count inputs")
    seconds = Fraction(repr(seconds))
    return batch_iterations(max(
        -(-headroom * seconds * n // Fraction(repr(wall)))
        for n, wall in finals), "warmup")


class CheckoutChanged(ValueError):
    """The checkout a measurement started in is not the one it ended in, or
    could not be judged. `dead` is whether the checkout is known to differ
    from the record (a head, a tree or products), which no `prepare` can
    undo; a checkout that only could not be judged (`CheckoutUnjudged`) is
    not."""

    def __init__(self, message, dead=True):
        super().__init__(message)
        self.dead = dead


class CheckoutRefused(ValueError):
    """What `checkout_identity` refuses: `what`, and `fresh`, the words that
    end it for a fresh start (the text is `what: fresh`). `resumed` is the
    same refusal as a resumption or a second stage gives it, which ends
    with `RESUMING` instead: that is the one place the words of a
    resumption are added."""

    def __init__(self, what, fresh=None):
        super().__init__(what if fresh is None else "%s: %s" % (what, fresh))
        self.what = what

    def resumed(self):
        return type(self)(self.what, RESUMING)


class CheckoutUnjudged(CheckoutRefused):
    """The checkout cannot be compared with the stamp: it is not clean, or
    there is no usable stamp. By itself that says nothing about the
    checkout the record names; `known_difference` asks what can still be
    judged."""


# The modules whose behaviour the replay of a replaced grid depends on, beside
# the replaced table's pin file and counts file (`Grid.replay_code`; the
# table's own sealed files and driver are sealed by its inventories). The
# counts of a follow-up record their seals when `predeclare` replays the grid
# in full as a record of what it replayed with, never re-derived. While the
# code is the same, the sealed commands bind the grid by its seals
# (`bind_sealed`); when it has changed, they replay the grid in full
# (`bind_replaced`). A hand list, not derived at run time: a `sys.modules`
# filter depends on which lazy imports have run, so the recorded set would
# differ between `predeclare` and `run`, and a static closure pulls in the
# modules only `close` imports. The list cannot drift unnoticed: a test
# computes the static import closure of the replay path and asserts that
# this list, the table's sealed files and its pin file cover it.
REPLAY_CODE = ("timing_grid.py", "acceptance.py", "summarize.py",
               "audit_evidence.py", "runtime_metrics.py")


class Replaces:
    """The grid a follow-up table replaces: the `engine` that measured it
    (the table with the hooks its module gave it; it replays the grid) and
    the rule that names the cells taken over, which is `inconclusive` (the
    cells whose class is that, see `classify_row`), the only one there is."""

    def __init__(self, engine, rule="inconclusive"):
        a.require(rule == "inconclusive", "unknown replacement rule")
        a.require(isinstance(engine, Grid), "malformed replaces: it names "
                  "the engine of the table replaced")
        self.engine, self.rule = engine, rule

    @property
    def table(self):
        return self.engine.t


class Table:
    """What a task supplies. Only data, no behaviour.

    cases: matrix case names; their sizes come from the matrix ledger.
    driver: the task's own module file, sealed into every inventory.
    counts: the committed predeclared counts file; revisions: the further
        files, in order, each derived from the one before it by
        `predeclare --revises` (a counts file is never edited, so a revision
        is a new path; a path is absolute or below `home`). A run uses the
        last; a replay uses the file its grid names.
    seconds, seconds_by_case: calibration target of a batch; a longer target
        for the cases that name it (tiny operations).
    pairs, samples: defaults of a grid; pilot_pairs, pilot_samples: of a
        pilot (the protocol minimum is ten pairs and three samples).
    baseline: the commit every B/B control and every comparison starts from;
        the counts, the pilot and the run must all name it.
    fixed_seconds: the counts file is the predeclaration (see the module
        docstring): it names each cell's seconds, the layout seed, pairs and
        samples, and a run uses those and no others (a task whose runs
        predate this keeps --batch-seconds, --pairs and --samples free).
    schedule: the fixed-count schedule of every process of the grid:
        `warmup` (the default: one recorded batch of N, any N, then the
        samples), whose counts follow `warmup_count`, or `ramp` (every count
        1, 2, 4, ..., N, a power of two). The headroom defaults to 1 for
        warmup and 2 for ramp. The default schedule does not depend on the
        other arguments, and a warmup table needs fixed seconds, so a table
        without them must name `schedule="ramp"`, as the TASK30 and TASK29A
        tables do: their counts, pilots and archives are ramp.
    pairs, samples and seed (the layout seed) are then fields of the table,
        as are headroom, target and max_pairs and the seconds: sealed with
        the driver, `predeclare` copies them into the counts file and `run`
        refuses a file that differs, so changing one is a visible commit of
        the table. A replay and the derivation of a counts file take them
        (the seconds of each cell, the headroom, and the target and cap of
        the second stage included) from the file, so that an older file
        stays replayable whatever the table says now.
    drivers, acceptance, layout_acceptance, engines: seals of earlier code
        whose recorded runs must still replay.
    engine: seal this module too (a task whose runs predate it does not).
    sealed: files of the directory `home` (names) whose seals every
        inventory records, with sealed_history their earlier seals by name.
    sources: files of the repository (paths) whose git blobs must be the
        same at the baseline and at the candidate; a run records them and a
        difference is never a pass.
    pinned: reviewed differences among the sources, {path: dict(blob=,
        reason=)}: a source that differs from the baseline is accepted
        (published, not a failure) only when its candidate blob is the
        pinned one. A pin outside `sources`, or on a file that does not
        differ from the baseline, is an error.
    pin_file: the file of `home` that holds the pins, sealed in every
        inventory of a run apart from `sealed` (the pins are facts of the
        candidate, so the counts are not bound to them), with pin_history,
        {sha256 of an earlier version of the file: the pins it held}, for
        the grids whose recorded pins have since changed (kept in the pin
        file itself, so that adding one changes no driver seal).
    ledger: the attempts ledger; by default `.agent-files/evidence/<name>/
        attempts.jsonl` below the root of the checkout, the one place the
        table has (a test names another). The build stamp of `prepare` is
        beside it.
    tree: a path of the repository whose whole name-status difference between
        the baseline and the candidate a run records and a replay derives
        again, so that the difference outside `sources` is published too.
    require_seed: refuse a first stage without layout randomization.
    cells: the names (`case-size`) of the cells of `cases` the table
        measures, all of them when none; pilot, counts, run, second stage and
        decision then work on these and are a complete table's.
    family: the name under which the table keeps its evidence: the directory
        of the attempts ledger and of the build stamp, and the refs that
        keep its commits (`name` when none). A follow-up names the family of
        the table it replaces, so that both are attempts of one ledger.
        Schemas keep the table's own name.
    replaces: a `Replaces`, for a follow-up. The table then names `cells`
        and a fixed-count table with fixed seconds; its baseline, the target
        and cap of the second stage and the seconds of its cells are those of
        the replaced table, its pairs are twice the replaced table's, and its
        layout seed, and the seed of its second stage, are other than the
        replaced table's two. `run`, `extend`, `replay`, `predeclare` and
        `verify-counts` then take the replaced grid (`Grid.bind_replaced`).
        The pairs of each cell are not a field of the table but derive from
        that grid (`Grid.followup_pairs`), and the counts file records them
        (`pairs_by_cell`), so `pairs` is their floor.
    root: the root of the repository the code is in (default: that of this
        module). The names of the sealed files and of the driver in the
        repository (`Grid.sealed_paths`) are relative to it, whatever
        checkout a command is pointed at."""

    def __init__(self, name, label, cases, driver, counts, *, seconds=0.3,
                 seconds_by_case=None, fixed_seconds=False, pairs=10,
                 samples=3, seed=None, revisions=(), pilot_pairs=10,
                 pilot_samples=3, headroom=None, schedule="warmup",
                 target=TARGET,
                 max_pairs=MAX_PAIRS, baseline=a.BASE, drivers=(),
                 acceptance=(), layout_acceptance=(), engine=True,
                 engines=(), sealed=(), sealed_history=None, sources=(),
                 pinned=None, pin_file=None, pin_history=None, tree=None,
                 home=a.HERE, require_seed=True, ledger=None, cells=None,
                 family=None, replaces=None, root=None,
                 allocation="exact allocation is the separate gate of "
                 "allocation_matrix.py; not part of this timing gate"):
        extra = seconds_by_case or {}
        a.require(len(set(cases)) == len(cases) and
                  all(c in ms.EXPECTED_CASES for c in cases),
                  "unknown or duplicate matrix case")
        every = ["%s-%d" % (case, size) for case in cases for size in
                 ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]]]
        a.require(cells is None or (
            cells and len(set(cells)) == len(cells) and
            set(cells) <= set(every)), "unknown or duplicate cell")
        a.require(family is None or re.fullmatch(
            r"[A-Za-z0-9_-]{1,40}", family) is not None, "invalid family")
        a.require(set(extra) <= set(cases) and all(
            0.1 <= v <= 60 for v in [seconds, *extra.values()]),
            "invalid batch seconds")
        pins = pinned or {}
        earlier = pin_history or {}
        a.require(pin_file is not None or not earlier,
                  "a pin history belongs to a table with a pin file")
        for found in [pins, *earlier.values()]:
            a.require(set(found) <= set(sources), "pin outside the sources")
            a.require(all(
                isinstance(v, dict) and sorted(v) == ["blob", "reason"] and
                isinstance(v["blob"], str) and len(v["blob"]) == 40 and
                isinstance(v["reason"], str) and v["reason"].strip()
                for v in found.values()), "malformed pin")
        history = sealed_history or {}
        a.require(set(history) <= set(sealed), "history of an unsealed file")
        a.require(seed is None or fixed_seconds, "a seed belongs to a "
                  "table with fixed seconds")
        a.require(seed is not None or not (fixed_seconds and require_seed),
                  "a table with fixed seconds names its layout seed")
        if seed is not None:
            layout_seed(seed)
            layout_seed(seed + "-ext")
        a.require(fixed_seconds or not revisions, "counts revisions belong "
                  "to a table with fixed seconds")
        a.require(schedule in ("ramp", "warmup"), "unknown schedule")
        a.require(schedule == "ramp" or fixed_seconds, "the warmup "
                  "schedule needs fixed seconds (its counts follow each "
                  "cell's predeclared seconds): set fixed_seconds=True, "
                  "or name schedule=\"ramp\"")
        headroom = (2 if schedule == "ramp" else 1) \
            if headroom is None else headroom
        names = [Path(p).name for p in (counts, *revisions)]
        a.require(len(set(names)) == len(names), "repeated counts file")
        if replaces is not None:
            self.check_replaces(
                replaces, cells, cases, fixed_seconds, baseline, seed,
                pairs, target, max_pairs, seconds, extra,
                name if family is None else family,
                None if ledger is None else Path(ledger))
        self.name, self.label, self.cases = name, label, tuple(cases)
        self.cells = None if cells is None else tuple(cells)
        self.family = name if family is None else family
        self.replaces = replaces
        self.root = Path(a.HERE.parents[3] if root is None else root)
        self.driver, self.counts = Path(driver), Path(counts)
        self.seconds, self.seconds_by_case = seconds, dict(extra)
        self.fixed_seconds = fixed_seconds
        self.pairs, self.samples, self.headroom = pairs, samples, headroom
        self.schedule = schedule
        self.seed, self.revisions = seed, tuple(map(Path, revisions))
        self.tree = tree
        self.pilot_pairs, self.pilot_samples = pilot_pairs, pilot_samples
        self.target, self.max_pairs = target, max_pairs
        self.baseline = baseline
        self.drivers, self.acceptance = tuple(drivers), tuple(acceptance)
        self.layout_acceptance = tuple(layout_acceptance)
        self.engine, self.engines = engine, tuple(engines)
        self.sealed = tuple(sealed)
        self.sealed_history = {k: tuple(v) for k, v in history.items()}
        self.sources, self.require_seed = tuple(sources), require_seed
        self.pinned = {k: dict(v) for k, v in pins.items()}
        self.pin_file = pin_file
        self.pin_history = {k: {p: dict(v) for p, v in found.items()}
                            for k, found in earlier.items()}
        self.home = Path(home)
        self.ledger = None if ledger is None else Path(ledger)
        self.allocation = allocation

    def check_replaces(self, replaces, cells, cases, fixed_seconds, baseline,
                       seed, pairs, target, max_pairs, seconds, extra,
                       family=None, ledger=None):
        """A follow-up measures what the table it replaces measured, under
        the same conditions, with a layout it has not drawn before."""
        a.require(isinstance(replaces, Replaces), "malformed replaces")
        old = replaces.table
        a.require(cells is not None and fixed_seconds,
                  "a follow-up names its cells and has fixed seconds")
        a.require(set(cells) <= set(old.names()) and
                  set(cases) <= set(old.cases),
                  "a follow-up measures cells of the table it replaces")
        a.require(baseline == old.baseline,
                  "a follow-up has the baseline of the table it replaces")
        a.require((target, max_pairs) == (old.target, old.max_pairs),
                  "a follow-up has the limits of the table it replaces")
        a.require(pairs == 2 * old.pairs, "a follow-up has twice the pairs "
                  "of the table it replaces")
        a.require(all(extra.get(c, seconds) == old.seconds_for(c)
                      for c in cases), "a follow-up has the batch seconds "
                  "of the table it replaces")
        a.require(family == old.family, "a follow-up keeps its evidence in "
                  "the family of the table it replaces (%s), not %s: it "
                  "extends the one chain of the family"
                  % (old.family, family))
        a.require(ledger == old.ledger, "a follow-up has the ledger of the "
                  "table it replaces (%s), not %s: it extends the one chain "
                  "of the family" % (old.ledger, ledger))
        taken = {old.seed, None if old.seed is None else old.seed + "-ext"}
        a.require(seed is not None and not {seed, seed + "-ext"} & taken,
                  "a follow-up draws its layout with a seed of its own: "
                  "the replaced table's seed and its -ext are taken")

    def every(self):
        """Every cell of the cases, in order, whether the table measures it
        or not."""
        return [(case, size) for case in self.cases for size in
                ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]]]

    def keys(self):
        return [k for k in self.every()
                if self.cells is None or "%s-%d" % k in self.cells]

    def names(self):
        return ["%s-%d" % k for k in self.keys()]

    def seconds_for(self, case):
        return self.seconds_by_case.get(case, self.seconds)

    def files(self):
        """Every counts file of the table, the first one first."""
        return (self.counts,) + self.revisions

    def latest(self):
        return self.files()[-1]

    def file_named(self, name):
        for path in self.files():
            if path.name == name:
                return path
        raise ValueError("unknown counts file: %r" % (name,))

    def seconds_map(self):
        """The per-cell seconds a counts file records, if it records any."""
        return ({"%s-%d" % k: self.seconds_for(k[0]) for k in self.keys()}
                if self.fixed_seconds else {})

    def code(self):
        """Header fields naming the code of a run."""
        return (("driver", "engine", "acceptance") if self.engine else
                ("driver", "acceptance")) + (
                    ("sealed",) if self.sealed else ()) + (
                    ("pins",) if self.pin_file else ())

    def schema(self, kind):
        return "%s-%s-v1" % (self.name, kind)


def checkpoint(path, value):
    """Rewrite the inventory after every cell; a crash keeps finished rows."""
    partial = path.with_name(path.name + ".partial")
    partial.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    partial.replace(path)


def canonical(value):
    """Compare as stored. Analyses key rows by integer pair, an archived
    report by string; with more than ten pairs sort_keys orders them
    differently ("10" < "2")."""
    return json.dumps(json.loads(json.dumps(value, allow_nan=False)),
                      sort_keys=True)


def unused(path):
    """`path`, or the first of `<stem>-N<suffix>` that does not exist."""
    number, found = 1, path
    while found.exists():
        found = path.with_name("%s-%d%s" % (path.stem, number, path.suffix))
        number += 1
    return found


def set_aside(path, kind):
    """Keep a file that is not evidence of its cell under another name
    (`<name>.<kind>-N`), so the cell can be measured again."""
    number = 1
    while True:
        target = path.with_name("%s.%s-%d" % (path.name, kind, number))
        if not target.exists():
            path.rename(target)
            return target
        number += 1


def git_blob(repo, rev, path):
    """Git blob of `path` at commit `rev`, or None when it has no such
    file."""
    try:
        found = subprocess.run(
            ["git", "-C", str(repo), "ls-tree", rev, "--", path], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    except subprocess.CalledProcessError:
        raise ValueError("unknown revision: " + rev) from None
    fields = found.stdout.split()
    return fields[2] if len(fields) >= 3 and fields[1] == "blob" else None


def git_commits(repo, rev, path):
    """The commits in the history of `rev` that changed `path`. The default
    history simplification follows one parent of a merge and hides a commit
    on the other side, so the whole history is walked; a merge is listed
    only when it changed the file itself (`--simplify-merges`)."""
    return a.git(repo, "log", "--format=%H", "--full-history",
                 "--simplify-merges", rev, "--", path).split()


def git_introduced(repo, rev, path):
    """The one commit that changed `path` in the history of `rev`. A file
    that was committed and then committed again is refused: only a file
    with a single commit was fixed at a point that git alone dates."""
    commits = git_commits(repo, rev, path)
    a.require(len(commits) == 1, "%s must be changed by exactly one commit "
              "in the candidate's history, not %d" % (path, len(commits)))
    a.require(git_blob(repo, commits[0], path) == git_blob(repo, rev, path),
              "no commit introduces " + path)
    return commits[0]


def git_difference(repo, baseline, candidate, tree):
    """Every file below `tree` that differs between two commits, as sorted
    [status, path] pairs (no rename detection, so each is one file)."""
    found = a.git(repo, "diff", "--name-status", "--no-renames", "-z",
                  baseline, candidate, "--", tree).split("\0")
    if found[-1] == "":
        found.pop()
    a.require(len(found) % 2 == 0, "unreadable name-status list")
    return sorted([found[i], found[i + 1]] for i in range(0, len(found), 2))


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ")


LEDGER_START = "0" * 64


def ledger_hash(text):
    return hashlib.sha256(text.encode()).hexdigest()


def ledger_record(text):
    """The line as a ledger record, or None when it is not one."""
    try:
        record = json.loads(text)
    except ValueError:
        return None
    return record if isinstance(record, dict) and "event" in record \
        else None


class Ledger:
    """What an attempts ledger holds: its records in order, the hash the
    next line must name, and the notes about its tail.

    Each line is one JSON object, and `prev` of a line is the SHA-256 of the
    line before it (64 zeros for the first), so that a line removed or
    changed in the middle breaks the chain. The end of the file may be cut
    short by a crash, or by a crash while the next append was acknowledging
    the first: any run of lines at the end that are no record, the last of
    them perhaps unterminated, is reported, left in the file and
    acknowledged together by the next append with one `torn` record naming
    their hashes. A line that is no record and is followed by a record that
    does not acknowledge it, or by a different run, is refused. The chain is
    a discipline and not a proof: it cannot show that lines after the last
    one, or the whole file, were removed.

    A line of an attempt names its table (`table`), since the tables of a
    family share one ledger. A line without the field, as every line written
    before the field existed, is of the table that names the family (the hash
    of a line is that of its text, so the lines already written verify as
    they were)."""

    def __init__(self, path):
        self.records, self.notes = [], []
        self.last, self.torn = LEDGER_START, []
        text = Path(path).read_text() if Path(path).exists() else ""
        lines = text.split("\n")
        tail = lines.pop()
        self.unterminated = tail != ""
        if self.unterminated:
            lines.append(tail)
        skipped, first = [], 0
        for number, line in enumerate(lines, 1):
            record = ledger_record(line)
            if record is None:
                first = first or number
                skipped.append(line)
                continue
            if skipped:
                a.require(record["event"] == "torn" and record.get(
                    "skipped") == [ledger_hash(x) for x in skipped],
                    "malformed attempts ledger: %s line %d" % (path, first))
                skipped, first = [], 0
            a.require(record.get("prev") == self.last,
                      "attempts ledger chain broken at line %d: %s"
                      % (number, path))
            self.records.append(record)
            self.last = ledger_hash(line)
            if number == len(lines) and self.unterminated:
                self.notes.append("LEDGER-UNTERMINATED-LAST-LINE %d: kept, "
                                  "it is a complete record" % number)
        self.torn = skipped
        for number, line in enumerate(skipped, len(lines) - len(skipped) + 1):
            self.notes.append("LEDGER-TORN-LINE %d: %d bytes of an "
                              "unfinished write, ignored"
                              % (number, len(line.encode())))

    def attempts(self, table=None, default=None):
        """With `table`, only the lines that name it (`table` of a line;
        a line without one, as every line written before lines named their
        table, is of `default`). (attempt, stage) -> candidate, the
        checkouts of all its lines (`checkout`: the first), opened,
        resumptions, and every status the attempt closed with, in order
        (`statuses`; `status`: the last), in the order the ledger first
        names them. A run that was resumed or is still open without a close
        of its own has been `interrupted`. The texts of the closes that
        carry a `found` (a difference found and not marked) or a `judgement`
        (an end that could not be judged) are in the lists of those names."""
        found = {}
        for record in self.records:
            if record["event"] not in ("open", "resume", "close"):
                continue
            if table is not None and record.get("table", default) != table:
                continue
            row = found.setdefault(
                (record["attempt"], record["stage"]),
                dict(candidate=record.get("candidate"), checkout=None,
                     checkouts=[], opened=None, resumed=0, statuses=[],
                     status=None, found=[], judgement=[], running=False))
            place = record.get("checkout")
            if place not in row["checkouts"]:
                row["checkouts"].append(place)
            if record["event"] != "close":
                if row["running"]:
                    row["statuses"].append("interrupted")
                row["running"] = True
            if record["event"] == "open":
                row["opened"] = record["time"]
            elif record["event"] == "resume":
                row["resumed"] += 1
            else:
                row["statuses"].append(record["status"])
                for key in ("found", "judgement"):
                    if key in record:
                        row[key].append(record[key])
                row["running"] = False
        for row in found.values():
            if row.pop("running"):
                row["statuses"].append("interrupted")
            row["checkout"] = row["checkouts"][0]
            row["status"] = row["statuses"][-1] if row["statuses"] else None
        return found


def sync_directory(path):
    """Make the entries of a directory durable (a file just created in it
    is not, until then)."""
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def ledger_append(path, **record):
    """Append one record, naming the line before it. The file is only ever
    appended to, and the line is on disk before the caller goes on. After
    lines cut short by a crash the append first ends the last of them and
    acknowledges them all, so that none is lost or repeated. A file the
    append creates is made durable in its directory too."""
    state, created = Ledger(path), not Path(path).exists()
    prefix, prev = "\n" if state.unterminated else "", state.last
    if state.torn:
        acknowledgement = json.dumps(
            dict(event="torn", prev=prev, time=utc_now(),
                 skipped=[ledger_hash(x) for x in state.torn]),
            sort_keys=True, allow_nan=False)
        prefix += acknowledgement + "\n"
        prev = ledger_hash(acknowledgement)
    line = json.dumps(dict(record, prev=prev, time=utc_now()),
                      sort_keys=True, allow_nan=False)
    with Path(path).open("a") as stream:
        stream.write(prefix + line + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    if created:
        sync_directory(Path(path).parent)


def git_keep(repo, table, commit):
    """A local ref that keeps a measured commit, and so the counts commit
    in its history, from a later rebase and garbage collection. It is
    `git update-ref` in the shared git directory, for this ref and for
    nothing else."""
    ref = "refs/performance/%s/%s" % (table, commit)
    a.git(repo, "update-ref", ref, commit)
    return ref


# What `prepare` runs, in the repository root: configure, which makes
# bin/hol, bin/Holmake and bin/build and writes the checkout's HOLDIR (the
# `poly` on the PATH reads the file), and then the real build, up to the
# parallel builds, which Holmake judges (it rebuilds what is out of date and
# leaves the rest), with the standard kernel.
CONFIGURE = ("poly",)
CONFIGURE_INPUT = "tools/smart-configure.sml"
BUILD = ("bin/build", "--stdknl", "--seq=tools/sequences/upto-parallel")
# The warning bin/build prints, and then waits on its standard input, when
# one of those executables is older than a source of it
# (tools/build/buildutils.sml, check_against); configure just before makes
# it unreachable, and it is asserted all the same.
STALE = "WARNING! WARNING!"
# The last line configure prints, once it has done everything. The real
# script runs under a handler that swallows an exception and lets poly
# exit 0, so the exit status alone does not say that it finished.
FINISHED = "Finished configuration!"
# The products a measurement loads from the checkout besides the sources the
# harness takes per side from git (the simplifier's, below src/simp/src): the
# executable, the heap, the Holmake that compiles the fixtures, everything the
# heap's libraries load from sigobj, and the theory data files and the
# theory sources below src/**/.hol/objs. The Poly/ML runtime and libraries are
# not here: each cell's manifest records them among its tools.
PRODUCTS = ("bin/hol", "bin/hol.state0", "bin/Holmake")
PREPARE = "run prepare at this commit"
# What is safe when a grid whose record has begun is refused, at a resumption
# or at a second stage: a prepare gives new products, so it cannot be the way
# back, and it ends the grid; a commit moves HEAD, and the way back is to the
# recorded commit.
RESUMING = ("this grid goes on only at the recorded commit, tree and "
            "products; remove the change, or restore the stamp from a copy "
            "of that same file; a prepare ends the grid, and a later commit "
            "must be left: go back to the recorded commit")
# A build from nothing takes the better part of an hour.
BUILD_TIMEOUT = 4 * 3600
# The exit status of a command that was refused or ended with an error, and
# so decided nothing; 0, 1 and 2 are those of a grid (`status_code`).
REFUSED = 3


@contextlib.contextmanager
def terminating_as_interrupt():
    """SIGTERM and SIGHUP (a plain `kill`, a `timeout`, an agent's stop, a
    closed terminal) raise `KeyboardInterrupt`, as SIGINT does, so that
    they take the path of an interrupt: the cell's process group is killed,
    the lock is released and the end of the attempt is judged. A signal
    that is ignored at the start (SIGHUP under `nohup`) stays ignored, as
    Python leaves an ignored SIGINT. What was replaced is restored at the
    exit. The cell's group is killed, but
    a process that `run_paired` started has a session of its own, runs to
    its end holding the lock, and may have to be killed by hand: the lock
    staying is deliberate (see `acceptance.serial_lock`). Off the main
    thread, where Python allows no handler, nothing changes."""
    old = {}
    try:
        for number in (signal.SIGTERM, signal.SIGHUP):
            if signal.getsignal(number) != signal.SIG_IGN:
                old[number] = signal.signal(number,
                                            signal.default_int_handler)
    except ValueError:
        pass
    try:
        yield
    finally:
        for number, handler in old.items():
            if handler is not None:
                signal.signal(number, handler)


def file_sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def products_digest(repo):
    """The content of the shared products a measurement loads: `PRODUCTS`,
    every file below sigobj (symlinks followed), and the theory data files
    and theory sources below src/**/.hol/objs, as the sha256 of their sorted
    names and content seals. Times play no part. A product, or a link's
    target, outside the repository is refused: the stamp binds this
    checkout's products only."""
    repo = Path(repo)
    found = {name: repo / name for name in PRODUCTS}
    top = repo / "sigobj"
    a.require(top.is_dir(), "no sigobj to measure with: " + str(top))
    seen = set()
    for folder, dirs, files in os.walk(top, followlinks=True):
        if os.path.realpath(folder) in seen:
            dirs.clear()
            continue
        seen.add(os.path.realpath(folder))
        for name in files:
            path = Path(folder) / name
            found[path.relative_to(repo).as_posix()] = path
    for suffix in ("dat", "sml"):
        for path in sorted((repo / "src").glob("**/.hol/objs/*." + suffix)):
            found[path.relative_to(repo).as_posix()] = path
    inside = Path(os.path.realpath(repo))
    digest = hashlib.sha256()
    for name in sorted(found):
        a.require(Path(os.path.realpath(found[name])).is_relative_to(inside),
                  "a product resolves outside the repository: %s (to %s)"
                  % (found[name], os.path.realpath(found[name])))
        a.require(found[name].is_file(), "no product to measure with: "
                  + str(found[name]))
        digest.update(("%s\0%s\n" % (name, file_sha256(found[name]))).encode())
    return dict(sha256=digest.hexdigest(), files=len(found))


def clean_head(repo):
    """HEAD and the seal of its tree outside the performance area, in a
    checkout whose tree is clean."""
    head = a.git(repo, "rev-parse", "HEAD")
    found = pr.harness_identity(repo, head)
    return dict(head=head,
                tree_outside_performance=found["tree_outside_performance"])


def build_stamp(repo):
    """What `prepare` records after a configure and a build that succeeded:
    HEAD, the seal of the tree outside the performance area, the content
    digest of the shared products and the build command."""
    return dict(clean_head(repo), products=products_digest(repo),
                build=list(BUILD))


def judge(ok, what, fresh=None):
    """`a.require` for what leaves the checkout unjudged, not different."""
    if not ok:
        raise CheckoutUnjudged(what, fresh)


def differs(ok, what, fresh=None):
    """`a.require` for what makes the checkout other than the one wanted."""
    if not ok:
        raise CheckoutRefused(what, fresh)


def tracked_changes(repo):
    """The status lines of the tracked files that differ from HEAD anywhere
    in the tree (every entry of `git status --porcelain` but an untracked
    file), beyond the agent-state directory."""
    listing = a.git(repo, "status", "--porcelain", "--untracked-files=all",
                    "--", ":(top)", ":(top,exclude)" + pr.AGENT_STATE)
    return [line for line in listing.splitlines()
            if line.strip() and not line.startswith("??")]


def known_difference(repo, recorded):
    """Why the checkout is known to differ from the record `recorded` (a
    grid's or a pilot's `checkout`) although `checkout_identity` could not
    judge it (the tree is not clean, or there is no usable stamp), or None
    when nothing is known. The head is judged first, by `checkout_identity`,
    which compares it with the commit before it looks at the tree. Here: the
    products digest, which needs neither a clean tree nor the stamp; then
    the tracked files. A change to any tracked file, a documentation file
    included, is a tree other than the recorded one. Only untracked files,
    or a missing stamp, say nothing."""
    try:
        products = products_digest(repo)["sha256"]
    except ValueError as error:
        return "the products are not the recorded ones: %s" % error
    if products != recorded["products"]:
        return ("the products (bin/hol, bin/hol.state0, bin/Holmake, "
                "sigobj, the theory data files and sources) are not the "
                "recorded ones: " + PREPARE)
    changed = tracked_changes(repo)
    if changed:
        return ("tracked file(s) changed, so the tree is not the recorded "
                "one: " + "; ".join(changed[:5])
                + (" ..." if len(changed) > 5 else ""))
    return None


def checkout_identity(repo, commit=None, stamp=None):
    """The checkout a measurement runs in: HEAD is the commit measured (HEAD
    itself when `commit` is None), the tree is clean, and the tree outside
    the performance area and the shared products are those `prepare` stamped
    (`stamp`, a file). It is the record of a grid: HEAD, the tree seal and
    the products digest. The simplifier's sources below src/simp/src are
    taken per side from git; the stamp binds the products named at
    `PRODUCTS` and `products_digest`: bin/hol, bin/hol.state0, bin/Holmake,
    sigobj, and the theory data files and sources. It does not bind the
    Poly/ML runtime and libraries, which each cell's manifest records among
    its tools.
    Holmake, not this module, judges whether a build is out of date: the
    comparison is of contents, so a commit that touches only the performance
    area, a checkout round trip to the same tree and a touched heap pass,
    while an edited product or a changed source outside the performance area
    is refused until `prepare` is run again. A checkout that is not clean,
    or a stamp that is missing or malformed or of another build command,
    cannot be judged here (`CheckoutUnjudged`, which `recheck` takes
    further with `known_difference`); a head, a tree or products that
    differ are judged. The stamp is a discipline and not a proof of
    provenance: it shows the products are those present when a configure
    and a build exited cleanly at this tree."""
    repo = Path(repo)
    head = a.git(repo, "rev-parse", "HEAD")
    differs(commit is None or head == commit,
            "the checkout is at %s, not at the commit measured (%s)"
            % (head, commit))
    try:
        found = clean_head(repo)
    except ValueError as error:
        # Its own words for a fresh start are kept, for a fresh start.
        text, fresh = str(error), "commit first"
        if text.endswith(": " + fresh):
            raise CheckoutUnjudged(text[:-len(fresh) - 2], fresh) from None
        raise CheckoutUnjudged(text) from None
    judge(stamp is not None and Path(stamp).is_file(),
          "no build stamp (%s)" % stamp, PREPARE)
    try:
        made = json.loads(Path(stamp).read_text())
    except ValueError:
        made = None
    judge(isinstance(made, dict) and sorted(made) == [
        "build", "head", "products", "tree_outside_performance"],
        "malformed build stamp %s" % stamp, PREPARE)
    judge(made["build"] == list(BUILD),
          "the build stamp is of another build command, %s" % made["build"],
          PREPARE)
    differs(made["tree_outside_performance"] ==
            found["tree_outside_performance"],
            "the tree outside the performance area is not the one the "
            "build was made from", PREPARE)
    products = products_digest(repo)
    differs(made["products"] == products,
            "the products (bin/hol, bin/hol.state0, bin/Holmake, sigobj, "
            "the theory data files and sources) differ from the stamped "
            "build", PREPARE)
    return dict(found, products=products["sha256"])


def configured_holdir(repo):
    """The HOLDIR that configure wrote into tools/Holmake/Systeml.sml, which
    every executable of the checkout (bin/hol, bin/Holmake, bin/build) and
    the build work from; it must be this repository. Configure has just
    written the HOLDIR of the directory it ran in, so this is an assertion
    about what it left."""
    repo = Path(repo)
    path = repo / "tools" / "Holmake" / "Systeml.sml"
    a.require(path.is_file(), "configure did not leave the checkout "
              "configured: no %s" % path)
    found = [m.group(1) for m in (
        re.match(r'val HOLDIR\s*=\s*"(.*)"\s*$', line)
        for line in path.read_text().splitlines()) if m]
    a.require(len(found) == 1, "configure did not leave a single HOLDIR "
              "in %s" % path)
    a.require(Path(found[0]).resolve() == repo.resolve(),
              "configure left the checkout configured for %s, not for %s "
              "(the build would work in, and link to, the other tree)"
              % (found[0], repo.resolve()))


def configure_finished(log):
    """Whether the log holds the line configure ends with."""
    text = Path(log).read_bytes().decode(errors="replace")
    return any(line.strip() == FINISHED for line in text.splitlines())


def stale_executable_warning(log):
    """Whether the log of a build holds the warning bin/build prints when
    bin/hol, bin/Holmake or bin/build is older than a source of it."""
    with Path(log).open(errors="replace") as stream:
        return any(STALE in line for line in stream)


def git_tree_outside(repo, rev):
    """The seal of the tree of `rev` outside the performance area."""
    return pr.tree_outside_performance(repo, rev)


def status_code(decisions):
    return {"pass": 0, "fail": 1}.get(decisions["status"], 2)


def open_metrics(row):
    """Metrics of a cell that are neither passed nor merely reported."""
    return [v for v in row["metrics"].values()
            if v["decision"] not in ("pass", "reported")]


def classify_row(row):
    """One cell: pass; fail; control_limited (every open metric is
    inconclusive only because its B/B control is outside the window);
    inconclusive; or protocol (no admitted measurement)."""
    if not row["protocol"]:
        return "protocol"
    open_ = open_metrics(row)
    if any(v["decision"] == "fail" for v in open_):
        return "fail"
    if not open_:
        return "pass"
    if all(v["reason"] == CONTROL for v in open_):
        return "control_limited"
    return "inconclusive"


def classify(decisions):
    """Every cell of a grid decision in exactly one class. The retained
    slope, when measured, is one more entry. Nothing is excused here."""
    cells = {k: [] for k in CLASSES}
    for row in decisions["workloads"]:
        cells[classify_row(row)].append("%s-%d" % (row["case"], row["size"]))
    scaling = decisions["retained_scaling"]
    if scaling is not None:
        if scaling["status"] != "measured":
            cells["inconclusive"].append("retained_scaling")
        else:
            found = {r["words_per_rule"]["decision"]
                     for r in scaling["adjacent_intervals"]
                     if r["selection"] == "candidate"}
            if "fail" in found:
                cells["fail"].append("retained_scaling")
            elif found != {"pass"}:
                cells["inconclusive"].append("retained_scaling")
    return cells


def class_report(label, decisions):
    """Printed outcome: the counts, then every cell that is not a pass and
    every source file that differs."""
    cells = classify(decisions)
    lines = ["%s grid: %s (%s)" % (label, decisions["status"], ", ".join(
        "%s %d" % (k.replace("_", "-"), len(cells[k])) for k in CLASSES))]
    for kind in CLASSES[1:]:
        lines += ["%s %s" % (kind.replace("_", "-").upper(), name)
                  for name in cells[kind]]
    lines += ["SOURCE-DIFFERS " + path for path in
              decisions.get("source_identity", {}).get("differing", [])]
    return lines


def control_half_width(result):
    """The larger half log-width of the develop/develop control intervals of
    the gated metrics of one cell (infinite when one has none): all the
    second-stage rule reads of a cell. Never the candidate's."""
    width = 0.0
    for m in a.EQUIVALENCE_POLICY["gated_timing"]:
        ci = result["control"]["metrics"][m][
            "paired_ratio_bootstrap_95_percent"]
        width = max(width, math.log(ci[1] / ci[0]) / 2
                    if ci and ci[0] > 0 else math.inf)
    return width


def second_stage_pairs(width, pairs, target, cap):
    """The pair count of the second-stage rule: `pairs` scaled to a control
    half width of `target`, rounded up to tens, between twice `pairs` and
    `cap`."""
    wanted = pairs * (width / target) ** 2
    if not math.isfinite(wanted):
        return cap
    return min(cap, max(2 * pairs, 10 * math.ceil(wanted / 10)))


class Hooks:
    """Steps a module overrides by name, the engine's own for the rest.

    A module that defines `STEPS` (names) with matching module-level
    functions is called for those steps at call time, so a patched or
    wrapped step is honored. The module itself carries the steps' defaults
    by delegating to its engine."""

    def __init__(self, module, engine):
        self.module, self.engine = module, engine

    def __getattr__(self, name):
        if name in self.module.STEPS:
            return getattr(self.module, name)
        return getattr(self.engine, name)


class Grid:
    """The engine for one table. Methods call each other through `h`."""

    def __init__(self, table, hooks=None, doc=None):
        self.t = table
        self.h = self if hooks is None else hooks
        self.doc = __doc__ if doc is None else doc
        # What a follow-up table binds (`bind_replaced`), and what the last
        # complete `replay` of this engine found, for the table that
        # replaces its grid.
        self.replaced = self.replayed = None

    # Cells and counts ------------------------------------------------

    def cell_seconds(self, inventory, name):
        """Calibration target of one cell: the predeclared one when the
        counts name it, else the inventory's."""
        return inventory["iterations"].get("seconds", {}).get(
            name, inventory["seconds"])

    def calibration_counts(self, folder, case, size):
        """Final calibration counts of the develop-only processes of one
        archived cell: the receipts of its `-control` experiment."""
        control = folder / ("%s-%d-control" % (case, size))
        counts = set()
        for path in sorted(control.glob("pair-*.json.gz")):
            receipt = a.load(path)
            if receipt["fixture"] != "performance":
                continue
            stages = receipt["measurements"]["workloads"][case]
            counts.add(stages["calibration"][-1]["iterations"])
        a.require(len(counts) >= 1, "no develop calibration counts")
        return counts

    def calibration_finals(self, folder, case, size):
        """(iterations, wall) of the final calibration batch of each
        develop-only process of one archived cell, sorted and without
        repeats: what the warmup count rule reads."""
        control = folder / ("%s-%d-control" % (case, size))
        finals = set()
        for path in sorted(control.glob("pair-*.json.gz")):
            receipt = a.load(path)
            if receipt["fixture"] != "performance":
                continue
            last = receipt["measurements"]["workloads"][case][
                "calibration"][-1]
            finals.add((last["iterations"], last["wall"]))
        a.require(len(finals) >= 1, "no develop calibration counts")
        return sorted(finals)

    def check_pilot_settings(self, inventory, seconds=None):
        """Counts follow the pilot's batch seconds; a pilot made with other
        seconds than the counts predeclare (the table's, or the file's own
        when it is derived again) says nothing about its cells. A table
        without fixed seconds takes the counts of a historical grid, which
        is no pilot."""
        t = self.t
        a.require(inventory["baseline"] == t.baseline,
                  "pilot of another baseline")
        if not t.fixed_seconds:
            return
        a.require(inventory["schema"] == t.schema("pilot"),
                  "pilot of another task")
        a.require("checkout_changed" not in inventory,
                  "the checkout changed while the pilot ran")
        a.require("checkout_unjudged" not in inventory,
                  "the checkout of the pilot could not be judged when it "
                  "ended (%s): resume it" % inventory.get("checkout_unjudged"))
        seconds = t.seconds_map() if seconds is None else seconds
        a.require(all(inventory["seconds_by_case"].get(
            case, inventory["seconds"]) == seconds.get("%s-%d" % (case, size))
            for case, size in t.keys()),
            "pilot batch seconds differ from the predeclared seconds")

    def table_settings(self):
        """What a table with fixed seconds predeclares besides the counts,
        as the counts file records it."""
        t = self.t
        return dict(layout_seed=t.seed, pairs=t.pairs, samples=t.samples,
                    headroom=t.headroom, seconds=t.seconds_map(),
                    target=t.target, max_pairs=t.max_pairs,
                    schedule=t.schedule)

    def file_settings(self, found):
        """The same as a counts file says them: a replay and the derivation
        of a file use these, so that a later change of the table does not
        make an earlier grid unreplayable. A key the file lacks is the
        table's, which then differs from what the file derives to, except
        `schedule`: a file without one is `ramp` (as every earlier file),
        never the table's."""
        settings = {k: found.get(k, v)
                    for k, v in self.table_settings().items()}
        settings["schedule"] = schedule_of(found)
        return settings

    def predeclare(self, grid, rederive=False, settings=None):
        """Per-cell counts from the develop-only (B/B) processes of a pilot
        or of a historical grid, before any candidate observation. A table
        with fixed seconds also predeclares the settings of its run: layout
        seed, pairs, samples, headroom, seconds and the limits of the second
        stage, which are the table's (`settings`, the file's own when it is
        derived again), and records the seals of the pilot and of the files
        the counts are bound to, so that the file can be derived again
        (`rederive`: the pilot's code need not be the current one then). It
        runs the pilot's analyses again on every archive."""
        t = self.t
        settings = self.table_settings() if settings is None else settings
        seed, pairs, samples = (settings[k] for k in (
            "layout_seed", "pairs", "samples"))
        headroom = settings["headroom"]
        schedule = settings.get("schedule", "ramp")
        a.require(schedule in ("ramp", "warmup"), "unknown schedule")
        inventory = a.load(grid / "inventory.json")
        self.h.check_pilot_settings(inventory, settings["seconds"] or None)
        if t.fixed_seconds:
            if not rederive:
                self.h.check_code(inventory, False)
            a.require(all(type(v) is int for v in (pairs, samples)) and
                      pairs >= 10 and samples >= 3,
                      "pairs and samples below the protocol minimum")
            a.require(seed is not None or not t.require_seed,
                      "%s needs layout randomization (a seed in its table)"
                      % t.label)
            if seed is not None:
                self.h.check_seed(seed)
        table, archives, found = {}, {}, {}
        with tempfile.TemporaryDirectory(
                prefix="%s-counts-" % t.name) as scratch:
            for row in inventory["runs"]:
                case, size = row["case"], row["size"]
                name = "%s-%d" % (case, size)
                a.require(name not in table, "repeated pilot cell: " + name)
                archive = a.safe_child(grid, row["archive"])
                a.require(a.seal(archive) == row["seal"], "changed archive")
                folder = Path(scratch) / row["archive"]
                a.require(bundle.unpack(archive, folder) == row["files"],
                          "changed archive file count")
                archives[name] = row["seal"]
                counts = self.h.calibration_counts(folder, case, size)
                if t.fixed_seconds:
                    found[name] = self.h.check_pilot_cell(
                        folder, inventory, row, counts,
                        settings["seconds"][name])
                if schedule == "warmup":
                    table[name] = warmup_count(
                        headroom, settings["seconds"][name],
                        self.h.calibration_finals(folder, case, size))
                else:
                    table[name] = batch_iterations(headroom * max(counts))
        a.require(set(table) == set(t.names()),
                  "incomplete predeclared counts")
        if t.fixed_seconds:
            a.require(canonical(a.load(grid / "variability.json")) ==
                      canonical(found), "changed pilot variability.json")
        result = dict(schema=t.schema("iterations"),
                      source=inventory["driver"],
                      baseline=inventory["baseline"], headroom=headroom,
                      rule=WARMUP_RULE if schedule == "warmup" else RAMP_RULE,
                      iterations=table)
        if schedule == "warmup":
            result["schedule"] = schedule
        if t.replaces is not None:
            result.update(self.h.replaced_counts(grid))
        if t.fixed_seconds:
            result.update(
                seconds=settings["seconds"], layout_seed=seed, pairs=pairs,
                samples=samples, target=settings["target"],
                max_pairs=settings["max_pairs"],
                sealed=inventory.get("sealed", {}),
                pilot=dict(inventory=a.seal(grid / "inventory.json"),
                           archives=archives))
        return result

    def check_pilot_cell(self, folder, inventory, row, counts, seconds=None):
        """One archived pilot cell is what its inventory says: both sides of
        every process are the baseline, the analysis gives again the
        variability that was recorded, and the calibration counts are those
        of the receipts. Returns the variability."""
        t = self.t
        case, size = row["case"], row["size"]
        seconds = t.seconds_for(case) if seconds is None else seconds
        control = folder / ("%s-%d-control" % (case, size))
        manifest = a.load(control / "manifest.json")
        a.require(all(manifest["selections"][side]["revision"] ==
                      inventory["baseline"]
                      for side in ("baseline", "candidate")),
                  "a pilot process is not the baseline")
        options = argparse.Namespace(
            baseline=inventory["baseline"], pairs=inventory["pairs"],
            samples=inventory["samples"], batch_seconds=seconds)
        variability = self.h.variability(
            self.h.check_pilot(control, options, case, size))
        a.require(row["counts"] == sorted(counts),
                  "changed pilot calibration counts")
        a.require(canonical(row["variability"]) == canonical(variability),
                  "changed pilot variability")
        return variability

    def previous_counts(self, seal):
        """The counts file of the table with this seal."""
        for path in self.t.files():
            if path.exists() and a.seal(path) == seal:
                return path
        raise ValueError("a counts revision of a file the table does not "
                         "name")

    def position(self, path):
        """Where the table lists a file of these bytes, or None."""
        for i, found in enumerate(self.t.files()):
            if found.exists() and a.seal(found) == a.seal(path):
                return i
        return None

    def rescaled(self, previous, cells):
        """The counts of a revision: those of the previous file, with the
        cells named multiplied by the factor, and the link to the file they
        come from."""
        found = a.load(previous)
        a.require(isinstance(cells, list) and cells and
                  all(isinstance(c, str) for c in cells) and
                  len(set(cells)) == len(cells) and
                  all(c in found["iterations"] for c in cells),
                  "a revision rescales cells of the previous counts")
        result = copy.deepcopy(found)
        schedule = schedule_of(found)
        for cell in cells:
            result["iterations"][cell] = batch_iterations(
                found["iterations"][cell] * REVISION_FACTOR, schedule)
        result["revises"] = dict(
            previous=a.seal(previous), cells=sorted(cells),
            factor=REVISION_FACTOR,
            reason=(WARMUP_REVISION_REASON if schedule == "warmup" else
                    REVISION_REASON))
        return result

    def repiloted(self, grid, previous, reason, settings=None,
                  rederive=False):
        """The counts of a revision that is a fresh pilot, for a change that
        alters what is measured (such as a fixture bug), with the stated
        reason and the link to the file it replaces. The pilot must be
        another than the one of that file."""
        a.require(isinstance(reason, str) and reason.strip(),
                  "a new pilot states its reason")
        result = self.h.predeclare(grid, rederive, settings)
        a.require(result["pilot"] != a.load(previous)["pilot"],
                  "a new pilot is another pilot than that of the file it "
                  "revises")
        result["revises"] = dict(previous=a.seal(previous), repilot=reason)
        return result

    def revision(self, grid, previous, cells=None, repilot=None):
        """A counts revision: the table's last counts file with the cells
        named rescaled (the file must be what its pilot made), or a new file
        from a fresh pilot with a stated reason."""
        a.require(self.t.fixed_seconds, "this table has no counts revisions")
        a.require(a.seal(previous) == a.seal(self.t.latest()),
                  "a revision follows the table's last counts file")
        a.require((cells is None) != (repilot is None),
                  "a revision rescales cells or states a new pilot")
        if repilot is not None:
            return self.repiloted(grid, previous, repilot)
        self.h.check_counts(grid, previous)
        return self.rescaled(previous, sorted(cells))

    def derive_counts(self, grid, path):
        """What the pilot, and the revisions the file names, make of it. A
        file the table lists after the first revises the one before it, by
        rescaling cells of it (the same pilot) or by a fresh pilot; the
        first, and a file of no table, is a first derivation unless it
        names a link."""
        found = a.load(path)
        link = found.get("revises")
        at = self.position(path)
        settings = self.file_settings(found) if self.t.fixed_seconds else None
        a.require(at != 0 or link is None, "the first counts file revises "
                  "no other")
        a.require(at in (0, None) or link is not None,
                  "a counts file after the first revises the file before it")
        if link is None:
            return self.h.predeclare(grid, True, settings)
        a.require(isinstance(link, dict) and
                  isinstance(link.get("previous"), dict),
                  "malformed counts revision")
        previous = self.h.previous_counts(link["previous"])
        a.require(at is None or at == self.position(previous) + 1,
                  "a counts file revises the file before it")
        if "repilot" in link:
            return self.repiloted(grid, previous, link["repilot"], settings,
                                  True)
        self.h.check_counts(grid, previous)
        return self.rescaled(previous, link.get("cells"))

    def check_counts(self, grid, path):
        """The counts file is what its pilot makes of it: derived again from
        the archives, whose analyses run again. A follow-up's pairs and its
        record of the replaced grid are those derived from that grid. The
        grid is recorded by its path from the follow-up pilot, compared
        exactly (it fails closed): the two stay siblings, as in the
        evidence layout."""
        if self.t.replaces is not None:
            want, got = self.h.replaced_counts(grid), a.load(path)
            seen = got.get("replaces")
            self.h.check_recorded_code(seen)
            same = {k: v for k, v in want["replaces"].items() if k != "code"}
            a.require(seen.get("grid") == want["replaces"]["grid"] or
                      "grid" not in seen,
                      "the counts record the replaced grid at %s from the "
                      "follow-up pilot, not %s: the pilot and the replaced "
                      "grid must stay siblings, as in the evidence layout"
                      % (seen.get("grid"), want["replaces"]["grid"]))
            a.require(got.get("pairs_by_cell") == want["pairs_by_cell"] and
                      {k: v for k, v in seen.items() if k != "code"} == same,
                      "the pairs or the replaced grid of the counts differ "
                      "from the derivation from the replaced grid")
        derived = self.h.derive_counts(Path(grid), path)
        if self.t.replaces is not None and "replaces" in derived:
            # `code` records what `predeclare` replayed with: it is not
            # derived again (the code may have changed since).
            derived["replaces"] = dict(
                derived["replaces"], code=seen["code"])
        a.require(canonical(a.load(path)) == canonical(derived),
                  "counts differ from their pilot")

    def verify_counts(self, args):
        """The counts file is what `predeclare` makes of its pilot."""
        t = self.t
        path = args.counts or t.latest()
        self.h.bind_from(args, counts=a.load(path) if t.replaces else None)
        self.h.check_counts(args.grid.resolve(), path)
        print("%s counts match their pilot" % t.label)
        return 0

    def check_seed(self, seed):
        """A layout seed, and the seed of its second stage, are valid."""
        layout_seed(seed)
        layout_seed(seed + "-ext")

    def locked(self, repo):
        """The host/repository lock for a batch, children inheriting it."""
        class Held:
            def __enter__(self):
                self.lock = a.serial_lock(repo)
                self.fds = self.lock.__enter__()
                self.old = os.environ.get("HOL4_PERF_LOCK_FDS")
                os.environ["HOL4_PERF_LOCK_FDS"] = ",".join(
                    map(str, self.fds))
                return self.fds

            def __exit__(self, *exc):
                if self.old is None:
                    del os.environ["HOL4_PERF_LOCK_FDS"]
                else:
                    os.environ["HOL4_PERF_LOCK_FDS"] = self.old
                return self.lock.__exit__(*exc)
        return Held()

    def code_now(self):
        """The seals of the code of this table as it stands."""
        t = self.t
        now = dict(driver=a.seal(t.driver), acceptance=a.seal(a.__file__))
        if t.engine:
            now["engine"] = a.seal(__file__)
        if t.sealed:
            now["sealed"] = {n: a.seal(t.home / n) for n in t.sealed}
        if t.pin_file:
            now["pins"] = a.seal(t.home / t.pin_file)
        return now

    def pins_for(self, code):
        """The pins an inventory (or a resumption) was judged by: the
        current ones, or those of an earlier version of the pin file that
        the table keeps."""
        t = self.t
        if not t.pin_file:
            return t.pinned
        seal = code.get("pins")
        if seal == a.seal(t.home / t.pin_file):
            return t.pinned
        a.require(isinstance(seal, dict) and
                  seal.get("sha256") in t.pin_history, "changed pins")
        return t.pin_history[seal["sha256"]]

    def pilot_inventory(self, args):
        t = self.t
        now = self.h.code_now()
        now.pop("pins", None)  # the pins are the candidate's, not the pilot's
        return dict(
            schema=t.schema("pilot"), baseline=args.baseline,
            seconds=t.seconds, seconds_by_case=t.seconds_by_case,
            pairs=args.pairs, samples=args.samples, outliers="none removed",
            runs=[], **now)

    def pilot(self, args):
        """Develop-only experiments (baseline in both slots) with free
        calibration, one per cell, archived losslessly. Their calibration
        counts, and nothing a candidate does, set the predeclared counts.
        The baseline-versus-baseline variability of each cell is published
        beside them in variability.json. The pilot has no candidate and is
        made in a checkout that is clean and was prepared at its tree
        (`prepare`), which the inventory names."""
        t = self.t
        a.require(args.pairs >= 10 and args.samples >= 3,
                  "pilot needs at least ten pairs and three samples")
        a.require(args.baseline == t.baseline,
                  "pilot baseline differs from the table's")
        root = args.output.resolve()
        inventory = self.h.pilot_inventory(args)
        self.h.attempts_file(args, True)  # the ledger place, while it is cheap
        self.h.check_output(args)
        if t.fixed_seconds:
            inventory["checkout"] = self.h.bind_checkout(
                args.repo, None, args.resume)
        done = {}
        with self.h.locked(args.repo) as fds:
            self.h.recheck(args.repo, None, inventory)
            if args.resume:
                a.require((root / "inventory.json").exists(),
                          "nothing to resume: %s has no inventory (a pilot "
                          "stopped before its first checkpoint); remove it "
                          "and start again" % root)
                old = a.load(root / "inventory.json")
                ignored = ("runs", "checkout_unjudged", "unjudged_ends")
                a.require({k: v for k, v in old.items()
                           if k not in ignored} ==
                          {k: v for k, v in inventory.items()
                           if k not in ignored},
                          "resume with different settings")
                for row in old["runs"]:
                    a.require(a.seal(a.safe_child(root, row["archive"])) ==
                              row["seal"], "changed archive")
                    done[row["case"], row["size"]] = row
                inventory["runs"] = old["runs"]
                if "unjudged_ends" in old:
                    # The mark is cleared by this resume; what it said stays.
                    inventory["unjudged_ends"] = list(old["unjudged_ends"])
            else:
                root.mkdir(parents=True, exist_ok=False)
            checkpoint(root / "inventory.json", inventory)
            try:
                if args.resume:
                    self.h.sweep(root, [row["archive"]
                                        for row in inventory["runs"]])
                for case, size in t.keys():
                    if (case, size) in done:
                        continue
                    ms.get_case(case, size)
                    self.h.pilot_cell(root, inventory, case, size, args, fds)
                # A pilot has no decisions that a missing mark would hold
                # back: an unjudged end is marked until a resume finds the
                # checkout as recorded, and listed for good (the resume
                # comparison ignores the list).
                self.h.judge_end(root, args.repo, None, inventory)
            except CheckoutChanged:
                raise
            except BaseException as stop:
                _, note = self.h.judge_end(root, args.repo, None, inventory,
                                           stop)
                # A pilot has no ledger to carry the note: what the judgement
                # could not write is kept in memory, for the checkpoint
                # below (if that fails too, its error shows).
                if "found" in note:
                    inventory["checkout_changed"] = note["found"]
                elif "judgement" in note:
                    inventory["checkout_unjudged"] = note["judgement"]
                    inventory["unjudged_ends"] = [
                        *inventory.get("unjudged_ends", []),
                        note["judgement"]]
                raise
            finally:
                checkpoint(root / "inventory.json", inventory)
                checkpoint(root / "variability.json", {
                    "%s-%d" % (r["case"], r["size"]): r["variability"]
                    for r in inventory["runs"]})
        return 0

    def pilot_cell(self, root, inventory, case, size, args, fds):
        name = "%s-%d" % (case, size)
        seconds = self.t.seconds_for(case)
        print("PILOT %s seconds=%s" % (name, seconds), flush=True)
        options = argparse.Namespace(
            repo=args.repo, baseline=args.baseline, pairs=args.pairs,
            samples=args.samples, batch_seconds=seconds,
            timeout=args.timeout)
        with tempfile.TemporaryDirectory(
                prefix="%s-pilot-" % self.t.name) as scratch:
            folder = Path(scratch) / name
            folder.mkdir()
            control = folder / (name + "-control")
            command = a.run_logged(
                a.matrix_command(options, case, size, args.baseline,
                                 control), folder / (name + "-control.log"),
                fds, None)
            archive = root / (name + ".json.xz")
            files = self.h.archive(folder, archive, scratch)
            try:
                a.require(command["exit"] == 0 and not command["timed_out"],
                          "pilot runner failed: " + name)
                found = self.h.check_pilot(control, options, case, size)
                counts = self.h.calibration_counts(folder, case, size)
            except BaseException:
                set_aside(archive, "failed")  # evidence, but of no cell
                raise
            inventory["runs"].append(dict(
                case=case, size=size, archive=archive.name,
                seal=a.seal(archive), files=files, counts=sorted(counts),
                variability=self.h.variability(found)))
            checkpoint(root / "inventory.json", inventory)
            print("END %s max_count=%d" % (name, max(counts)), flush=True)

    def check_pilot(self, control, options, case, size):
        return a.analyze(
            control, case=case, size=size, baseline=options.baseline,
            candidate=options.baseline, pairs=options.pairs,
            samples=options.samples, seconds=options.batch_seconds,
            policy=a.EQUIVALENCE_POLICY)

    def variability(self, analysis):
        """What a baseline-versus-baseline cell says about the host: the
        median and 95% interval of each metric's paired ratio, and for a
        gated metric whether the interval lies in the equivalence window."""
        found = {}
        for metric, value in analysis["metrics"].items():
            ci = value.get("paired_ratio_bootstrap_95_percent")
            found[metric] = dict(median=value.get("median_paired_ratio"),
                                 ci95=ci)
            margin = value.get("margin")
            if margin:
                found[metric]["in_window"] = bool(ci) and (
                    1 / (1 + margin) <= ci[0] and ci[1] <= 1 + margin)
        return found

    def sweep(self, root, kept):
        """Clear what a stopped run left in its output: an unfinished
        archive is no evidence, and a complete archive that no row names is
        set aside, so that its cell can be measured again."""
        for path in [*root.glob("*.partial"), *root.glob("*.partial.xz")]:
            path.unlink()
        for path in root.glob("*.json.xz"):
            if path.name not in kept:
                set_aside(path, "unrecorded")

    def archive(self, folder, archive, scratch):
        """Pack a cell and verify every original byte before the scratch
        tree goes: a replay defect must not lose unique observations. The
        archive appears under its name only when it is complete."""
        partial = archive.with_name(archive.name + ".partial.xz")
        files = bundle.pack(folder, partial)
        restored = Path(scratch) / "roundtrip"
        a.require(bundle.unpack(partial, restored) == files,
                  "transport count mismatch")
        for path in folder.rglob("*"):
            if path.is_file():
                a.require(a.seal(path) == a.seal(
                    restored / path.relative_to(folder)),
                    "transport changed original bytes")
        partial.replace(archive)
        return files

    # Decisions -------------------------------------------------------

    def check_report(self, folder, report, baseline, candidate, seconds,
                     case, size, iterations, pairs=None, samples=None,
                     layout_seed=None, schedule=None):
        """Recompute a report under the policy it recorded."""
        t = self.t
        pairs = t.pairs if pairs is None else pairs
        samples = t.samples if samples is None else samples
        if not report["success"]:
            a.require(report.get("failure") or report.get("blocked"),
                      "unexplained incomplete experiment")
            return
        policy = report["policy"]
        a.require(policy == a.EQUIVALENCE_POLICY,
                  "unexpected %s policy" % t.label)
        results = {}
        for selection in ("control", "candidate"):
            results[selection] = a.analyze(
                folder / ("%s-%d-%s" % (case, size, selection)),
                case=case, size=size, baseline=baseline,
                candidate=baseline if selection == "control" else candidate,
                pairs=pairs, samples=samples, seconds=seconds,
                iterations=iterations, policy=policy,
                layout_seed=layout_seed,
                **({} if schedule is None else dict(schedule=schedule)))
        for name, value in results["candidate"]["metrics"].items():
            a.apply_control(value, results["control"]["metrics"][name])
        a.require(canonical([results]) == canonical(report["workloads"]),
                  "changed point analysis")
        scaling = (a.retained_scaling([results])
                   if case == "storage_graph" else None)
        a.require(canonical(scaling) == canonical(report["retained_scaling"]),
                  "changed slope analysis")

    def summary(self, reports):
        t = self.t
        result = gate.summary(reports, t.keys(), t.label)
        exits = [row["exit"] for row in result["workloads"]]
        scaling = result["retained_scaling"]
        if scaling is not None and scaling["status"] == "measured":
            exits += [{"pass": 0, "fail": 1}.get(
                r["words_per_rule"]["decision"], 2)
                for r in scaling["adjacent_intervals"]
                if r["selection"] == "candidate"]
        elif scaling is not None:
            exits.append(2)
        result.update(
            schema=t.schema("grid"), policy=a.EQUIVALENCE_POLICY,
            status=("pass" if set(exits) == {0} else
                    "fail" if 1 in exits else "inconclusive"),
            allocation=t.allocation)
        return result

    def status_code(self, decisions):
        return status_code(decisions)

    def unpack_report(self, root, row, scratch):
        archive = a.safe_child(root, row["archive"])
        a.require(a.seal(archive) == row["seal"], "changed archive")
        folder = Path(scratch) / "unpacked"
        a.require(bundle.unpack(archive, folder) == row["files"],
                  "changed archive file count")
        report = a.load(folder / "acceptance.json")
        a.require(row["exit"] == a.report_exit_status(report) and
                  row["protocol"] == report["success"],
                  "changed experiment outcome")
        return folder, report

    def schedule_args(self, inventory):
        """The schedule of the counts of an inventory, as the trailing
        argument of `check_report` when it is not the historical one (a
        module that wraps that step keeps the signature its archives
        used)."""
        schedule = schedule_of(inventory["iterations"])
        return () if schedule == "ramp" else (schedule,)

    def replay_rows(self, root, inventory, only=None):
        """Recompute every archived cell of one inventory, or only the cells
        `only` (keys) names, each of which must be there."""
        t = self.t
        reports = {}
        for row in inventory["runs"]:
            key = row["case"], row["size"]
            name = "%s-%d" % key
            if only is not None and key not in only:
                continue
            a.require(key in t.keys() and key not in reports,
                      "wrong/duplicate case")
            a.require(row["iterations"] ==
                      inventory["iterations"]["iterations"][name],
                      "count differs from predeclaration")
            a.require(inventory["schema"] != t.schema("experiment") or
                      row.get("pairs", inventory["pairs"]) ==
                      self.cell_pairs(inventory["iterations"], key,
                                      inventory["pairs"]),
                      "pairs differ from predeclaration")
            with tempfile.TemporaryDirectory(
                    prefix="%s-replay-" % t.name) as scratch:
                folder, report = self.h.unpack_report(root, row, scratch)
                self.h.check_report(
                    folder, report, inventory["baseline"],
                    inventory["candidate"],
                    self.h.cell_seconds(inventory, name), *key,
                    row["iterations"],
                    row.get("pairs", inventory["pairs"]),
                    inventory["samples"], inventory.get("layout_seed"),
                    *self.schedule_args(inventory))
                reports[key] = report
            print("REPLAY %s %d" % key, flush=True)
        a.require(only is None or set(reports) == set(only),
                  "archives of cells missing from the grid")
        return reports

    def begin(self, root, inventory, resume):
        """A fresh output, or the same experiment after an infrastructure
        failure: identical settings, finished cells replayed and kept, an
        unrecorded cell measured again from scratch (`measure` clears what
        the stop left, under the lock). The code may differ only when
        check_header accepts both, as for the moved lock; each such change
        is recorded with the number of rows before it."""
        code = self.t.code()
        if not resume:
            root.mkdir(parents=True, exist_ok=False)
            return {}
        a.require((root / "inventory.json").exists(),
                  "nothing to resume: %s has no inventory (a run stopped "
                  "before its first checkpoint); remove it and start again"
                  % root)
        old = a.load(root / "inventory.json")
        a.require(not (root / "decisions.json").exists(),
                  "run already complete")
        self.h.check_header(old)
        ignored = ("runs", "resumed", "attempt") + code
        a.require({k: v for k, v in old.items() if k not in ignored} ==
                  {k: v for k, v in inventory.items() if k not in ignored},
                  "resume with different settings")
        resumed = old.get("resumed", [])
        now = {k: inventory[k] for k in code}
        if now != {k: (resumed[-1] if resumed else old)[k] for k in code}:
            resumed = resumed + [dict(now, after=len(old["runs"]))]
        inventory.update({k: old[k] for k in code})
        if "attempt" in old:
            inventory["attempt"] = old["attempt"]
        if resumed:
            inventory["resumed"] = resumed
        inventory["runs"] = old["runs"]
        return self.h.replay_rows(root, old)

    def measure(self, root, inventory, cells, args, reports):
        """Measure (case, size, pairs) cells in order; checkpoint every
        row. The lock is taken before the first checkpoint."""
        seed = inventory.get("layout_seed")
        counts = inventory["iterations"]["iterations"]
        with self.h.locked(args.repo) as fds:
            checkpoint(root / "inventory.json", inventory)
            try:
                if getattr(args, "resume", False):
                    self.h.sweep(root, [row["archive"]
                                        for row in inventory["runs"]])
                for case, size, pairs in cells:
                    if (case, size) in reports:
                        continue
                    ms.get_case(case, size)
                    name = "%s-%d" % (case, size)
                    count = counts[name]
                    seconds = self.h.cell_seconds(inventory, name)
                    print("START %s N=%d pairs=%d seconds=%s%s" % (
                        name, count, pairs, seconds, "" if schedule_of(
                            inventory["iterations"]) == "ramp" else
                        " schedule=warmup"), flush=True)
                    self.h.measure_cell(root, inventory, case, size, pairs,
                                        count, seconds, seed, args, reports,
                                        fds)
                self.h.judge_end(root, args.repo, inventory["candidate"],
                                 inventory)
            finally:
                checkpoint(root / "inventory.json", inventory)
        return reports

    def measure_cell(self, root, inventory, case, size, pairs, count,
                     seconds, seed, args, reports, fds):
        name = "%s-%d" % (case, size)
        schedule = schedule_of(inventory["iterations"])
        # A backstop: `run` and `extend` have refused a mismatch already.
        a.require(schedule == self.t.schedule, "the schedule of the counts "
                  "differs from the table's")
        with tempfile.TemporaryDirectory(
                prefix="%s-" % self.t.name) as scratch:
            folder = Path(scratch) / name
            options = argparse.Namespace(
                pairs=pairs, samples=inventory["samples"],
                batch_seconds=seconds, batch_iterations=count,
                timeout=args.timeout, baseline=inventory["baseline"],
                candidate=inventory["candidate"],
                authorize_measurements=True, case=[case], size=[size],
                output=folder, mode="isolated", repo=args.repo,
                build_manifest=None, layout_seed=seed,
                batch_schedule=None if schedule == "ramp" else schedule)
            report = a.run(options)
            archive = root / (name + ".json.xz")
            files = self.h.archive(folder, archive, scratch)
            reports[case, size] = report
            row = dict(case=case, size=size, iterations=count,
                       archive=archive.name, seal=a.seal(archive),
                       files=files, exit=a.report_exit_status(report),
                       protocol=report["success"])
            if pairs != inventory["pairs"]:
                row["pairs"] = pairs
            inventory["runs"].append(row)
            checkpoint(root / "inventory.json", inventory)
            self.h.check_report(folder, report, inventory["baseline"],
                                inventory["candidate"], seconds, case, size,
                                count, pairs, inventory["samples"], seed,
                                *self.schedule_args(inventory))
            print("END %s exit=%d protocol=%s" % (
                name, a.report_exit_status(report), report["success"]),
                flush=True)

    def settings(self, args, counts):
        """(pairs, samples, layout seed) of a run. A table with fixed
        seconds has them as fields, the counts file records them, and a run
        refuses a file or an explicit value that differs; another keeps the
        command line's."""
        t = self.t
        if not t.fixed_seconds:
            return (t.pairs if args.pairs is None else args.pairs,
                    t.samples if args.samples is None else args.samples,
                    args.layout_seed)
        for key, own in (("pairs", t.pairs), ("samples", t.samples),
                         ("layout_seed", t.seed)):
            given = getattr(args, key)
            a.require(given is None or given == own,
                      "--%s differs from the predeclared counts"
                      % key.replace("_", "-"))
            a.require(counts[key] == own, "the %s of the counts differs "
                      "from the table's" % key.replace("_", " "))
        for key, own in (("headroom", t.headroom), ("target", t.target),
                         ("max_pairs", t.max_pairs)):
            a.require(counts.get(key) == own, "the %s of the counts differs "
                      "from the table's" % key.replace("_", " "))
        return t.pairs, t.samples, t.seed

    def repo_path(self, repo, path):
        """`path` as the repository names it."""
        try:
            return Path(path).resolve().relative_to(
                Path(repo).resolve()).as_posix()
        except ValueError:
            raise ValueError("%s is outside the repository" % path) from None

    def counts_commit(self, repo, candidate, path):
        """The commit that introduced the counts file: the file in use is,
        byte for byte, what the candidate's history holds, and exactly one
        commit of that history touched it. That commit is no later than the
        candidate; it does not date the file against any observation."""
        name = self.repo_path(repo, path)
        a.require(git_blob(repo, candidate, name) ==
                  a.git(repo, "hash-object", str(path)),
                  "the counts file is not committed in the candidate's "
                  "history: " + name)
        return git_introduced(repo, candidate, name)

    def counts_for(self, inventory):
        """The counts file of the table that an inventory names (a table
        without fixed seconds has the one)."""
        if not self.t.fixed_seconds:
            return self.t.counts
        a.require("counts_file" in inventory, "no counts file named")
        return self.t.file_named(inventory["counts_file"])

    def check_commit(self, inventory, repo=None):
        """The recorded commit and seal of the counts file are what git and
        the file say now."""
        t = self.t
        if not t.fixed_seconds:
            return
        repo = a.HERE.parents[3] if repo is None else repo
        path = self.h.counts_for(inventory)
        a.require(inventory.get("counts_commit") == self.h.counts_commit(
            repo, inventory["candidate"], path), "changed counts commit")
        a.require(inventory.get("iterations_seal") == a.seal(path),
                  "changed counts seal")

    def source_record(self, repo, baseline, candidate):
        """The git blob of each source file of the table at the baseline
        and at the candidate. A file the baseline lacks is recorded with no
        baseline blob, and only when the table pins it."""
        record = {}
        for path in self.t.sources:
            base = git_blob(repo, baseline, path)
            found = git_blob(repo, candidate, path)
            a.require(base is not None or path in self.t.pinned,
                      "source file absent at the baseline and not pinned: "
                      + path)
            a.require(base is not None or found is not None,
                      "source file absent at both commits: " + path)
            record[path] = dict(baseline=base, candidate=found)
        return record

    def source_tree(self, repo, baseline, candidate):
        """Every difference below the table's tree, so that the whole of it
        is published, not only the part the sources cover."""
        return dict(tree=self.t.tree, changes=git_difference(
            repo, baseline, candidate, self.t.tree))

    def check_sources(self, inventory, repo=None):
        """The recorded source identity is what git says it is."""
        t = self.t
        if not t.sources and not t.tree:
            return
        repo = a.HERE.parents[3] if repo is None else repo
        base, cand = inventory["baseline"], inventory["candidate"]
        if t.sources:
            a.require(inventory.get("sources") == self.h.source_record(
                repo, base, cand), "changed source identity")
        if t.tree:
            a.require(inventory.get("source_tree") == self.h.source_tree(
                repo, base, cand), "changed source difference")

    def source_identity(self, record, pins=None):
        """The files of the record, those that differ from the baseline
        and are not a reviewed pinned revision, and (for a table with
        pins) the reviewed ones with their reasons. A pin on a file the
        candidate leaves as the baseline has it is an error. Only the
        candidate blob a pin names is accepted: any other revision of the
        file differs as it would without a pin. `pins` are those the grid
        was judged by (the table's now, when none are given)."""
        pins = self.t.pinned if pins is None else pins
        for path in pins:
            a.require(record[path]["baseline"] != record[path]["candidate"],
                      "pinned source identical to the baseline: " + path)
        accepted = sorted(
            p for p in pins if record[p]["candidate"] == pins[p]["blob"])
        identity = dict(files=sorted(record), differing=sorted(
            p for p, r in record.items() if r["baseline"] != r["candidate"]
            and p not in accepted))
        if pins:
            identity["reviewed"] = {p: dict(pins[p]) for p in accepted}
        return identity

    def with_sources(self, decisions, inventory):
        """A source file that differs between the baseline and the candidate
        is named in the decisions, and no grid with one passes: the cost of
        a scan that allocates nothing is invisible to every other gate. A
        reviewed difference (a table's pin) is published beside them with
        its reason and does not affect the status."""
        if "sources" not in inventory:
            return decisions
        decisions["source_identity"] = self.h.source_identity(
            inventory["sources"], self.h.pins_for(inventory))
        if decisions["source_identity"]["differing"] and \
                decisions["status"] == "pass":
            decisions["status"] = "inconclusive"
        return decisions

    # Attempts -------------------------------------------------------------

    def ledger_path(self, repo):
        """The one attempts ledger of the table in a checkout: below its
        root, in the agent-state directory that git excludes, where this
        project keeps evidence. A grid and its retries stay in the one
        checkout, so the ledger is that checkout's."""
        t = self.t
        if t.ledger is not None:
            return t.ledger
        return (Path(repo).resolve() / ".agent-files" / "evidence" /
                t.family / "attempts.jsonl")

    def stamp_path(self, repo):
        """The build stamp of `prepare`, beside the ledger. The tables of a
        family share the directory, so each keeps its own stamp and log: the
        table that names the family (`name` is `family`) keeps the names it
        always had, another adds its name (`build-stamp-NAME.json`)."""
        t = self.t
        return self.h.ledger_path(repo).with_name(
            "build-stamp.json" if t.name == t.family
            else "build-stamp-%s.json" % t.name)

    def prepare_log_path(self, repo):
        """The log of `prepare`, beside the stamp and by the same rule."""
        t = self.t
        return self.h.ledger_path(repo).with_name(
            "prepare.log" if t.name == t.family
            else "prepare-%s.log" % t.name)

    def attempts_file(self, args, appending):
        """The attempts ledger of a table with fixed seconds, or None. A
        measurement appends to the ledger of its own checkout (`pilot` and
        `prepare` only check its place); below the checkout it must be
        ignored by git, so that no commit can hold or rewrite it. A replay
        or a close in another checkout may name the file read-only
        (`args.ledger`)."""
        t = self.t
        if not t.fixed_seconds:
            return None
        given = getattr(args, "ledger", None)
        if given is not None:
            a.require(not appending, "a measurement appends to the ledger "
                      "of its own checkout, not to another")
            return Path(given)
        path = self.h.ledger_path(args.repo)
        if appending:
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.resolve().is_relative_to(Path(args.repo).resolve()):
                found = subprocess.run(
                    ["git", "-C", str(args.repo), "check-ignore", "-q",
                     str(path)], stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL)
                a.require(found.returncode == 0, "the attempts ledger would "
                          "be tracked by git: exclude .agent-files first, "
                          "in the file `git rev-parse --git-path "
                          "info/exclude` names: %s" % path)
            if path.exists():
                Ledger(path)
        return path

    def check_output(self, args):
        """A table with fixed seconds needs a clean checkout at the end of
        a measurement, so an output inside the repository must be ignored by
        git; one that is not would be found out only at the end, after the
        measuring."""
        if not self.t.fixed_seconds:
            return
        root = args.output.resolve()
        if root.is_relative_to(Path(args.repo).resolve()):
            found = subprocess.run(
                ["git", "-C", str(args.repo), "check-ignore", "-q",
                 str(root / "inventory.json")], stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL)
            a.require(found.returncode == 0, "the output %s is inside the "
                      "repository and not ignored by git, so the checkout "
                      "would not be clean when the measuring is over: "
                      "put it below %s" % (root, Path(
                          self.h.ledger_path(args.repo)).parent))

    def record_attempt(self, path, event, stage, inventory, root, repo,
                       **more):
        """One line of the ledger about a grid of `stage` ("first" or
        "second"): its opening, a resumption, or its close with a status,
        with the checkout it was made in."""
        if path is not None:
            ledger_append(
                path, event=event, stage=stage, table=self.t.name,
                attempt=inventory["attempt"],
                candidate=inventory["candidate"],
                counts_file=inventory["counts_file"],
                counts=inventory["iterations_seal"],
                seed=inventory.get("layout_seed"), output=str(root),
                checkout=str(Path(repo).resolve()), **more)

    def close_attempt(self, path, stage, inventory, root, repo, status,
                      **note):
        """The close of an attempt, with `note` (what the end of an early
        stop adds: the reason it could not be judged, or the difference it
        found and could not mark). When it cannot be written the attempt
        stays open in the ledger, which shows it as interrupted, the
        outcome of the run is not replaced by the failure, and the line
        printed carries `note`, which is then the only record of it."""
        try:
            self.h.record_attempt(path, "close", stage, inventory, root,
                                  repo, status=status, **note)
        except Exception as error:
            print("ATTEMPT-NOT-CLOSED %s (outcome %s): %s%s" % (
                inventory["attempt"], status, error, "".join(
                    "; %s: %s" % item for item in note.items())),
                file=sys.stderr, flush=True)

    def check_attempt(self, args, inventory, stage):
        """The ledger holds the opening of this grid, and its chain is
        intact. Returns the ledger, or None."""
        path = self.h.attempts_file(args, False)
        if path is None:
            return None
        a.require(path.is_file(), "no attempts ledger: %s" % path)
        state = Ledger(path)
        want = dict(event="open", stage=stage, attempt=inventory["attempt"],
                    candidate=inventory["candidate"],
                    counts=inventory["iterations_seal"],
                    seed=inventory.get("layout_seed"))
        a.require(any(all(line.get(k) == v for k, v in want.items()) and
                      line.get("table", self.t.family) == self.t.name
                      for line in state.records),
                  "the attempts ledger has no opening of this grid")
        return state

    def refuse_found(self, state, attempts):
        """The attempts of this grid, named by id (`attempts`), that hold a
        difference found and not marked are refused like a dead grid: the
        checkout was known to differ and the inventory could not say so.
        The ledger is the table's, shared by every grid, so the attempts
        of another grid are not read: a found difference kills its own
        grid, stays in the ledger and is printed by every later replay,
        but does not touch a new grid in a new output. Only a replay (and
        so a close) reads it; a `--resume` does not."""
        if state is None:
            return
        for (attempt, _), row in state.attempts().items():
            if attempt in attempts and row["found"]:
                raise ValueError(
                    "the checkout changed while attempt %s ran (%s) and "
                    "the mark could not be written: the grid is dead, "
                    "neither replayed nor closed; its route is a new grid "
                    "in a new output" % (attempt, row["found"][0]))

    def attempt_counts(self, state, candidate):
        """(attempts of the table, attempts of the candidate) in a ledger;
        each stage of a grid is one."""
        found = state.attempts(self.t.name, self.t.family)
        return len(found), sum(1 for row in found.values()
                               if row["candidate"] == candidate)

    def ledger_counts(self, args, candidate):
        """The counts of the ledger that args name, or None."""
        path = self.h.attempts_file(args, False)
        if path is None:
            return None
        a.require(path.is_file(), "no attempts ledger: %s" % path)
        return self.h.attempt_counts(Ledger(path), candidate)

    def report_attempts(self, state, inventory, stage):
        """Print every attempt of the table in the ledger, the candidate's
        marked, with every status it closed with and the checkouts of its
        lines, so that a reader of a replay sees each retry, an interruption
        or a checkout that changed on the way, and a retry made elsewhere.
        A close that carries a difference found and not marked
        (`CHECKOUT-FOUND-NOT-MARKED`), or an end that could not be judged
        (`JUDGEMENT-NOT-MADE`), has a line of its own. The former is
        refused for the attempts of the grid being replayed (and its first
        stage) before this is reached, so a replay that gets here prints it
        only for the attempts of other grids of the table: they stay
        visible, and they do not touch this one.
        The attempts of a table that are not all in one checkout are
        named."""
        if state is None:
            return
        found = state.attempts(self.t.name, self.t.family)
        total, mine = self.h.attempt_counts(state, inventory["candidate"])
        own = sum(1 for line in state.records
                  if line.get("table", self.t.family) == self.t.name)
        print("ATTEMPTS of %s: %d in the ledger, %d of this candidate %s "
              "(%d records of %s, %d records in the family ledger, "
              "chain intact)" % (
                  self.t.label, total, mine, inventory["candidate"], own,
                  self.t.label, len(state.records)))
        for (attempt, kind), row in found.items():
            mark = (" (this grid)" if (attempt, kind) == (
                inventory["attempt"], stage) else
                " (this candidate)" if row["candidate"] ==
                inventory["candidate"] else "")
            print("ATTEMPT %s %s opened %s resumed %d status %s candidate "
                  "%s checkout %s%s" % (
                      attempt, kind, row["opened"], row["resumed"],
                      ",".join(row["statuses"]) or "interrupted",
                      row["candidate"], ",".join(map(str, row["checkouts"])),
                      mark))
            for text in row["found"]:
                print("CHECKOUT-FOUND-NOT-MARKED %s %s" % (attempt, text))
            for text in row["judgement"]:
                print("JUDGEMENT-NOT-MADE %s %s" % (attempt, text))
        places = {x for row in found.values() for x in row["checkouts"]}
        if len(places) > 1:
            print("LEDGER-CHECKOUTS: the attempts of this ledger were made "
                  "in %d different checkouts" % len(places))
        for note in state.notes:
            print(note)

    def check_provenance(self, args, inventory):
        """The counts file the grid names is derived again from the pilot
        (a table with fixed seconds)."""
        if not self.t.fixed_seconds:
            return
        a.require(args.pilot is not None,
                  "%s needs --pilot DIR" % self.t.label)
        self.h.check_counts(Path(args.pilot).resolve(),
                            self.h.counts_for(inventory))

    def bind_checkout(self, repo, commit, recorded=False):
        """The checkout the measurement runs in is that of `commit`, and
        the one `prepare` stamped (checkout_identity). Where the record of
        the grid already exists (`recorded`: a resumption, or a second
        stage, whose first stage has been measured) a refusal ends with what
        is safe there (`RESUMING`), not with what a fresh start does."""
        try:
            return checkout_identity(repo, commit, self.h.stamp_path(repo))
        except CheckoutRefused as error:
            if not recorded:
                raise
            raise error.resumed() from None

    def recheck(self, repo, commit, inventory):
        """The checkout is still the one the inventory recorded. It is
        asked under the lock, before anything is written, and at every end
        of an attempt that the process survives (`judge_end`); a checkout
        that changed while a grid ran (a build, an edit, a checkout of
        another commit) leaves no grid that passes, and the attempt closes
        as `checkout-changed`. The grid
        is dead (`CheckoutChanged.dead`) when the head, the tree or the
        products are known to differ from the record, which includes any
        change to a tracked file (`known_difference`: that is judged
        without a clean tree or a stamp). Only a checkout with untracked
        files, or without a usable stamp, is not dead, and a resumption
        compares the record."""
        if not self.t.fixed_seconds:
            return
        try:
            # The head is the recorded one, for a pilot too: a head that
            # moved is judged before the tree is looked at.
            found = self.h.bind_checkout(
                repo, commit or inventory["checkout"]["head"])
        except CheckoutUnjudged as error:
            known = known_difference(repo, inventory["checkout"])
            if known is not None:
                raise CheckoutChanged(known) from None
            # The record is of a grid that has begun: what is safe is what a
            # resumption does, and a prepare is not.
            raise CheckoutChanged(str(error.resumed()), dead=False) \
                from None
        except ValueError as error:
            raise CheckoutChanged(str(error)) from None
        if found != inventory["checkout"]:
            raise CheckoutChanged(
                "the checkout is not the one recorded: %s, not %s"
                % (found, inventory["checkout"]))

    def judge_end(self, root, repo, commit, inventory, stop=None):
        """Judge the checkout at the end of an attempt, as `recheck` does,
        and mark what it finds: the one place that marks. A grid or a
        second stage records `checkout_changed` when the checkout is known
        to differ (dead), and nothing when it was only not judged; a pilot
        records `checkout_unjudged` too, and lists the text in
        `unjudged_ends`. The inventory is written with the mark, or not at
        all.

        It is called at the normal end of the measuring, where it raises
        the `CheckoutChanged` it found. It is called again for an attempt
        that stops early, by the exception `stop` (a cell that raised, a
        failure inside the measuring, an interrupt), and then it never
        raises: the exception of the stop goes on to decide the exit
        status. It returns the status the attempt closes with and what its
        close line adds:

        - something was found and marked: `checkout-changed`, nothing
          added;
        - the checkout was found to differ (dead) and the mark could not be
          written: `checkout-changed`, with `found`, the text found and the
          failure of the mark; the inventory does not say it, so the ledger
          is the only record (a `replay` and a `close` refuse such a
          grid);
        - the checkout could not be asked, or the mark of an end that was
          only not judged could not be written: `interrupted`, with the
          reason as `judgement`, as of a process that was killed;
        - nothing found: `interrupted`, nothing added."""
        try:
            try:
                self.h.recheck(repo, commit, inventory)
            except CheckoutChanged as error:
                try:
                    self.h.mark_end(root, inventory, error)
                except BaseException as failure:
                    if stop is not None and error.dead:
                        return "checkout-changed", dict(
                            found="%s; not marked: %s: %s" % (
                                error, type(failure).__name__, failure))
                    raise
                if stop is None:
                    raise
                return "checkout-changed", {}
            return "interrupted", {}
        except BaseException as failure:
            if stop is None:
                raise
            return "interrupted", dict(judgement="not made: %s: %s" % (
                type(failure).__name__, failure))

    def mark_end(self, root, inventory, error):
        """Write into the inventory what the end of an attempt found, if it
        is to be marked (see `judge_end`)."""
        if error.dead:
            marks = dict(checkout_changed=str(error))
        elif inventory["schema"] == self.t.schema("pilot"):
            marks = dict(checkout_unjudged=str(error), unjudged_ends=[
                *inventory.get("unjudged_ends", []), str(error)])
        else:
            return
        checkpoint(root / "inventory.json", dict(inventory, **marks))
        inventory.update(marks)

    def prepare(self, args):
        """Configure the checkout, build it and stamp it. It needs a clean
        checkout and takes the lock; in the repository root it runs
        configure (`CONFIGURE` reading `CONFIGURE_INPUT`, with the `poly` on
        the PATH) and then the real build (`BUILD`; Holmake decides what is
        out of date) with no standard input. Only when both exit zero,
        configure has printed its closing line (`FINISHED`), the build has
        printed no stale-executable warning, and the checkout is configured
        here and clean at the same HEAD, does it write the stamp: HEAD, the tree
        outside the performance area, the content digest of the shared
        products and the build command. An earlier stamp is removed first,
        so that a failed or interrupted configure or build leaves none. The
        log of both is `prepare.log` beside the ledger, replaced by the next
        `prepare` (a table of a family that is not named like it keeps its own
        stamp and log, see `stamp_path`). The measuring commands compare the
        checkout with the stamp and never read a file time."""
        t = self.t
        a.require(t.fixed_seconds, "%s takes no build stamp" % t.label)
        repo = Path(args.repo).resolve()
        stamp = self.h.stamp_path(repo)
        self.h.attempts_file(args, True)  # the ledger place, while cheap
        before = clean_head(repo)
        with self.h.locked(repo) as fds:
            stamp.unlink(missing_ok=True)
            log = self.h.prepare_log_path(repo)
            log.unlink(missing_ok=True)
            inside = ["/bin/sh", "-c", 'cd "$1" && shift && exec "$@"',
                      "prepare", str(repo)]
            configured = a.run_logged(
                inside + list(CONFIGURE), log, fds, args.timeout,
                stdin=repo / CONFIGURE_INPUT)
            a.require(configured["exit"] == 0 and
                      not configured["timed_out"],
                      "configure failed (exit %s%s), no build stamp: see %s"
                      % (configured["exit"], ", timed out" if
                         configured["timed_out"] else "", log))
            a.require(configure_finished(log),
                      "configure exited 0 but did not print %r, so it "
                      "stopped on an exception it swallowed, no build "
                      "stamp: see %s" % (FINISHED, log))
            configured_holdir(repo)
            built = a.run_logged(
                inside + list(BUILD), log, fds, args.timeout,
                stdin=subprocess.DEVNULL, append=True)
            a.require(not stale_executable_warning(log),
                      "bin/build warned that an executable is older than "
                      "its sources although configure ran just before, so "
                      "bin/hol or bin/Holmake may not be the product of "
                      "this tree, no build stamp: see %s" % log)
            a.require(built["exit"] == 0 and not built["timed_out"],
                      "the build failed (exit %s%s), no build stamp: see %s"
                      % (built["exit"], ", timed out" if built["timed_out"]
                         else "", log))
            try:
                found = build_stamp(repo)
            except ValueError as error:
                raise ValueError("configure and the build left the checkout "
                                 "unusable, no build stamp: %s"
                                 % error) from None
            a.require(found["head"] == before["head"],
                      "HEAD moved during the build, no build stamp")
            partial = stamp.with_name(stamp.name + ".partial")
            partial.write_text(json.dumps(found, indent=2, sort_keys=True,
                                          allow_nan=False) + "\n")
            partial.replace(stamp)
        print("PREPARED %s tree %s products %s (%d files), stamp %s" % (
            found["head"], found["tree_outside_performance"][:12],
            found["products"]["sha256"][:12], found["products"]["files"],
            stamp), flush=True)
        return 0

    def check_checkout(self, inventory, repo=None):
        """The recorded checkout names the candidate, its tree outside the
        performance area is what git gives for the candidate, and it holds
        the digest of the products. That is all a replay can know: not that
        the checkout was so at the time of the run, which the stamp, the lock
        and the ledger make a discipline of the run, nor what the products
        were, which only the machine that measured can compare."""
        if not self.t.fixed_seconds:
            return
        repo = a.HERE.parents[3] if repo is None else repo
        found = inventory.get("checkout")
        a.require(isinstance(found, dict) and sorted(found) == [
            "head", "products", "tree_outside_performance"] and
            found["head"] == inventory["candidate"] and
            isinstance(found["products"], str) and
            len(found["products"]) == 64 and
            found["tree_outside_performance"] == git_tree_outside(
                repo, inventory["candidate"]), "changed checkout")

    def refuse_unpassable(self, args, differing):
        """A grid with a source that differs without a current pin never
        passes (with_sources), so measuring it is days for a known result.
        Only a diagnostic subset (`--only`) is allowed, and it is marked,
        so that a resumption cannot make it a grid."""
        a.require(args.only, "%d source file(s) differ from the baseline "
                  "without a current pin, so the grid cannot pass: %s "
                  "(--only measures a diagnostic subset)"
                  % (len(differing), ", ".join(differing)))
        return True

    def keep(self, repo, commit):
        """Keep the measured commit, and with it the counts commit of its
        history, where a rebase and garbage collection will not take it."""
        git_keep(repo, self.t.family, commit)

    def run(self, args):
        t = self.t
        root = args.output.resolve()
        counts = a.load(args.iterations)
        a.require(counts["schema"] == t.schema("iterations"),
                  "wrong predeclared counts")
        a.require(set(counts["iterations"]) == set(t.names()) and
                  counts.get("seconds", {}) == t.seconds_map(),
                  "predeclared counts do not match the table")
        a.require(a.seal(args.iterations) == a.seal(t.latest()),
                  "changed predeclared counts")
        a.require(counts["baseline"] == args.baseline == t.baseline,
                  "baseline differs from the table's or its counts'")
        a.require(args.candidate != args.baseline,
                  "the candidate is the baseline")
        a.require(not t.fixed_seconds or args.batch_seconds == t.seconds,
                  "batch seconds differ from the table")
        a.require(not t.fixed_seconds or all(k in counts for k in (
            "pairs", "samples", "layout_seed", "target", "max_pairs",
            *(("pairs_by_cell",) if t.replaces is not None else ()))),
            "predeclared counts do not match the table")
        # Before an attempt can be opened: a mismatch is a refusal, not a
        # failed attempt in the ledger.
        a.require(schedule_of(counts) == t.schedule, "the schedule of the "
                  "counts differs from the table's")
        pairs, samples, seed = self.h.settings(args, counts)
        a.require(seed is not None or not t.require_seed,
                  "%s needs layout randomization (--layout-seed)" % t.label)
        if t.replaces is None:
            self.h.bind_from(args)  # refuses a grid to replace
        else:
            # The grid replaced is bound (by the seals the counts record, or
            # in full where the code has changed), and its attempts must be
            # in the ledger this appends to, before anything is created.
            self.h.bind_from(args, counts=counts)
            self.h.require_replaced_openings(args)
        inventory = dict(
            schema=t.schema("experiment"), baseline=args.baseline,
            candidate=args.candidate, seconds=args.batch_seconds,
            pairs=pairs, samples=samples, outliers="none removed",
            policy=a.EQUIVALENCE_POLICY, iterations=counts,
            iterations_seal=a.seal(t.latest()), runs=[],
            **self.h.code_now())
        keys = t.keys()
        if args.only:
            keys = [k for k in keys if "%s-%d" % k in args.only]
            a.require(len(set(args.only)) == len(args.only),
                      "repeated --only cell")
            a.require(len(keys) == len(args.only), "unknown --only cell")
        ledger = self.h.attempts_file(args, True)
        self.h.check_output(args)
        if t.fixed_seconds:
            # A resumption after a recorded change of a sealed file is
            # judged by the grid's own header (check_header).
            a.require(args.resume or counts.get("sealed", {}) ==
                      inventory.get("sealed", {}),
                      "the counts are bound to other sealed files")
            inventory.update(counts_file=t.latest().name,
                             attempt=uuid.uuid4().hex)
            inventory["checkout"] = self.h.bind_checkout(
                args.repo, args.candidate, args.resume)
        if seed is not None:
            self.h.check_seed(seed)
            inventory["layout_seed"] = layout_seed(seed)
        if t.fixed_seconds:
            inventory["counts_commit"] = self.h.counts_commit(
                args.repo, args.candidate, t.latest())
        if t.sources:
            inventory["sources"] = self.h.source_record(
                args.repo, args.baseline, args.candidate)
            differing = self.h.source_identity(
                inventory["sources"], self.h.pins_for(inventory))["differing"]
            for path in differing:
                print("SOURCE-DIFFERS " + path, flush=True)
            if differing and t.fixed_seconds and \
                    self.h.refuse_unpassable(args, differing):
                inventory["diagnostic"] = True
        if t.tree:
            inventory["source_tree"] = self.h.source_tree(
                args.repo, args.baseline, args.candidate)
        if t.replaces is not None:
            # What the follow-up takes over from the replaced grid is
            # judged before an attempt opens.
            inventory["replaces"] = self.h.replaces_record(root, inventory)
            self.h.check_replaced(inventory, root, args.repo)
        self.h.check_provenance(args, inventory)
        with self.h.locked(args.repo):
            self.h.recheck(args.repo, args.candidate, inventory)
            reports = self.h.begin(root, inventory, args.resume)
            if args.resume:
                self.h.check_attempt(args, inventory, "first")
            if t.fixed_seconds:
                self.h.keep(args.repo, args.candidate)
            self.h.record_attempt(ledger, "resume" if args.resume else "open",
                                  "first", inventory, root, args.repo,
                                  only=args.only)
            status, note = "interrupted", {}
            try:
                self.h.measure(root, inventory, [
                    k + (self.cell_pairs(counts, k, pairs),) for k in keys],
                    args, reports)
                if args.only:
                    status = "partial"
                    return 2
                decisions = self.h.with_sources(self.h.summary(reports),
                                                inventory)
                a.save(root / "decisions.json", decisions)
                status = decisions["status"]
                return self.h.status_code(decisions)
            except CheckoutChanged:
                status = "checkout-changed"
                raise
            except BaseException as stop:
                status, note = self.h.judge_end(
                    root, args.repo, args.candidate, inventory, stop)
                raise
            finally:
                self.h.close_attempt(ledger, "first", inventory, root,
                                     args.repo, status, **note)

    # Follow-up -------------------------------------------------------

    def cell_pairs(self, counts, key, default):
        """The pairs of one cell: the counts' own for it when they name
        one per cell (a follow-up's), else `default`."""
        return counts.get("pairs_by_cell", {}).get("%s-%d" % key, default)

    def bound(self):
        """What `bind_replaced` or `bind_sealed` kept; a refusal when
        nothing was bound (a table that replaces none, or a helper called
        before the grid is)."""
        a.require(self.t.replaces is not None,
                  "%s replaces no grid" % self.t.label)
        a.require(self.replaced is not None,
                  "%s has not bound the grid it replaces: bind it first "
                  "(bind_from)" % self.t.label)
        return self.replaced

    def replaced_names(self, grid, inventory):
        """The files of the replaced grid that the binding reads, by name
        relative to the grid: the inventory and decisions of the grid, and
        of its first stage where it is a second stage. `inventory` is the
        grid's own. Returns (names, the first stage's directory)."""
        old = self.t.replaces.engine
        names = ["inventory.json", "decisions.json"]
        first = Path(grid)
        if inventory["schema"] == old.t.schema("extension"):
            first = (Path(grid) / inventory["grid"]).resolve()
            where = os.path.relpath(first, grid)
            names += [os.path.join(where, n)
                      for n in ("inventory.json", "decisions.json")]
        return names, first

    def check_replaced_cells(self, first, decisions):
        """What the replaced grid's first stage and final decision must be
        for this table to replace it: the baseline, limits and pairs of the
        table, and exactly the table's cells inconclusive. Returns the open
        cells."""
        t = self.t
        old = t.replaces.engine
        a.require(first["baseline"] == t.baseline,
                  "baseline differs from the replaced grid's")
        a.require(old.limits_of(first) == (t.target, t.max_pairs),
                  "the second-stage limits differ from the replaced grid's")
        a.require(t.pairs == 2 * first["pairs"], "the pairs of the table "
                  "are not twice those of the replaced grid")
        opened = sorted("%s-%d" % (row["case"], row["size"])
                        for row in decisions["workloads"]
                        if classify_row(row) == "inconclusive")
        a.require(opened == sorted(t.names()), "follow-up cells differ "
                  "from the open cells of the replaced grid: %s, not %s"
                  % (", ".join(sorted(t.names())), ", ".join(opened)))
        return opened

    def bind_replaced(self, grid, pilot, repo, ledger=None):
        """Replay the grid this table replaces in full, by the engine of the
        table that measured it, and keep what follows from it: its first
        stage's reports and the cells it left inconclusive, which must be
        exactly this table's. The grid is its second stage where it has one;
        a first stage whose second stage is still to come is refused, for the
        follow-up replaces the final stage. Anything the replay finds wrong
        is a refusal. This is the binding of `predeclare` (which records the
        seals of what it read) and of `replay`; the other commands bind by
        those seals (`bind_sealed`)."""
        t = self.t
        old = t.replaces.engine
        old.replay(argparse.Namespace(output=grid, partial=False, repo=repo,
                                      pilot=pilot, ledger=ledger))
        found = old.replayed
        first, decisions = found["first"], found["decisions"]
        if found["inventory"]["schema"] != old.t.schema("extension"):
            a.require(not old.planned(found["stage1"], first),
                      "the replaced grid is not final: its second stage "
                      "is still to come, name that (--replaces)")
        opened = self.h.check_replaced_cells(first, decisions)
        names, first_root = self.h.replaced_names(grid, found["inventory"])
        self.replaced = dict(
            grid=Path(grid), first_root=first_root, first=first,
            stage1=found["stage1"], decisions=decisions, open=opened,
            files={n: a.seal(Path(grid) / n) for n in names})
        return self.replaced

    def check_recorded_code(self, recorded):
        """The `replaces` block of a counts file holds `code`: the seals of
        the code `predeclare` replayed with, a record that is not derived
        again, so only its shape is checked."""
        code = recorded.get("code") if isinstance(recorded, dict) else None
        a.require(isinstance(code, dict) and code and all(
            isinstance(n, str) and isinstance(v, dict) and
            sorted(v) == ["bytes", "sha256"] and type(v["bytes"]) is int and
            isinstance(v["sha256"], str) and
            re.fullmatch(r"[0-9a-f]{64}", v["sha256"]) is not None
            for n, v in code.items()),
            "the counts record no well-formed seals of the code that "
            "replayed the replaced grid (replaces.code)")

    def changed_code(self, recorded):
        """The names of the files of the code of the replay whose seals
        are not those `predeclare` recorded (`replaces.code`), sorted; none
        when the seal binding is valid. A record that is no block of seals
        is left to `bind_sealed` to refuse, a malformed `code` is refused
        here."""
        if not (isinstance(recorded, dict) and
                isinstance(recorded.get("files"), dict)):
            return []
        self.h.check_recorded_code(recorded)
        was, now = recorded["code"], self.h.replay_code()
        return sorted(n for n in {*was, *now} if was.get(n) != now.get(n))

    def bind_sealed(self, grid, recorded, repo=None):
        """Bind the grid this table replaces by the seals the counts file
        records (`recorded`, its `replaces`): every file of the grid that the
        binding reads is that of `predeclare`, the open cells are those of
        the sealed decisions, and the first-stage reports of the table's
        cells (alone) are replayed from their archives for the pairs. The
        full replay was made at `predeclare` and is made again by `replay`.
        The binding is valid only while the code that replayed the grid is
        unchanged (`changed_code`; `bind_from` replays in full otherwise),
        and the cheap checks of the full replay are made on both
        inventories of the grid (header, sources, commit, checkout), through
        the hooks of the replaced engine as the full replay does; what the
        full replay leaves is named in PROTOCOL.md."""
        t = self.t
        old = t.replaces.engine
        grid = Path(grid)
        a.require(isinstance(recorded, dict) and isinstance(
            recorded.get("files"), dict) and "inventory.json" in
            recorded["files"], "the counts record no replaced grid")
        files = recorded["files"]

        def same(name):
            path = grid / name
            a.require(path.is_file() and a.seal(path) == files.get(name),
                      "replaced grid changed since predeclare: %s" % name)
        same("inventory.json")
        inventory = a.load(grid / "inventory.json")
        names, first_root = self.h.replaced_names(grid, inventory)
        a.require(sorted(files) == sorted(names),
                  "replaced grid changed since predeclare: the files "
                  "read are %s, not %s" % (", ".join(sorted(names)),
                                           ", ".join(sorted(files))))
        for name in names:
            same(name)
        changed = self.h.changed_code(recorded)
        a.require(not changed, "the seal binding is valid only for the code "
                  "of predeclare, which changed: %s" % ", ".join(changed))
        if first_root != grid:
            where = os.path.relpath(first_root, grid)
            a.require(
                inventory["grid_inventory"] == files[
                    os.path.join(where, "inventory.json")] and
                inventory["grid_decisions"] == files[
                    os.path.join(where, "decisions.json")],
                "replaced grid changed since predeclare: its second stage "
                "names another first stage")
        first = a.load(first_root / "inventory.json")
        old.h.check_experiment(first)
        repo = a.HERE.parents[3] if repo is None else repo
        for found in ([first] if first_root == grid else [first, inventory]):
            old.h.check_header(found)
            old.h.check_sources(found, repo)
            old.h.check_commit(found, repo)
            old.h.check_checkout(found, repo)
        decisions = a.load(grid / "decisions.json")
        opened = self.h.check_replaced_cells(first, decisions)
        a.require(opened == recorded.get("open"),
                  "the open cells differ from those the counts record")
        self.replaced = dict(
            grid=grid, first_root=first_root, first=first,
            stage1=old.h.replay_rows(first_root, first, only=t.keys()),
            decisions=decisions, open=opened, files=dict(files))
        return self.replaced

    def bind_from(self, args, inventory=None, root=None, counts=None):
        """Bind the grid for a command: the grid is the one `--replaces`
        names, or where a recorded inventory of the follow-up (in `root`)
        says it is, with the seals that record holds; a table that replaces
        none is given none. Without `counts` the grid is replayed in full
        (`bind_replaced`, which needs `--replaces-pilot`); with the counts
        file (or the counts an inventory holds) it is bound by the seals
        that file records (`bind_sealed`)."""
        t = self.t
        given = getattr(args, "replaces", None)
        pilot = getattr(args, "replaces_pilot", None)
        if t.replaces is None:
            a.require(given is None and pilot is None,
                      "%s replaces no grid" % t.label)
            return None
        a.require(counts is not None or pilot is not None,
                  "%s needs --replaces-pilot DIR, the pilot of the grid it "
                  "replaces" % t.label)
        if inventory is None:
            a.require(given is not None, "%s needs --replaces GRID, the "
                      "grid it replaces" % t.label)
            grid = given
        else:
            a.require(given is None, "the replaced grid is the one the "
                      "record names")
            grid = Path(root) / inventory["replaces"]["grid"]
        repo = getattr(args, "repo", None) or a.HERE.parents[3]
        changed = [] if counts is None else self.h.changed_code(
            counts.get("replaces"))
        if changed:
            # The seals bind only the code of `predeclare`: with other
            # code the grid is replayed in full, as `predeclare` did.
            a.require(pilot is not None,
                      "code changed since predeclare: %s; the replaced "
                      "grid is then replayed in full, which needs "
                      "--replaces-pilot DIR" % ", ".join(changed))
            print("%s: code changed since predeclare (%s): the replaced "
                  "grid is replayed in full" % (t.label, ", ".join(changed)),
                  flush=True)
        if counts is not None and not changed:
            bound = self.h.bind_sealed(Path(grid).resolve(),
                                       counts.get("replaces"), repo)
        else:
            bound = self.h.bind_replaced(
                Path(grid).resolve(), Path(pilot).resolve(), repo,
                getattr(args, "ledger", None))
        if inventory is not None:
            a.require(inventory["replaces"] ==
                      self.h.replaces_record(root, inventory),
                      "changed replaced grid")
        return bound

    def replaces_record(self, root, inventory):
        """What an inventory in `root` records of the replaced grid, the
        fields of the replaced grid named as such and the follow-up's own
        beside them: the grid by its path relative to `root` and the seals of
        its inventory and decisions, the layout seed and the counts seal it
        was measured with, and the layout seed and counts seal of this
        grid (`inventory`'s)."""
        rep = self.h.bound()
        grid, first = rep["grid"], rep["first"]
        return dict(grid=os.path.relpath(grid, root),
                    replaced_inventory=a.seal(grid / "inventory.json"),
                    replaced_decisions=a.seal(grid / "decisions.json"),
                    replaced_seed=first.get("layout_seed"),
                    replaced_counts=first["iterations_seal"],
                    followup_seed=inventory.get("layout_seed"),
                    followup_counts=inventory["iterations_seal"])

    def followup_pairs(self):
        """The pairs of each cell of the follow-up: the second-stage rule
        applied to the develop/develop control of the replaced grid's first
        stage, with the pairs of that stage as its base, so that twice them
        is the floor and the cap is the table's. Nothing of a candidate
        enters."""
        rep = self.h.bound()
        first = rep["first"]
        limits = self.t.replaces.engine.limits_of(first)
        found = {}
        for key in self.t.keys():
            report = rep["stage1"][key]
            a.require(report["success"], "a follow-up cell the replaced "
                      "grid did not measure")
            result, = report["workloads"]
            found["%s-%d" % key] = second_stage_pairs(
                control_half_width(result), first["pairs"], *limits)
        return found

    def replaced_counts(self, pilot):
        """The fields of a counts file that come from the replaced grid: the
        pairs of each cell, and a `replaces` block with the grid's path
        relative to the follow-up's pilot (the two must stay siblings in the
        evidence layout: the path is compared exactly), the seals of every
        file of the grid the binding reads and of the code that replayed it
        (`bind_sealed` checks them) and the open cells."""
        rep = self.h.bound()
        grid = rep["grid"]
        return dict(pairs_by_cell=self.h.followup_pairs(), replaces=dict(
            grid=os.path.relpath(grid, Path(pilot).resolve()),
            files={n: a.seal(grid / n) for n in sorted(rep["files"])},
            open=list(rep["open"]), code=self.h.replay_code()))

    def replay_code(self):
        """The seals of the code that replayed the replaced grid:
        REPLAY_CODE, the pin file and the counts file of the table
        replaced (the counts are what its header check compares)."""
        old = self.t.replaces.engine.t
        here = Path(__file__).resolve().parent
        found = {n: a.seal(here / n) for n in REPLAY_CODE}
        if old.pin_file:
            found[old.pin_file] = a.seal(old.home / old.pin_file)
        found[old.latest().name] = a.seal(old.latest())
        return dict(sorted(found.items()))

    def require_replaced_openings(self, args):
        """The ledger the attempt of a follow-up will be appended to (the
        very file `run` and `extend` append to, in the checkout `--repo`
        names) holds the openings of every attempt of the replaced grid,
        made in this checkout: the follow-up extends the one chain of the
        family, in the checkout that holds it. A missing ledger, one
        without those openings or with openings of another checkout, or one
        whose attempts of the replaced grid the full replay refuses
        (`refuse_found`) is refused before anything is measured or
        created, and a fresh chain is never started."""
        old = self.t.replaces.engine
        rep = self.h.bound()
        path = self.h.ledger_path(args.repo)
        where = argparse.Namespace(ledger=path, repo=args.repo)
        a.require(path.is_file(),
                  "no attempts ledger at %s: a follow-up appends to the "
                  "ledger that holds the openings of the replaced grid, "
                  "in the checkout of that ledger" % path)
        inventory = a.load(rep["grid"] / "inventory.json")
        stages = [(inventory, "first")]
        if inventory["schema"] == old.t.schema("extension"):
            stages = [(rep["first"], "first"), (inventory, "second")]
        here = str(Path(args.repo).resolve())
        for found, stage in stages:
            try:
                state = old.h.check_attempt(where, found, stage)
            except ValueError as e:
                raise ValueError(
                    "the attempts ledger %s lacks the %s-stage opening of "
                    "attempt %s of the replaced grid (%s): a follow-up "
                    "appends to the ledger that holds it, in the checkout "
                    "of that ledger" % (path, stage, found.get("attempt"),
                                        e)) from None
            a.require(state is not None, "the replaced grid has no "
                      "attempts ledger")
            opened = [line for line in state.records
                      if line.get("event") == "open" and
                      line.get("stage") == stage and
                      line.get("attempt") == found["attempt"] and
                      line.get("table", old.t.family) == old.t.name]
            a.require(any(line.get("checkout") == here for line in opened),
                      "the attempts ledger %s holds the %s-stage opening of "
                      "attempt %s of the replaced grid from the checkout "
                      "%s, not this one (%s): a follow-up appends to the "
                      "ledger in the checkout that holds it, not to a copy"
                      % (path, stage, found["attempt"], ", ".join(sorted(
                          {str(x.get("checkout")) for x in opened})), here))
            old.h.refuse_found(state, {found["attempt"]})

    def sealed_paths(self):
        """The repository names of the table's sealed files and its driver,
        relative to the root of the repository the code is in (`Table.root`),
        whatever checkout a command is pointed at and whether the files
        exist there. A file outside that repository is refused."""
        t = self.t
        found = set()
        for path in [t.driver, *(t.home / n for n in t.sealed)]:
            try:
                found.add(Path(path).resolve().relative_to(
                    t.root.resolve()).as_posix())
            except ValueError:
                raise ValueError("%s lies outside the repository %s" % (
                    path, t.root)) from None
        return found

    def check_replaced(self, inventory, root, repo):
        """A follow-up inventory (in `root`) against the replaced grid: the
        record of it, a layout seed that was not drawn before, the same
        candidate sources, and a candidate that differs from the replaced
        one below the table's tree only in the performance area and the
        files the table seals (the code it measures with), and in nothing
        the cases run."""
        t = self.t
        first = self.h.bound()["first"]
        repo = a.HERE.parents[3] if repo is None else repo
        a.require(inventory.get("replaces") ==
                  self.h.replaces_record(root, inventory),
                  "changed record of the replaced grid")
        seed = inventory.get("layout_seed")
        drawn = first.get("layout_seed")
        taken = set() if drawn is None else {drawn, drawn + "-ext"}
        a.require(seed is not None and not {seed, seed + "-ext"} & taken,
                  "the layout seed of the follow-up was drawn by the "
                  "replaced grid")
        a.require(inventory.get("sources") == first.get("sources"),
                  "candidate sources differ from the replaced grid's")
        if t.tree:
            sealed = self.h.sealed_paths()
            moved = [path for _, path in git_difference(
                repo, first["candidate"], inventory["candidate"], t.tree)
                if not path.startswith(pr.PERFORMANCE_DIR) and
                path not in sealed]
            a.require(not moved, "the candidate differs from the replaced "
                      "grid's below %s outside the performance area and the "
                      "sealed files: %s" % (t.tree, ", ".join(moved)))

    # Second stage ----------------------------------------------------

    def limits_of(self, inventory):
        """(target, cap) of the second stage as the counts the grid used say
        them, or None when they say none (a table whose counts predate
        them): a later change of the table does not change the plan an older
        grid is replayed by."""
        counts = inventory["iterations"]
        return (counts["target"], counts["max_pairs"]) \
            if "target" in counts and "max_pairs" in counts else None

    def limits_dict(self, inventory):
        target, cap = self.limits_of(inventory) or (self.t.target,
                                                    self.t.max_pairs)
        return dict(target=target, max_pairs=cap)

    def planned(self, stage1, first):
        """The remeasurement plan of a first stage, by its own limits."""
        limits = self.limits_of(first)
        pairs = first["iterations"].get("pairs_by_cell", first["pairs"])
        return self.h.extension_plan(
            stage1, pairs, *(() if limits is None else (limits,)))

    def extension_pairs(self, report, pairs, limits=None):
        """Pairs for a cell's remeasurement, or None when it is final.

        Under randomized layout a cell's develop/develop control may be too
        wide to resolve the margin. Such a cell is measured again, with a
        pair count computed from its control interval alone (never the
        candidate's), aiming at a half width of half the margin. A
        first-stage fail stays final whatever its control, so the candidate
        can only add fails."""
        if not report["success"]:
            return None
        result, = report["workloads"]
        metrics = result["candidate"]["metrics"]
        gated = a.EQUIVALENCE_POLICY["gated_timing"]
        if any(metrics[m]["decision"] == "fail" for m in gated):
            return None
        if all(metrics[m].get("control_valid") for m in gated):
            return None
        target, cap = limits or (self.t.target, self.t.max_pairs)
        return second_stage_pairs(control_half_width(result), pairs, target,
                                  cap)

    def extension_plan(self, reports, pairs, limits=None):
        """The remeasurement plan: `pairs` is the first-stage pair count of
        every cell, or a mapping from the name of each cell to its own."""
        plan = []
        for key in self.t.keys():
            own = pairs["%s-%d" % key] if isinstance(pairs, dict) else pairs
            extra = self.h.extension_pairs(
                reports[key], own, *(() if limits is None else (limits,)))
            if extra is not None:
                plan.append([*key, extra])
        return plan

    def check_code(self, code, seeded):
        """The seals of one code record (an inventory or a resumption) are
        those of this table's code now or of the earlier code it names."""
        t = self.t
        layout = [a.seal(a.__file__)] + list(t.layout_acceptance)
        a.require(code["driver"] in [a.seal(t.driver)] + list(t.drivers),
                  "changed driver")
        a.require(not t.engine or code["engine"] in
                  [a.seal(__file__)] + list(t.engines), "changed engine")
        a.require(code["acceptance"] in layout + list(t.acceptance),
                  "changed acceptance")
        a.require(not seeded or code["acceptance"] in layout,
                  "layout seed needs a layout-seeded acceptance")
        sealed = code.get("sealed", {})
        a.require(set(sealed) == set(t.sealed), "changed sealed files")
        for name, seal in sealed.items():
            a.require(seal in [a.seal(t.home / name),
                               *t.sealed_history.get(name, ())],
                      "changed " + name)
        if t.pin_file and "pins" in code:
            self.h.pins_for(code)

    def check_header(self, inventory):
        t = self.t
        a.require("checkout_changed" not in inventory,
                  "the checkout changed while this grid ran (%s): it is "
                  "dead, neither resumed nor replayed; its route is a new "
                  "grid in a new output" % inventory.get("checkout_changed"))
        seeded = inventory.get("layout_seed") is not None
        for code in [inventory] + inventory.get("resumed", []):
            self.h.check_code(code, seeded)
        a.require(inventory["policy"] == a.EQUIVALENCE_POLICY,
                  "changed policy")
        counts = a.load(self.h.counts_for(inventory))
        a.require(inventory["iterations"] == counts,
                  "changed predeclared counts")
        base = inventory["baseline"]
        a.require(base == t.baseline and counts["baseline"] == base,
                  "changed baseline")
        if t.fixed_seconds:
            settings = ["pairs", "samples"]
            if inventory["schema"] == t.schema("experiment"):
                settings.append("layout_seed")
            a.require(all(inventory.get(k) == counts[k] for k in settings),
                      "settings differ from the predeclared counts")
            if inventory["schema"] == t.schema("experiment"):
                a.require(counts.get("sealed", {}) ==
                          inventory.get("sealed", {}),
                          "the counts are bound to other sealed files")
            a.require(isinstance(inventory.get("counts_commit"), str) and
                      len(inventory["counts_commit"]) == 40,
                      "no commit of the predeclared counts")
            a.require(isinstance(inventory.get("attempt"), str) and
                      inventory["attempt"],
                      "no attempt recorded for the grid")
        a.require(not t.pin_file or "pins" in inventory,
                  "no seal of the pins")
        a.require(("sources" in inventory) == bool(t.sources) and
                  sorted(inventory.get("sources", t.sources)) ==
                  sorted(t.sources), "changed source files")
        a.require(("source_tree" in inventory) == bool(t.tree) and
                  inventory.get("source_tree", {"tree": t.tree})["tree"] ==
                  t.tree, "changed source tree")

    def replay_grid(self, root, repo=None):
        """A complete first-stage grid and its recorded decisions."""
        t = self.t
        inventory = a.load(root / "inventory.json")
        self.h.check_experiment(inventory)
        self.h.check_header(inventory)
        self.h.check_sources(inventory, repo)
        self.h.check_commit(inventory, repo)
        self.h.check_checkout(inventory, repo)
        reports = self.h.replay_rows(root, inventory)
        decisions = self.h.with_sources(self.h.summary(reports), inventory)
        a.require(decisions == a.load(root / "decisions.json"),
                  "changed %s decisions" % t.label)
        return inventory, reports, decisions

    def check_experiment(self, inventory):
        """Only a first-stage run replays like one; a pilot has no
        decisions and replays through `verify-counts`."""
        t = self.t
        a.require(inventory["schema"] != t.schema("pilot"),
                  "a pilot is checked by verify-counts, not replayed")
        a.require(inventory["schema"] == t.schema("experiment"),
                  "not a first-stage grid")

    def extension_inventory(self, grid, root, inventory):
        t = self.t
        seed = inventory.get("layout_seed")
        a.require(seed is not None,
                  "extension needs a layout-randomized grid")
        header = {k: inventory[k] for k in (
            "baseline", "candidate", "seconds", "pairs", "samples",
            "outliers", "policy", "iterations", "iterations_seal",
            "counts_file", "counts_commit", "checkout", "sources",
            "source_tree") if k in inventory}
        result = dict(header, schema=t.schema("extension"),
                      grid=os.path.relpath(grid, root),
                      grid_inventory=a.seal(grid / "inventory.json"),
                      grid_decisions=a.seal(grid / "decisions.json"),
                      layout_seed=layout_seed(seed + "-ext"),
                      **self.h.limits_dict(inventory), runs=[],
                      **self.h.code_now())
        if "replaces" in inventory:
            result["replaces"] = self.h.replaces_record(root, result)
        return result

    def combined(self, stage1, stage2, plan, inventory):
        a.require(set(stage2) == {(c, s) for c, s, _ in plan},
                  "incomplete remeasurement")
        decisions = self.h.with_sources(
            self.h.summary({**stage1, **stage2}), inventory)
        decisions["remeasured"] = dict(
            plan=plan, target=inventory["target"],
            max_pairs=inventory["max_pairs"], seed=inventory["layout_seed"],
            rule="B/B control outside the window and no first-stage fail")
        return decisions

    def extend(self, args):
        t = self.t
        grid, root = args.grid.resolve(), args.output.resolve()
        self.h.check_output(args)
        if t.fixed_seconds:
            # The cheap refusal first: the kind of grid, the recorded
            # checkout, then the present one, before the first stage is
            # replayed in full.
            recorded = a.load(grid / "inventory.json")
            self.h.check_experiment(recorded)
            self.h.check_checkout(recorded, args.repo)
            a.require(self.h.bind_checkout(
                args.repo, recorded["candidate"], True) ==
                recorded["checkout"],
                "the checkout is not the one the first stage was measured "
                "in")
        first, stage1, _ = self.h.replay_grid(grid, args.repo)
        if t.replaces is not None:
            self.h.bind_from(args, first, grid, counts=first["iterations"])
            self.h.check_replaced(first, grid, args.repo)
            self.h.require_replaced_openings(args)
        else:
            self.h.bind_from(args)
        # After the refusals about the ledger of the replaced grid, which
        # create nothing, as in `run`.
        ledger = self.h.attempts_file(args, True)
        self.h.check_provenance(args, first)
        # As `run` does, before the second stage is an attempt of the
        # ledger: a mismatch is a refusal, not a failed attempt.
        a.require(schedule_of(first["iterations"]) == t.schedule,
                  "the schedule of the counts differs from the table's")
        self.h.check_attempt(args, first, "first")
        inventory = self.h.extension_inventory(grid, root, first)
        if t.fixed_seconds:
            # Every second stage is an attempt of its own.
            inventory["attempt"] = uuid.uuid4().hex
        plan = self.h.planned(stage1, first)
        inventory["plan"] = plan
        print("PLAN %d cells: %s" % (len(plan), json.dumps(plan)),
              flush=True)
        with self.h.locked(args.repo):
            self.h.recheck(args.repo, first["candidate"], inventory)
            reports = self.h.begin(root, inventory, args.resume)
            if args.resume:
                self.h.check_attempt(args, inventory, "second")
            if t.fixed_seconds:
                self.h.keep(args.repo, first["candidate"])
            self.h.record_attempt(ledger, "resume" if args.resume else "open",
                                  "second", inventory, root, args.repo)
            status, note = "interrupted", {}
            try:
                self.h.measure(root, inventory, [tuple(p) for p in plan],
                               args, reports)
                decisions = self.h.combined(stage1, reports, plan, inventory)
                a.save(root / "decisions.json", decisions)
                status = decisions["status"]
                return self.h.status_code(decisions)
            except CheckoutChanged:
                status = "checkout-changed"
                raise
            except BaseException as stop:
                status, note = self.h.judge_end(
                    root, args.repo, first["candidate"], inventory, stop)
                raise
            finally:
                self.h.close_attempt(ledger, "second", inventory, root,
                                     args.repo, status, **note)

    def replay(self, args):
        t = self.t
        root = args.output.resolve()
        repo = getattr(args, "repo", None)
        inventory = a.load(root / "inventory.json")
        second = inventory["schema"] == t.schema("extension")
        if not second:
            self.h.check_experiment(inventory)
        self.h.check_header(inventory)
        if schedule_of(inventory["iterations"]) == "warmup":
            print("%s schedule: warmup; counts rule: %s" % (
                t.label, inventory["iterations"]["rule"]), flush=True)
        self.h.check_sources(inventory, repo)
        self.h.check_commit(inventory, repo)
        self.h.check_checkout(inventory, repo)
        if t.replaces is not None:
            self.h.bind_from(args, inventory, root)
            self.h.check_replaced(inventory, root, repo)
        else:
            self.h.bind_from(args)
        self.h.check_provenance(args, inventory)
        stage = "second" if second else "first"
        state = self.h.check_attempt(args, inventory, stage)
        self.h.refuse_found(state, {inventory.get("attempt")})
        if second:
            grid = (root / inventory["grid"]).resolve()
            a.require(a.seal(grid / "inventory.json") ==
                      inventory["grid_inventory"] and
                      a.seal(grid / "decisions.json") ==
                      inventory["grid_decisions"],
                      "changed first-stage grid")
            first, stage1, _ = self.h.replay_grid(grid, repo)
            self.h.check_attempt(args, first, "first")
            # The first stage is a part of this grid: its difference found
            # and not marked kills the second stage as well.
            self.h.refuse_found(state, {first.get("attempt")})
            a.require(inventory == dict(
                self.h.extension_inventory(grid, root, first),
                plan=self.h.planned(stage1, first),
                runs=inventory["runs"],
                **{k: inventory[k] for k in t.code() + ("resumed", "attempt")
                   if k in inventory}), "changed extension plan")
            self.h.report_attempts(state, inventory, stage)
            reports = self.h.replay_rows(root, inventory)
            a.require([[r["case"], r["size"],
                        r.get("pairs", inventory["pairs"])]
                       for r in inventory["runs"]] ==
                      inventory["plan"][:len(inventory["runs"])],
                      "remeasurement differs from plan")
            if args.partial:
                a.require(not (root / "decisions.json").exists(),
                          "complete run replayed as partial")
                print("%s partial remeasurement: %d of %d cells replayed"
                      % (t.label, len(reports), len(inventory["plan"])))
                return 2
            decisions = self.h.combined(stage1, reports, inventory["plan"],
                                        inventory)
            a.require(decisions == a.load(root / "decisions.json"),
                      "changed %s decisions" % t.label)
            self.replayed = dict(inventory=inventory, first=first,
                                 stage1=stage1, stage2=reports,
                                 decisions=decisions)
            print("%s two-stage archives and decisions replayed: %s" % (
                t.label, decisions["status"]))
            return self.h.status_code(decisions)
        self.h.report_attempts(state, inventory, stage)
        reports = self.h.replay_rows(root, inventory)
        if args.partial:
            # An interrupted run has no grid decision; each finished cell
            # still replays exactly.
            a.require(not (root / "decisions.json").exists(),
                      "complete run replayed as partial")
            print("%s partial run: %d of %d cells replayed; no grid "
                  "decision" % (t.label, len(reports), len(t.keys())))
            return 2
        decisions = self.h.with_sources(self.h.summary(reports), inventory)
        a.require(decisions == a.load(root / "decisions.json"),
                  "changed %s decisions" % t.label)
        self.replayed = dict(inventory=inventory, first=inventory,
                             stage1=reports, stage2={}, decisions=decisions)
        print("%s archives and decisions replayed: %s" % (
            t.label, decisions["status"]))
        return self.h.status_code(decisions)

    # Command line ----------------------------------------------------

    def parser(self):
        t = self.t
        parser = argparse.ArgumentParser(description=self.doc)
        sub = parser.add_subparsers(dest="action", required=True)
        repo = a.HERE.parents[3]

        def settings(p):
            p.add_argument("--repo", type=Path, default=repo)
            p.add_argument("--timeout", type=int, default=1800)

        def provenance(p):
            # Required by a table with fixed seconds (checked when the
            # command runs, so that the other checks come first).
            p.add_argument("--pilot", type=Path,
                           help="the pilot the counts derive from")

        def ledger(p):
            p.add_argument("--ledger", type=Path,
                           help="read this attempts ledger, of the checkout "
                           "the grid was made in (read-only)")

        def replaced(p, grid=True):
            # A follow-up's: the grid it replaces and that grid's pilot
            # (the grid is the one the record names, where there is one).
            # The pilot is read by the commands that replay the grid in
            # full (`predeclare`, `replay`); the others bind it by the seals
            # of the counts and ignore it.
            if grid:
                p.add_argument("--replaces", type=Path, metavar="GRID",
                               help="the grid this table replaces (a "
                               "follow-up table), its second stage where "
                               "there is one")
            p.add_argument("--replaces-pilot", type=Path, metavar="DIR",
                           help="the pilot the counts of the replaced grid "
                           "derive from")

        build = sub.add_parser(
            "prepare", help="configure and build the checkout and stamp it "
            "for the measuring commands")
        build.add_argument("--repo", type=Path, default=repo)
        build.add_argument("--timeout", type=int, default=BUILD_TIMEOUT,
                           help="seconds each of the two commands, configure "
                           "and the build, may take")
        pilot = sub.add_parser(
            "pilot", help="develop-only experiments for the counts")
        pilot.add_argument("--output", type=Path, required=True)
        pilot.add_argument("--baseline", default=t.baseline)
        pilot.add_argument("--pairs", type=int, default=t.pilot_pairs)
        pilot.add_argument("--samples", type=int, default=t.pilot_samples)
        pilot.add_argument("--resume", action="store_true")
        pilot.add_argument("--authorize-measurements", action="store_true")
        settings(pilot)
        counts = sub.add_parser(
            "predeclare", help="counts file from a pilot or earlier grid")
        counts.add_argument("--grid", type=Path, required=True)
        counts.add_argument("--output", type=Path, required=True)
        counts.add_argument("--revises", type=Path,
                            help="the table's last counts file, to revise "
                            "(a new file, never an edit)")
        counts.add_argument("--repo", type=Path, default=repo)
        ledger(counts)
        replaced(counts)
        how = counts.add_mutually_exclusive_group()
        how.add_argument("--rescale", nargs="+", metavar="CELL",
                         help="cells the previous grid rejected as fixed "
                         "calibration too short (a warmup table: as a "
                         "warm-up or batch too short)")
        how.add_argument("--repilot", metavar="REASON",
                         help="a fresh pilot, for a change that alters "
                         "what is measured; the reason is recorded")
        again = sub.add_parser(
            "verify-counts", help="counts file against its pilot")
        again.add_argument("--grid", type=Path, required=True)
        again.add_argument("--counts", type=Path,
                           help="default: the table's counts file")
        again.add_argument("--repo", type=Path, default=repo)
        ledger(again)
        replaced(again)
        execute = sub.add_parser("run")
        execute.add_argument("--output", type=Path, required=True)
        execute.add_argument("--iterations", type=Path, default=t.latest())
        execute.add_argument("--baseline", default=t.baseline)
        execute.add_argument("--candidate", required=True)
        execute.add_argument("--batch-seconds", type=float,
                             default=t.seconds)
        execute.add_argument("--pairs", type=int)
        execute.add_argument("--samples", type=int)
        execute.add_argument("--layout-seed",
                             help="randomize code layout per fresh process")
        execute.add_argument("--only", action="append",
                             help="diagnostic subset; never a grid decision")
        execute.add_argument("--resume", action="store_true",
                             help="continue after an infrastructure failure")
        execute.add_argument("--authorize-measurements",
                             action="store_true")
        settings(execute)
        provenance(execute)
        replaced(execute)
        more = sub.add_parser("extend")
        more.add_argument("--grid", type=Path, required=True)
        more.add_argument("--output", type=Path, required=True)
        more.add_argument("--resume", action="store_true",
                          help="continue after an infrastructure failure")
        more.add_argument("--authorize-measurements", action="store_true")
        settings(more)
        provenance(more)
        replaced(more, False)
        check = sub.add_parser("replay")
        check.add_argument("--output", type=Path, required=True)
        check.add_argument("--repo", type=Path, default=repo)
        check.add_argument("--partial", action="store_true",
                           help="interrupted run: replay cells, no decision")
        ledger(check)
        provenance(check)
        replaced(check, False)
        return parser, sub

    def main(self, argv=None, extra=None):
        """`execute`, with a command that decided nothing printed as a
        `REFUSED` line on the standard error and the status `REFUSED`, which
        no grid has: a wrapper tells a command that measured nothing, or
        ended in no decision, from a grid that failed (1) or was not
        conclusive (2). A refusal (a ValueError, among them a checkout that
        changed and a lock that is held) is that line alone; any other error
        (a missing file, a full disk, a malformed record, a bug) has its
        traceback before it. An interrupt is not caught, and SIGTERM and
        SIGHUP are one, for every command (`terminating_as_interrupt`)."""
        with terminating_as_interrupt():
            try:
                return self.execute(argv, extra)
            except Exception as error:
                text = str(error)
                if not isinstance(error, ValueError):
                    traceback.print_exc()
                    text = "%s: %s" % (type(error).__name__, text)
                print("REFUSED: " + " ".join(text.split()),
                      file=sys.stderr, flush=True)
                return REFUSED

    def execute(self, argv=None, extra=None):
        """Dispatch. `extra` maps a task's own action to (configure the
        subparser, handler); the engine decides nothing of the kind."""
        parser, sub = self.parser()
        handlers = {}
        for name, (configure, handler) in (extra or {}).items():
            configure(sub.add_parser(name))
            handlers[name] = handler
        args = parser.parse_args(argv)
        if args.action in handlers:
            return handlers[args.action](args)
        status = self.dispatch(args)
        if args.action in ("run", "extend", "replay"):
            decided = args.output.resolve() / "decisions.json"
            if decided.exists():
                for line in class_report(self.t.label, a.load(decided)):
                    print(line)
        return status

    def dispatch(self, args):
        if args.action == "predeclare":
            a.require(not args.output.exists(),
                      "refusing to overwrite counts")
            a.require((args.revises is None) ==
                      (args.rescale is None and args.repilot is None),
                      "--revises goes with --rescale or --repilot")
            grid = args.grid.resolve()
            self.h.bind_from(args)
            if args.revises is None:
                counts = self.h.predeclare(grid)
            else:
                counts = self.h.revision(
                    grid, args.revises.resolve(), args.rescale, args.repilot)
            a.save(args.output, counts)
            return 0
        if args.action == "verify-counts":
            return self.h.verify_counts(args)
        if args.action == "prepare":
            return self.h.prepare(args)
        if args.action in ("pilot", "run", "extend"):
            a.require(args.authorize_measurements,
                      "exclusive window required")
        if args.action in ("pilot", "run"):
            a.exact_pin(args.baseline)
        if args.action == "pilot":
            return self.h.pilot(args)
        if args.action == "run":
            a.exact_pin(args.candidate)
            return self.h.run(args)
        if args.action == "extend":
            return self.h.extend(args)
        return self.h.replay(args)
