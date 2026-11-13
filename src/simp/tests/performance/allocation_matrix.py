#!/usr/bin/env python3
"""TASK29B paired cumulative-allocation matrix: run, replay, toolchain.

Measures raw mutator allocation words (patched private Poly/ML runtime) for
the 27 TASK29 cases at six sizes, baseline against candidate, with
baseline/baseline controls and fresh-process AB/BA pairs. One source-built
toolchain serves the whole grid; only the libpolyml DSO is swapped, via
LD_LIBRARY_PATH, and its binding is checked against the process maps. No
timing is measured. Failures and uncertainty stay failures and uncertainty:
no thresholds, outlier removal or subtraction. Output goes only below
--output; nothing here names a path inside the repository.

TASK37: the tasks `task37-matrix` (every TASK29 and TASK30 case, 306 cells,
size 10000 included) and `task37-client` (the 245 cells that `task31`
allocates) run 3 pairs per cell (Task.pairs, TASK37_PAIRS); the legacy tasks
keep 10. Counts are exact and no run ever saw a nondeterministic cell; the
determinism and control checks of allocation_analysis run on the 3 pairs
unchanged. `--pairs` defaults to the task's; fewer is a smoke. The cost of a
cell is proportional to its pairs (4 fresh processes per pair, one after the
other); `--jobs` runs cells, not processes of one cell, in parallel. The
`downstream_*` cells are not a task here (see task37_client).
"""
import argparse
from collections import Counter
import collections.abc
from concurrent.futures import FIRST_EXCEPTION, ThreadPoolExecutor, wait
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import queue
import shutil
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]  # the harness checkout; inputs are keyed relative to it
for sub in ("allocator-counter", "../compatibility"):
    sys.path.insert(0, str((HERE / sub).resolve()))
import acceptance as a
import allocation_analysis as an
import allocation_boundary as bd
import allocation_schema as sc
import evidence_bundle as bundle
import loading
import matrix_schema as ms
import path_schema
import private_runtime as pr
import run_paired as rp
import task29_gate as gate
import task30_cases
from prepare_patch import DEFAULT_SOURCE

ITERATIONS = HERE / "allocation_iterations.json"
BOUNDARY = HERE / "allocation_boundary.json"
SCHEMA = "task29b-matrix-v2"
CONTROLS_SCHEMA = "task29-managed-counter-controls-v4"
SIZES = a.SIZES
# Acceptance minimum of the pairs of a legacy task (TASK29B, TASK30, TASK31);
# fewer pairs is a smoke only. Every task has its own (Task.pairs): the
# TASK37 tasks use TASK37_PAIRS.
PAIRS = 10
TASK37_PAIRS = 3
# Job directories are named "j%02d" (make_job): more would give some private
# paths, hence PAIR_PRIVATE, another length than the rest of the grid.
MAX_JOBS = 100
# Equal-length private directory names, also used as the process selection
# label: neither a path nor a label length can change the startup words.
# Two baseline copies form the control.
SIDES = {"baseline": "sel-b0", "control": "sel-b1", "candidate": "sel-c0"}
EXPERIMENTS = {"candidate": ("baseline", "candidate"),
               "control": ("baseline", "control")}
FIXTURES = ("MatrixAllocation.sml", "MatrixSupport.sml")
# Every family installs the same two names in a private directory: the
# fixture as Performance.sml and the work-phase support as MatrixSupport.sml.
INSTALLED = ("Performance.sml", "MatrixSupport.sml")
# Selected modules every process elaborates privately (run_paired.validate
# demands the same of the performance fixture).
DIRECT_MODULES = ("Traverse", "simpLib")
# Everything that must be identical for every cell of one grid, and for the
# resume of its run: contents (seals, blobs, revisions, settings), never the
# location of a scratch tree.
GRID_KEYS = (
    "schema", "baseline", "candidate", "pairs", "runtime", "shim", "repo",
    "toolchain_head", "toolchain_products", "tools", "inputs", "controls",
    "sources", "revisions", "fixtures", "word_bytes", "canary",
    "iterations", "environment", "boundary", "harness")
# Path-valued header keys: where this run's private runtime and shim live
# and where its scratch trees stand. They differ between a run and its
# resume, so they are kept per run (in each cell's meta and inventory row)
# and their values are never compared; what stands at the first three is
# sealed by runtime and shim. TMPDIR is a place and not content: the runtime
# reads it to place the backing file of its memory mappings (osmemunix.cpp;
# tools-poly/poly/Mosml.sml reads it too), and the counter counts requested
# reservations, not where they are backed. A place has a length, though. The
# scratch tree stands below TMPDIR, so PAIR_PRIVATE, LD_LIBRARY_PATH and
# TASK29_ALLOC_SHIM change length with it, and path length can change
# startup words (see SIDES). A resume under a TMPDIR of another length would
# give cells of one grid private paths of different lengths, and published
# startup could differ between cells. So a resume needs the lengths of
# LENGTH_KEYS equal. The library path is the resolved scratch tree, which a
# symlinked TMPDIR can lengthen on its own.
PLACE_KEYS = ("shim_path", "library", "aliases", "tmpdir")
LENGTH_KEYS = ("tmpdir", "library")
# The launchers whose stored process receipts a controls receipt must
# replay under the current path schema: (receipt key, profile, program).
PATH_LAUNCHERS = (
    ("path", "native-rts", "path-controls.exe"),
    ("interpreter_path", "interpreter", "interpreter-path-controls.exe"),
    ("failure_path", "failure", "failure-path-controls.exe"))


class Family:
    """The allocation fixture of the cases that one timing fixture of
    matrix.json (`fixture`) runs: the files installed in every private
    directory as (file here, name there). A process loads only the selected
    simplifier sources, the installed files and the shared heap, so no
    family installs a shared closure, but for one with `closure` (the TASK37
    downstream cells, whose workloads use numLib, reduceLib and bossLib): it
    installs the shared client closure recompiled against the private
    simplifier (client_dependencies.py, as the timing path does; see
    Grid.make_closure). `timing` is the `fixture` of matrix.json whose cases
    it measures, when that is not the key it stands under."""

    def __init__(self, files, closure=False, timing=None):
        self.files = files
        self.closure = closure
        self.timing = timing

    @property
    def sources(self):
        return tuple(source for source, _ in self.files)


# One mechanism for every case: matrix.json's `fixture` of the case picks
# the allocation fixture; both bracket and count alike (MatrixAllocation.sml
# and ClientAllocation.sml share their driver text).
FAMILIES = {
    "MatrixPerformance.sml": Family(
        (("MatrixAllocation.sml", "Performance.sml"),
         ("MatrixSupport.sml", "MatrixSupport.sml"))),
    "ClientPerformance.sml": Family(
        (("ClientAllocation.sml", "Performance.sml"),
         ("MatrixSupport.sml", "MatrixSupport.sml")))}


# The downstream cases of ClientPerformance.sml have a fixture of their own
# (DownstreamAllocation.sml): it needs the shared closure, which the TASK31
# client cells (ClientAllocation.sml) must not load.
DOWNSTREAM_FAMILY = Family(
    (("DownstreamAllocation.sml", "Performance.sml"),
     ("MatrixSupport.sml", "MatrixSupport.sml")),
    closure=True, timing="ClientPerformance.sml")


class Task:
    """Which cases a grid measures and where its steady counts stand. The
    default task is TASK29B's; a header names another only by `task`.

    A case's sizes are those of its size set in matrix.json, without the
    `infeasible` (case, size) cells, which no gate can run. With `rows`
    the decisions also hold one pass/fail row per cell (see assemble).

    `pairs` is the acceptance minimum of fresh-process AB/BA pairs per
    cell (a run with fewer is a smoke). The legacy tasks keep PAIRS (10).
    The TASK37 tasks use TASK37_PAIRS (3): the allocation counts are exact
    (the private counter counts words, not time), and no run of TASK29B,
    TASK30 or TASK31 ever observed a nondeterministic count. Three pairs
    (six candidate and six control processes besides the baselines) still
    detect a cell that is nondeterministic, as the analysis compares every
    process of a cell, repeat by repeat, with the others and with the
    baseline/baseline control (allocation_analysis.control_identical and
    `deterministic`); more pairs would only lengthen the run (the cost is
    proportional to the pairs). `case_files` are the case-list modules of
    this checkout besides those every task binds, which the harness seals.
    `family` is the allocation fixture of a task whose cases are not run by
    the family of their matrix.json fixture (the family's `timing` is that
    fixture).
    """

    def __init__(self, name, label, cases, iterations, infeasible=(),
                 rows=False, pairs=PAIRS, case_files=(), family=None):
        self.name, self.label = name, label
        self.cases, self.iterations = tuple(cases), iterations
        self.infeasible, self.rows = frozenset(infeasible), rows
        sc.require(isinstance(pairs, int) and not isinstance(pairs, bool)
                   and pairs >= 2, "a task needs at least an AB and a BA "
                   "pair")
        self.pairs, self.case_files = pairs, tuple(case_files)
        fixtures = {ms.EXPECTED_CASES[c]["fixture"] for c in self.cases}
        sc.require(len(fixtures) == 1 and (
            fixtures <= set(FAMILIES) if family is None else
            fixtures == {family.timing}),
            "a task runs the cases of one fixture family")
        self.family = family or FAMILIES[fixtures.pop()]
        sc.require(self.infeasible <= {(c, n) for c in self.cases
                                       for n in self.every_size(c)},
                   "infeasible cells that are no cell of the task")

    @staticmethod
    def every_size(case):
        return tuple(ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]])

    def sizes(self, case):
        return tuple(n for n in self.every_size(case)
                     if (case, n) not in self.infeasible)


DEFAULT_TASK = "task29b"


def task31():
    """The TASK31 task. Its case list is read only when a process asks for
    this task: the other tasks' processes, their replays and the TASK30
    disposition never load task31_cases.py."""
    import task31_cases
    return Task("task31", "TASK31", task31_cases.CASES,
                HERE / "allocation_iterations_task31.json",
                task31_cases.INFEASIBLE_CELLS, rows=True,
                case_files=("task31_cases.py",))


def task37_matrix():
    """The TASK37 matrix task: every TASK29 and TASK30 cell (162 + 144),
    size 10000 included, at TASK37_PAIRS pairs. Lazy, like task31."""
    import task37_cases
    return Task("task37-matrix", "TASK37 matrix", task37_cases.MATRIX_CASES,
                HERE / "allocation_iterations_task37_matrix.json",
                rows=True, pairs=TASK37_PAIRS,
                case_files=task37_cases.FILES)


def task37_downstream():
    """The TASK37 downstream task: the 11 `downstream_*` cells, at
    TASK37_PAIRS pairs, in the fixture that needs the shared client
    closure. Lazy, like task31."""
    import task37_cases
    return Task("task37-downstream", "TASK37 downstream",
                task37_cases.DOWNSTREAM_CASES,
                HERE / "allocation_iterations_task37_downstream.json",
                rows=True, pairs=TASK37_PAIRS, case_files=task37_cases.FILES,
                family=DOWNSTREAM_FAMILY)


def task37_client():
    """The TASK37 client task: exactly the 245 cells that task31 allocates
    (the cells of the TASK31 case list but its infeasible ones), at
    TASK37_PAIRS pairs. Lazy, like task31. The `downstream_*` cells are
    the task `task37-downstream`."""
    import task37_cases
    return Task("task37-client", "TASK37 client", task37_cases.CLIENT_CASES,
                HERE / "allocation_iterations_task37_client.json",
                task37_cases.CLIENT_INFEASIBLE_CELLS, rows=True,
                pairs=TASK37_PAIRS, case_files=task37_cases.FILES)


class Tasks(collections.abc.Mapping):
    """The tasks by name. A task of `lazy` is built on its first lookup
    (and then kept), so that its module is imported by no other task's
    process; naming, iterating and testing membership build nothing."""

    def __init__(self, eager, lazy):
        self.made, self.lazy = dict(eager), dict(lazy)

    def __getitem__(self, name):
        if name not in self.made:
            if name not in self.lazy:
                raise KeyError(name)
            self.made[name] = self.lazy[name]()
        return self.made[name]

    def __contains__(self, name):
        return name in self.made or name in self.lazy

    def __iter__(self):
        return iter([*self.made, *(n for n in self.lazy
                                   if n not in self.made)])

    def __len__(self):
        return len(set(self.made) | set(self.lazy))


TASKS = Tasks({
    DEFAULT_TASK: Task(DEFAULT_TASK, "TASK29B", gate.CASES, ITERATIONS),
    "task30": Task("task30", "TASK30", task30_cases.CASES,
                   HERE / "allocation_iterations_task30.json")},
    {"task31": task31, "task37-matrix": task37_matrix,
     "task37-client": task37_client,
     "task37-downstream": task37_downstream})


def task_named(name):
    sc.require(name in TASKS, "unknown task: %r" % (name,))
    return TASKS[name]


def task_of(header):
    """The task a grid header (or inventory) belongs to."""
    return task_named(header.get("task", DEFAULT_TASK))


def keys(task=None):
    task = task or TASKS[DEFAULT_TASK]
    return [(case, size) for case in task.cases for size in task.sizes(case)]


def name_of(case, size):
    return "%s-%d" % (case, size)


def load_iterations(path=None, task=None):
    task = task or TASKS[DEFAULT_TASK]
    counts = a.load(path or task.iterations)
    sc.require(counts.get("schema") == "task29b-iterations-v1",
               "wrong predeclared counts")
    sc.require(isinstance(counts["repeats"], int) and counts["repeats"] >= 3,
               "need at least three steady repeats")
    steady = counts["steady"]
    sc.require(set(steady) == {name_of(*k) for k in keys(task)} and
               all(isinstance(v, int) and not isinstance(v, bool) and v > 0
                   for v in steady.values()), "incomplete predeclared counts")
    return counts


def trimmed(receipt):
    """Build logs are huge; keep exit status, hash and the tail."""
    text = receipt["stdout"]
    return dict(receipt, stdout=text[-2000:],
                stdout_truncated=len(text) > 2000)


def compact(value):
    data = (json.dumps(value, indent=2, allow_nan=False) + "\n").encode()
    return gzip.compress(data, mtime=0)


def write_receipt(folder, name, value):
    path = Path(folder) / (name + ".json.gz")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(compact(value))


def sealed_tree(root):
    return {str(p.relative_to(root)): rp.fingerprint(p)
            for p in sorted(Path(root).rglob("*")) if p.is_file()}


def source_map(inventory):
    """Selected sources by file name: identity of a checkout."""
    return {Path(i["git_path"]).name: {
        k: i[k] for k in ("sha256", "bytes", "git_blob")} for i in inventory}


def grid_digest(header):
    """Digest of every input shared by all cells of one grid."""
    shared = {k: header[k] for k in GRID_KEYS}
    if header.get("task", DEFAULT_TASK) != DEFAULT_TASK:
        shared["task"] = header["task"]  # TASK29B digests are unchanged
    if "structure" in header:  # so are those of grids without structure
        shared["structure"] = header["structure"]
    if "closure" in header:  # and those of grids without a shared closure
        shared["closure"] = header["closure"]
    data = json.dumps(shared, sort_keys=True, allow_nan=False).encode()
    return hashlib.sha256(data).hexdigest()


def places(header):
    """Where this run's private runtime and shim stand."""
    return {k: header[k] for k in PLACE_KEYS}


def binding(header, case, size, where=None):
    """What an archived cell's meta must say, from the grid header alone
    and the places of the run that measured it."""
    where = places(header) if where is None else where
    name = name_of(case, size)
    named = {"structure": header["structure"]} if "structure" in header \
        else {}
    if "closure" in header:
        named["closure"] = {k: header["closure"][k]
                            for k in ("changed", "sides")}
    return dict(
        named,
        case=case, size=size, steady=header["iterations"]["steady"][name],
        repeats=header["iterations"]["repeats"], pairs=header["pairs"],
        library=where["library"], aliases=where["aliases"],
        repo=header["repo"], shim=where["shim_path"],
        word_bytes=header["word_bytes"], sources=header["sources"],
        revisions=header["revisions"], fixtures=header["fixtures"],
        environment=header["environment"], tmpdir=where["tmpdir"],
        boundary_prefixes=header["boundary"]["manifest_prefixes"],
        grid=grid_digest(header))


def closure_record(result, directory):
    """The job-independent seal of one installed shared closure: its
    modules and roots and each product's seal. A descriptor holds the
    directory it was installed in, which is replaced; the other products
    are copies, whose seals are those of their source."""
    private = str(Path(directory).resolve(strict=True)).encode()
    products = {}
    for name, info in sorted(result["products"].items()):
        data = (Path(directory) / name).read_bytes().replace(
            private, b"@PRIVATE@")
        products[name] = dict(source=info["source"],
                              sha256=hashlib.sha256(data).hexdigest(),
                              bytes=len(data))
    return dict(modules=list(result["modules"]),
                roots=list(result["roots"]), products=products)


def row_binding(inventory, row):
    """binding() of one inventory row, with the places it was run at."""
    where = row.get("places")
    sc.require(isinstance(where, dict) and set(where) == set(PLACE_KEYS),
               "inventory row without the places it was measured at")
    return binding(inventory, row["case"], row["size"], where)


def place_lengths(where):
    """Path lengths that must agree across cells of one grid."""
    return {k: len(where[k]) if k in where else None for k in LENGTH_KEYS}


def changed_settings(old, new):
    """Grid keys by which two headers differ (paths excluded, but not their
    lengths: those are listed as `<key>-length`)."""
    return ([k for k in GRID_KEYS + ("acceptance_pairs",)
             if old.get(k) != new[k]] +
            [k for k in ("task",) if old.get(k, DEFAULT_TASK) !=
             new.get(k, DEFAULT_TASK)] +
            [k for k in ("structure", "closure")
             if old.get(k) != new.get(k)] +
            [k + "-length" for k in LENGTH_KEYS
             if place_lengths(old).get(k) != place_lengths(new)[k]])


def library_names(libraries):
    """Library seals by file name: the paths differ between builds."""
    names = {}
    for raw, info in libraries.items():
        name = Path(raw).name
        sc.require(name not in names, "ambiguous library name: " + name)
        names[name] = {k: info[k] for k in ("sha256", "bytes")}
    return names


def replay_path_controls(data):
    """The path launchers' stored process receipts, validated again by the
    current path schema: an older, weaker receipt of the same patch and
    tree does not pass guards added since."""
    for key, profile, program in PATH_LAUNCHERS:
        rows = [c for c in data["commands"]
                if Path(c["command"][0]).name == program and
                c["command"][1:] == list(path_schema.FLAGS[profile])]
        sc.require(len(rows) == 1,
                   "controls receipt lacks the %s process" % program)
        try:
            found = path_schema.validate_receipt(rows[0], profile, timeout=1)
        except ValueError as error:
            raise sc.InvalidAllocation(
                "controls receipt fails the current path schema (%s): %s"
                % (program, error))
        sc.require(json.loads(json.dumps(found)) ==
                   data[key + "_observations"],
                   "controls receipt observations differ from a replay")


def controls_facts(data, runtime, tree):
    """What a controls receipt itself establishes (no checkout needed): a
    successful run on this very private runtime, from a clean, committed
    harness that equals the candidate outside the performance area, over a
    recorded HOL and native build lineage of that harness head, whose
    path-launcher processes replay under the current schema.

    Strict: a missing field is a rejection, and so is any seal mismatch."""
    try:
        sc.require(data["schema"] == CONTROLS_SCHEMA and
                   data["success"] is True and "failure" not in data,
                   "not a successful managed-counter controls receipt")
        sc.require(data["runtime"] == runtime,
                   "controls receipt was produced for a different runtime "
                   "(sha256/bytes differ from this grid's private DSO)")
        head, harness, lineage = data["head"], data["harness"], data[
            "lineage"]
        sc.require(harness["head"] == head and harness["dirty"] is False,
                   "controls receipt was not produced from a clean, "
                   "committed harness")
        sc.require(harness["tree_outside_performance"] == tree,
                   "controls harness differs from the candidate outside "
                   "the performance area")
        sc.require(lineage["hol_snapshot"] == head and
                   lineage["hol_products"] and lineage["native_products"],
                   "controls receipt carries no HOL lineage of its harness")
        replay_path_controls(data)
        return dict(
            runtime=runtime, head=head, tree=tree,
            native_configuration=hashlib.sha256(
                lineage["native_configuration"].encode()).hexdigest(),
            libraries=library_names(data["instrumented_libraries"]))
    except (KeyError, TypeError, AttributeError, IndexError) as error:
        raise sc.InvalidAllocation(
            "malformed controls receipt: %r" % (error,))


def controls_receipt(path, runtime, tree, libraries, configuration):
    """The controls receipt of this grid: controls_facts, every harness file
    of this checkout sealed exactly as in the receipt, and the instrumented
    libraries and native configuration of the receipt's build equal to the
    matrix toolchain's (libraries: raw path to seal; configuration: the
    config.h text)."""
    path = Path(path).resolve(strict=True)
    data = a.load(path)
    facts = controls_facts(data, runtime, tree)
    try:
        rows = {}
        for key, seal in data["inputs"].items():
            where = Path(key)
            rows.setdefault((where.parent.name, where.name), []).append(seal)
    except (KeyError, AttributeError, TypeError) as error:
        raise sc.InvalidAllocation(
            "malformed controls receipt: %r" % (error,))
    for harness in pr.harness_inputs():
        sc.require(rows.get((harness.parent.name, harness.name)) ==
                   [a.seal(harness)],
                   "controls receipt used a different " + harness.name)
    sc.require(facts["libraries"] == library_names(libraries),
               "controls receipt linked other instrumented libraries than "
               "this toolchain")
    sc.require(facts["native_configuration"] == hashlib.sha256(
        configuration.encode()).hexdigest(),
        "controls receipt used another native Poly/ML configuration")
    return dict(facts, receipt=a.seal(path), file="controls-receipt.json" +
                (".gz" if path.suffix == ".gz" else ""))


def controls_copy(root, inventory):
    """The controls receipt kept in the output, checked again from the
    archives' side: its seal, and every fact the header recorded."""
    try:
        controls = inventory["controls"]
        sc.require(controls["runtime"] == inventory["runtime"],
                   "controls receipt belongs to another runtime")
        copy = a.safe_child(root, controls["file"])
        sc.require(a.seal(copy) == controls["receipt"],
                   "controls receipt copy changed")
        facts = controls_facts(a.load(copy), inventory["runtime"],
                               controls["tree"])
        sc.require(all(controls.get(k) == v for k, v in facts.items()),
                   "controls receipt facts differ from the inventory")
    except (KeyError, TypeError) as error:
        raise sc.InvalidAllocation(
            "malformed controls entry of the inventory: %r" % (error,))


def harness_files(task=None):
    """Files of this checkout that decide a measurement, as paths: the
    driver and its helpers, the fixtures installed in every private
    directory, the iteration counts of `task` and the reviewed boundary."""
    task = task or TASKS[DEFAULT_TASK]
    paired = sorted(p for p in (HERE.parent / "compatibility" /
                                "paired").iterdir() if p.is_file())
    inputs = [HERE / n for n in (
        "allocation_matrix.py", "allocation_schema.py",
        "allocation_analysis.py", "allocation_boundary.py",
        "allocation_boundary.json", task.iterations.name,
        *task.family.sources, "acceptance.py",
        "evidence_bundle.py", "loading.py", "task29_gate.py",
        "task30_cases.py", *task.case_files,
        "path_schema.py", "performance_schema.py", "matrix_schema.py",
        "audit_evidence.py", "summarize.py",
        *(("client_dependencies.py",) if task.family.closure else ()))]
    inputs += [HERE / "allocator-counter" / n for n in (
        "private_runtime.py", "bracket.c", "managed_alloc_counter.h",
        "SOURCE_SHA256.json", "PATCHED_SHA256.json",
        "managed-allocation.patch.gz", "check_patch.py",
        "prepare_patch.py")]
    inputs += [HERE.parent / "compatibility" / "run_paired.py"] + paired
    fixtures = [HERE / n for n in task.family.sources] + [
        p for p in paired if p.suffix == ".sml"]
    return inputs, fixtures


def harness_binding(root, candidate, inputs, fixtures):
    """Bind the driver and fixtures that run to commits: the checkout they
    are in is clean (so each file is its committed blob), equal to the
    candidate outside the performance area, and every fixture installed in
    the private directories is the candidate's own blob."""
    root = Path(root).resolve(strict=True)
    identity = pr.harness_identity(root, candidate)

    def relative(files):
        return sorted({Path(p).resolve(strict=True).relative_to(
            root).as_posix() for p in files})
    committed = bd.candidate_blobs(root, identity["head"], relative(inputs))
    sc.require(set(committed) == set(relative(inputs)),
               "a harness input is not committed")
    for name, blob in committed.items():
        sc.require(a.git(root, "hash-object", name) == blob,
                   "harness input differs from its commit: " + name)
    wanted = bd.candidate_blobs(root, candidate, relative(fixtures))
    sc.require(wanted == {n: committed[n] for n in relative(fixtures)},
               "a fixture is not the candidate's committed blob")
    return dict(identity, blobs=committed, fixtures=relative(fixtures))


class Job:
    """Private selection directories of one worker (never shared)."""

    def __init__(self, root):
        self.root = root
        self.dirs = {k: root / v for k, v in SIDES.items()}
        self.sources, self.inventory, self.tree = {}, {}, {}


class Grid:
    """Locked, sealed environment: toolchain, private runtime, shim."""

    task = TASKS[DEFAULT_TASK]
    closure = None

    def __init__(self, args):
        self.args = args
        self.task = task_named(getattr(args, "task", DEFAULT_TASK))
        self.pairs = self.task.pairs if args.pairs is None else args.pairs
        self.repo = args.repo.resolve(strict=True)
        self.report = dict(commands=[])
        self.scratch = None
        self.ready = False
        self.header = {}

    def bind_harness(self, candidate):
        """The harness binding of this grid's task, with the input and
        fixture files it covers."""
        inputs, fixtures = harness_files(self.task)
        return (harness_binding(HERE.parents[3], candidate, inputs, fixtures),
                inputs, fixtures)

    def run(self, command, cwd=None, runtime_env=None):
        env = self.env if runtime_env is None else runtime_env
        receipt = loading.execute(command, cwd or self.hol, env,
                                  self.args.timeout, self.fds)
        self.report["commands"].append(trimmed(dict(
            receipt, environment=dict(env))))
        sc.require(receipt["exit"] == 0 and not receipt["timed_out"],
                   "failed command: " + str(command))
        return receipt

    def __enter__(self):
        args = self.args
        a.exact_pin(args.baseline)
        a.exact_pin(args.candidate)
        sc.require(args.baseline != args.candidate,
                   "candidate equals baseline: a vacuous comparison")
        sc.require(args.authorize_experimental_runtime and args.timeout > 0,
                   "authorization and positive timeout required")
        sc.require(sys.platform == "linux" and platform.machine() ==
                   "aarch64", "unsupported host")
        self._lock = a.serial_lock(self.repo)
        self.fds = self._lock.__enter__()
        try:
            self.prepare()
        except BaseException:
            self.__exit__(*sys.exc_info())
            raise
        return self

    def checkout(self, side, directory):
        """Selected sources of one side extracted from git into directory."""
        ref = self.args.candidate if side == "candidate" \
            else self.args.baseline
        directory.mkdir()
        rev = rp.git(self.repo, "rev-parse", ref + "^{commit}").decode(
            ).strip()
        return rev, rp.extract(self.repo, rev, directory)

    def prepare(self):
        args = self.args
        root = args.toolchain.resolve(strict=True)
        lineage = a.load(root / "lineage.json")
        sc.require(lineage.get("schema") == "task29b-toolchain-v1" and
                   lineage.get("success") is True and
                   lineage.get("head") == args.candidate,
                   "toolchain not built at the candidate commit")
        built = lineage["lineage"]
        self.native_configuration = built["native_configuration"]
        pr.reject_compact32(self.native_configuration)
        self.hol = root / "hol-source"
        products, native = built["hol_products"], built["native_products"]
        loading.check_seals(products)
        loading.check_seals(native)
        self.toolchain_seals = self.check_toolchain_sources(built)
        # Refuse an unreviewed difference between the sides, and a harness
        # that is not what its commit says, before anything is built.
        self.boundary = bd.resolve(self.repo, args.baseline, args.candidate,
                                   pr.HOL_SEQUENCE, BOUNDARY)
        self.harness, inputs, fixtures = self.bind_harness(args.candidate)
        self.env = dict(
            PATH=pr.PATH, HOME="/nonexistent",
            TMPDIR=os.environ.get("TMPDIR", "/tmp"), HOLDIR=str(self.hol),
            TERM="dumb", LC_ALL="C", TZ="UTC", CONFIG_SITE="/dev/null")
        for key, name in (("CC", "gcc"), ("CXX", "g++")):
            self.env[key] = shutil.which(name, path=self.env["PATH"]) or ""
            sc.require(bool(self.env[key]), "missing compiler: " + name)
        # Keyed by path relative to the harness checkout: the content of a
        # checkout does not depend on where it stands.
        self.inputs = {Path(p).resolve(strict=True).relative_to(
            ROOT).as_posix(): a.seal(p) for p in inputs}
        # Selected fixtures as installed in every private directory.
        family = self.task.family
        self.fixtures = {target: a.seal(HERE / source)
                         for source, target in family.files}
        self.fixtures.update({p.name: a.seal(p) for p in fixtures
                              if p.name not in family.sources})
        # Same files the timing runs seal: heap, project file, compiler and
        # every library of the process; libraries are added after binding.
        self.tools = dict(products, **native)
        for name in ("bin/hol.state.min", "holproject.toml"):
            self.tools[str(self.hol / name)] = a.seal(self.hol / name)
        patched = pr.verify_source(args.source)
        # Compilers and tools resolve on the fixed PATH and are sealed.
        self.tools.update(pr.seal_tools(self.env, self.run))
        self.scratch = Path(tempfile.mkdtemp(
            prefix="task29b-", dir=self.env["TMPDIR"])).resolve()
        report = self.report
        self.revisions, self.sources = {}, {}
        for side in SIDES:
            self.revisions[side], inventory = self.checkout(
                side, self.scratch / ("probe-" + side))
            self.sources[side] = source_map(inventory)
        self.check_sides()
        self.closure = self.make_closure() if self.task.family.closure \
            else None
        lib, _, self.source_seals = pr.build_runtime(
            args.source, self.scratch, self.run, report, patched)
        self.lib = lib.resolve(strict=True)
        self.aliases = sorted(str(p) for p in self.lib.parent.iterdir()
                              if p.name.startswith("libpolyml.so") and
                              p.resolve(strict=True) == self.lib and
                              p != self.lib)
        run_env = dict(self.env, LD_LIBRARY_PATH=str(self.lib.parent))
        self.run_env = run_env
        self.libraries = pr.bind_runtime(self.run, self.hol, self.lib,
                                         run_env, report)
        self.tools.update({raw: {k: info[k] for k in ("sha256", "bytes")}
                           for raw, info in self.libraries.items()})
        fixture = self.scratch / "fixture"
        fixture.mkdir()
        shim, report["shim_libraries"] = pr.build_shim(
            self.env, self.run, fixture, self.lib, run_env, report)
        self.shim = shim
        report["shim"] = a.seal(shim)
        self.header = self.make_header(lineage["head"], products)
        self.ready = True

    def install_private(self, directory, sources):
        """The fixtures of the task in a private directory of one side (the
        selected sources, `sources`, already checked out). A family with a
        shared closure also gets it, as the timing path installs it
        (client_dependencies.install); its result is returned, else None."""
        rp.install_fixtures(directory)
        for source, target in self.task.family.files:
            shutil.copyfile(HERE / source, directory / target)
        with (directory / "Holmakefile").open("a") as out:
            out.write("\npaired.exe: Performance.uo\n")
        if not self.task.family.closure:
            return None
        from client_dependencies import install
        return install(self.hol, directory,
                       {Path(s["git_path"]).stem for s in sources})

    def make_closure(self):
        """What the shared closure of this grid is, for the sides that run:
        installed once per side in a scratch directory. Every job must
        install exactly this (see make_job). The header records, per side,
        the modules recompiled, the roots and the seal of every installed
        product (the descriptors, which name their directory, with that
        name replaced), the paths that differ between baseline and
        candidate (a process may load no shared file among them), and the
        shared inputs read, which are in the toolchain and sealed again at
        the end."""
        sides, inputs = {}, {}
        for side in SIDES:
            directory = self.scratch / ("closure-" + side)
            _, sources = self.checkout(side, directory)
            result = self.install_private(directory, sources)
            sides[side] = closure_record(result, directory)
            for path, stamp in result["inputs"].items():
                sc.require(inputs.setdefault(path, stamp) == stamp,
                           "closure input changed between sides")
        sc.require(sides["control"] == sides["baseline"],
                   "control closure is not a copy of the baseline's")
        return dict(changed=bd.changed_paths(
            self.repo, self.args.baseline, self.args.candidate),
            sides=sides, inputs=inputs)

    def check_toolchain_sources(self, built):
        """The tracked HOL sources (as the build left them) and sigobj, as
        sealed by the toolchain build, are what stands there now."""
        try:
            changed = built["hol_source_changes"]
            seals = {str(self.hol / name): changed.get(name, seal)
                     for name, seal in built["hol_source_inputs"].items()}
            seals.update({str(self.hol / name): seal
                          for name, seal in built["hol_sigobj"].items()})
            sc.require(built["hol_snapshot"] == self.args.candidate and
                       seals, "toolchain lineage is not that of the "
                       "candidate")
        except (KeyError, AttributeError, TypeError) as error:
            raise sc.InvalidAllocation(
                "toolchain lineage lacks %r: rebuild the toolchain" % (
                    error,))
        loading.check_seals(seals)
        return seals

    def check_sides(self):
        """The three sides resolved as promised: a real candidate, and a
        control that is the baseline's own copy."""
        sc.require(self.revisions["candidate"] != self.revisions["baseline"],
                   "candidate resolves to the baseline commit")
        sc.require(self.sources["control"] == self.sources["baseline"] and
                   self.revisions["control"] == self.revisions["baseline"],
                   "control is not a copy of the baseline")

    def make_header(self, toolchain_head, products):
        """Everything shared by all cells of this grid, with the controls
        receipt that must belong to this very private runtime."""
        args, report = self.args, self.report
        tree = pr.tree_outside_performance(self.repo,
                                           self.revisions["candidate"])
        controls = controls_receipt(args.controls_receipt, report["runtime"],
                                    tree, self.libraries,
                                    self.native_configuration)
        # The private runtime stands in a scratch tree: its path-valued
        # entries are places (see PLACE_KEYS); its content is `runtime`.
        tools = {k: v for k, v in self.tools.items()
                 if not Path(k).is_relative_to(self.lib.parent)}
        named = {} if self.task.name == DEFAULT_TASK else dict(
            task=self.task.name)
        named["structure"] = sc.STRUCTURE
        if self.closure is not None:
            named["closure"] = self.closure
        return dict(
            named, schema=SCHEMA, baseline=args.baseline,
            candidate=args.candidate,
            pairs=self.pairs, runtime=report["runtime"], shim=report["shim"],
            shim_path=str(self.shim), library=str(self.lib),
            aliases=self.aliases, repo=str(self.hol),
            toolchain_head=toolchain_head, toolchain_products=products,
            tools=tools, inputs=self.inputs, controls=controls,
            sources=self.sources, revisions=self.revisions,
            fixtures=self.fixtures, word_bytes=sc.WORD_BYTES,
            canary=dict(array=sc.CANARY_ARRAY, words=sc.CANARY),
            environment={k: v for k, v in self.env.items()
                         if k != "TMPDIR"}, tmpdir=self.env["TMPDIR"],
            boundary=self.boundary,
            harness=self.harness,
            acceptance_pairs=self.pairs >= self.task.pairs,
            outliers="none removed",
            decision="no allowance; no subtraction; see allocation_analysis")

    def make_job(self, index):
        job = Job(self.scratch / ("j%02d" % index))
        job.root.mkdir()
        for side, directory in job.dirs.items():
            rev, sources = self.checkout(side, directory)
            sc.require(rev == self.revisions[side] and
                       source_map(sources) == self.sources[side],
                       "checkout differs from the grid's sources")
            installed = self.install_private(directory, sources)
            if self.task.family.closure:
                sc.require(closure_record(installed, directory) ==
                           self.closure["sides"][side],
                           "installed closure differs from the grid's")
            job.inventory[side] = sources
        job.names = {Path(s["git_path"]).stem for v in job.inventory.values()
                     for s in v}
        for side, directory in job.dirs.items():
            cmd = [str(self.hol / "bin/Holmake"), "--no-project", "--no-cache",
                   "--no_prereqs", "--holstate=" +
                   str(self.hol / "bin/hol.state0"), "-C", str(directory),
                   "-j1", "paired.exe"]
            self.run(cmd, job.root)
            text = (directory / "paired.exe").read_text()
            sc.require(str(self.hol / "bin/hol") + " --gcthreads=1 run " in
                       text and "--holstate=" + str(self.hol /
                       "bin/hol.state0") in text,
                       "unexpected launcher runtime/options")
            job.tree[side] = sealed_tree(directory)
            for f in directory.rglob("*"):
                if f.is_file():
                    job.sources[str(f.resolve())] = rp.fingerprint(f)
        return job

    def process(self, job, experiment, side, case, size, pair, steady,
                repeats):
        """One fresh process; a rejected one is kept with its reason."""
        directory = job.dirs[side]
        selection = SIDES[side]
        env = dict(
            self.run_env, PAIR_SELECTION=selection, PAIR_FIXTURE="performance",
            PAIR_CONTROL="none", PAIR_PRIVATE=str(directory),
            PAIR_TARGET="Performance", PERF_CASE=case, PERF_SIZE=str(size),
            ALLOC_STEADY=str(steady), ALLOC_REPEATS=str(repeats),
            TASK29_ALLOC_SHIM=str(self.shim))
        receipt = loading.execute([str(directory / "paired.exe")], directory,
                                  env, self.args.timeout, self.fds)
        receipt.update(experiment=experiment, side=side, selection=selection,
                       pair=pair, environment=dict(env))
        try:
            events = rp.parse_events(receipt["stdout"])
            _, observed = sc.parse(events, case=case, size=size,
                                   steady=steady, repeats=repeats,
                                   structure=self.header.get("structure"))
            sc.check_runtime(receipt["stdout"], str(self.lib), self.aliases)
            result = rp.validate(
                receipt, selection=selection, fixture="performance",
                control="none", private=directory, repo=self.hol,
                private_names=job.names, flavor="baseline",
                signature="pass", source_hashes=job.sources,
                expected_observations=observed)
            receipt["paths"] = result["paths"]
            receipt["accepted"] = True
        except (ValueError, OSError) as error:
            receipt.update(accepted=False, rejection=str(error))
        return receipt

    def cell(self, job, case, size, root, counts):
        """All 4*pairs fresh processes of one cell, archived and replayed."""
        name = name_of(case, size)
        steady = counts["steady"][name]
        bind = binding(dict(self.header, iterations=counts), case, size)
        meta = dict(bind, schema=SCHEMA, rejected=None)
        rejected, started = None, time.perf_counter()
        with tempfile.TemporaryDirectory(
                prefix="task29b-cell-", dir=self.env["TMPDIR"]) as tmp:
            folder = Path(tmp) / name
            try:
                for experiment, sides in EXPERIMENTS.items():
                    for pair in range(self.pairs):
                        order = sides if pair % 2 == 0 else sides[::-1]
                        for position, side in enumerate(order):
                            receipt = self.process(
                                job, experiment, side, case, size, pair,
                                steady, counts["repeats"])
                            receipt["position"] = position
                            write_receipt(folder / experiment, "pair-%02d-%s" %
                                          (pair, SIDES[side]), receipt)
                            sc.require(receipt["accepted"],
                                       receipt.get("rejection", ""))
                self.audit(job, folder)
            except (ValueError, OSError) as error:
                rejected = str(error)
            meta["rejected"] = rejected
            write_receipt(folder, "meta", meta)
            archive = root / (name + ".json.xz")
            partial = root / (name + ".json.xz.partial")
            count = bundle.pack(folder, partial)
            restored = Path(tmp) / "roundtrip"
            sc.require(bundle.unpack(partial, restored) == count,
                       "transport count mismatch")
            for path in folder.rglob("*"):
                if path.is_file():
                    sc.require(a.seal(path) == a.seal(
                        restored / path.relative_to(folder)),
                        "transport changed original bytes")
            partial.rename(archive)
            analysis = None
            if not rejected:
                # A protocol failure only the offline replay sees is a
                # rejected cell like any other, never an aborted run.
                try:
                    analysis = replay_cell(archive, bind)["record"]
                except (ValueError, OSError) as error:
                    rejected = str(error)
        return dict(case=case, size=size, steady=steady,
                    wall=round(time.perf_counter() - started, 1),
                    archive=archive.name, places=places(self.header),
                    seal=a.seal(archive), files=count, rejected=rejected,
                    status=cell_status(analysis))

    def audit(self, job, folder):
        """Sources, products and shared inputs unchanged by the processes."""
        for side, directory in job.dirs.items():
            sc.require(sealed_tree(directory) == job.tree[side],
                       "private selection changed during cell: " + side)
        seen = {}
        for path in sorted(Path(folder).rglob("pair-*.json.gz")):
            for logical, info in a.load(path)["paths"].items():
                seen[info["physical"]] = {k: info[k] for k in ("sha256",
                                                               "bytes")}
                for product, expected in info["related_products"].items():
                    seen[product] = expected
        for physical, expected in seen.items():
            sc.require(rp.fingerprint(Path(physical)) == expected,
                       "loaded source/product changed during cell")

    def reseal(self):
        """Everything sealed at the start, sealed again at the end."""
        loading.check_seals({str(ROOT / k): v
                             for k, v in self.inputs.items()})
        loading.check_seals(self.tools)
        loading.check_seals(self.toolchain_seals)
        loading.check_seals(self.source_seals)
        if self.closure is not None:
            loading.check_seals(self.closure["inputs"])
        sc.require(a.seal(self.lib) == self.report["runtime"],
                   "runtime changed")
        sc.require(a.seal(self.shim) == self.report["shim"], "shim changed")
        after = loading.library_inputs(self.run(
            ["ldd", str(self.hol / "bin/hol")], runtime_env=self.run_env))
        sc.require(after == self.libraries, "instrumented linkage drift")
        shim = loading.library_inputs(self.run(
            ["ldd", str(self.shim)], runtime_env=self.run_env))
        sc.require(shim == self.report["shim_libraries"],
                   "shim linkage drift")

    def __exit__(self, *exc):
        try:
            if exc[0] is None and self.ready:
                self.reseal()
        finally:
            try:
                if self.scratch is not None:
                    shutil.rmtree(self.scratch, ignore_errors=True)
            finally:
                self._lock.__exit__(None, None, None)
        return False


def load_receipts(folder):
    receipts = {}
    for experiment in EXPERIMENTS:
        for path in sorted((Path(folder) / experiment).glob("pair-*.json.gz")):
            receipts[experiment, path.name] = a.load(path)
    return receipts


def check_protocol(receipt, meta, events):
    """The loader's ordered inventories, replayed from archived stdout."""
    side = receipt["side"]
    private = receipt["environment"]["PAIR_PRIVATE"]
    repo = meta["repo"]
    sc.require(events[:3] == [["begin", SIDES[side], "performance", "none"],
                              ["cwd", private], ["holdir", repo, repo]],
               "wrong archived loader header")
    sc.require(len(events) > 6 and events[3][0] == "preloaded" and
               len(events[3]) == 2, "missing preloaded-module inventory")
    names = {Path(n).stem for n in meta["sources"][side]}
    sc.require(not (names & set(events[3][1].split(","))),
               "selected implementation preloaded in shared heap")
    index, heaps = 4, []
    while index < len(events) and events[index][0] == "heapfile":
        sc.require(len(events[index]) == 2, "invalid heap inventory")
        heaps.append(events[index][1])
        index += 1
    sc.require(heaps and len(set(heaps)) == len(heaps),
               "missing/duplicate heap inventory")
    sc.require(events[index:index + 2] == [
        ["search", private], ["search", str(Path(repo) / "sigobj")]],
        "wrong archived search paths")
    sc.require(events[-1] == ["end", "pass", "1"],
               "missing or wrong completion/test count")
    used, completed, loaded, pending, final = [], [], [], None, False
    for event in events[index + 2:-1]:
        kind = event[0]
        if kind == "use":
            sc.require(not final and len(event) == 2 and pending is None,
                       "unordered archived source use")
            pending = event[1]
            used.append(pending)
        elif kind == "used":
            sc.require(not final and len(event) == 2 and pending == event[1],
                       "unmatched archived source completion")
            completed.append(pending)
            pending = None
        elif kind in ("observation", "check"):
            sc.require(not final, "observation after loaded inventory")
        elif kind == "loaded":
            sc.require(len(event) == 2, "invalid loaded inventory")
            final = True
            loaded.append(event[1])
        else:
            raise sc.InvalidAllocation("unknown archived event: " + kind)
    sc.require(pending is None and loaded and len(set(loaded)) ==
               len(loaded) and set(loaded) == set(heaps + completed) and
               set(receipt["paths"]) == set(used + loaded),
               "incomplete archived source inventory")
    for target in INSTALLED:
        sc.require(str(Path(private) / target) in completed,
                   "fixture never completed: " + target)
    for name in DIRECT_MODULES:
        sc.require(str(Path(private) / (name + ".sml")) in completed,
                   "selected implementation not elaborated: " + name)


def under_prefix(repo, path, prefixes):
    """The manifest prefix a path of the toolchain lies under, or None. A
    prefix is a directory the subject cannot load from; a process that
    loads a file there would make the boundary a false pass. A path outside
    the toolchain is refused, never judged to be under no prefix."""
    try:
        below = Path(path).relative_to(repo).as_posix()
    except ValueError:
        raise sc.InvalidAllocation(
            "shared input outside the toolchain: %s" % (path,))
    return next((p for p in prefixes if below.startswith(p)), None)


def changed_input(repo, path, changed):
    """Whether a file of the toolchain is among the changed paths of the
    comparison. A path outside the toolchain is refused."""
    try:
        return Path(path).relative_to(repo).as_posix() in set(changed)
    except ValueError:
        raise sc.InvalidAllocation(
            "shared input outside the toolchain: %s" % (path,))


def check_receipt(receipt, meta, experiment):
    """Offline protocol and provenance checks of one archived process."""
    sc.require(receipt["accepted"] is True and receipt["exit"] == 0 and
               receipt["timed_out"] is False, "failed process")
    side = receipt["side"]
    sides = EXPERIMENTS[experiment]
    sc.require(side in sides and receipt["experiment"] == experiment and
               receipt["selection"] == SIDES[side], "wrong selection")
    pair = receipt["pair"]
    sc.require(isinstance(pair, int) and 0 <= pair < meta["pairs"],
               "wrong pair index")
    want = sides if pair % 2 == 0 else sides[::-1]
    sc.require(want[receipt["position"]] == side, "not AB/BA order")
    env = receipt["environment"]
    private = env["PAIR_PRIVATE"]
    # The whole environment of the process, not a filtered subset of it.
    sc.require(env == dict(
        meta["environment"], TMPDIR=meta["tmpdir"],
        LD_LIBRARY_PATH=str(Path(meta["library"]).parent),
        PAIR_SELECTION=SIDES[side], PAIR_FIXTURE="performance",
        PAIR_CONTROL="none", PAIR_PRIVATE=private, PAIR_TARGET="Performance",
        PERF_CASE=meta["case"], PERF_SIZE=str(meta["size"]),
        ALLOC_STEADY=str(meta["steady"]), ALLOC_REPEATS=str(meta["repeats"]),
        TASK29_ALLOC_SHIM=meta["shim"]) and
        Path(private).name == SIDES[side], "wrong environment binding")
    events = rp.parse_events(receipt["stdout"])
    structure = meta.get("structure")
    brackets, found = sc.parse(events, case=meta["case"], size=meta["size"],
                               steady=meta["steady"],
                               repeats=meta["repeats"], structure=structure)
    sc.check_runtime(receipt["stdout"], meta["library"], meta["aliases"])
    check_protocol(receipt, meta, events)
    source, repo = meta["sources"][side], Path(meta["repo"])
    closure = meta.get("closure", {"sides": {}})["sides"].get(side, {})
    for logical, info in receipt["paths"].items():
        physical = Path(info["physical"])
        seal = {k: info[k] for k in ("sha256", "bytes")}
        if physical.is_relative_to(private):
            want = source.get(physical.name) or meta["fixtures"].get(
                physical.name) or closure.get("products", {}).get(
                    physical.relative_to(private).as_posix())
            sc.require(want is not None and
                       seal == {k: want[k] for k in ("sha256", "bytes")},
                       "wrong selected source: " + physical.name)
        else:
            sc.require(physical.is_relative_to(repo) and not
                       physical.is_relative_to(repo / "src/simp"),
                       "shared input outside the toolchain: " + logical)
            # The name it was loaded by, normalized (a symlink under a
            # prefix is under it whatever it points to), the file it is and
            # every product beside it.
            for product in (Path(os.path.normpath(logical)), physical,
                            *map(Path, info["related_products"])):
                if "closure" in meta:
                    # The cases load shared modules that the manifest's
                    # prefixes claim nothing loads from; what must hold
                    # is that no loaded file differs between the sides.
                    sc.require(
                        not changed_input(repo, product,
                                          meta["closure"]["changed"]),
                        "shared input differs between baseline and "
                        "candidate: " + logical)
                    continue
                prefix = under_prefix(repo, product, meta["boundary_prefixes"])
                sc.require(prefix is None,
                           "shared input under the boundary prefix %s: %s"
                           % (prefix, logical))
    return sc.observation(brackets, meta["steady"],
                          sc.work(found, structure))


def shared_inputs(receipt):
    """Loaded inputs outside the private directory, with their products."""
    private = receipt["environment"]["PAIR_PRIVATE"] + "/"
    return {logical: {k: info[k] for k in ("physical", "sha256", "bytes",
                                           "related_products")}
            for logical, info in receipt["paths"].items()
            if not info["physical"].startswith(private)}


def merge_shared(known, new):
    for logical, sealed in new.items():
        sc.require(known.setdefault(logical, sealed) == sealed,
                   "shared input changed between processes")


def cell_data(folder, bind):
    """Validated observations of one unpacked cell. A malformed archive
    (missing field, wrong type) is a rejection, never a crash."""
    try:
        return checked_cell(folder, bind)
    except (KeyError, TypeError, IndexError, AttributeError) as error:
        raise sc.InvalidAllocation("malformed archive: %r" % (error,))


def checked_cell(folder, bind):
    meta = a.load(Path(folder) / "meta.json.gz")
    sc.require(meta["rejected"] is None, "unresolved cell")
    sc.require(meta == dict(bind, schema=SCHEMA, rejected=None),
               "cell measured under different inputs or settings")
    sc.require(meta["sources"]["control"] == meta["sources"]["baseline"] and
               meta["revisions"]["control"] ==
               meta["revisions"]["baseline"],
               "control is not a copy of the baseline")
    receipts = load_receipts(folder)
    sc.require(len(receipts) == 4 * meta["pairs"], "missing process receipt")
    data = {e: [dict() for _ in range(meta["pairs"])] for e in EXPERIMENTS}
    shared = {}
    for (experiment, _), receipt in receipts.items():
        side, pair = receipt["side"], receipt["pair"]
        observation = check_receipt(receipt, meta, experiment)
        sc.require(side not in data[experiment][pair], "duplicate process")
        data[experiment][pair][side] = observation
        merge_shared(shared, shared_inputs(receipt))
    sc.require(all(set(p) == set(EXPERIMENTS[e]) for e in EXPERIMENTS
                   for p in data[e]), "missing process")
    return meta, data["candidate"], data["control"], shared


def replay_cell(archive, bind):
    """Cell record, observations and shared inputs from an archive alone;
    shared by run and replay."""
    with tempfile.TemporaryDirectory(prefix="task29b-replay-") as tmp:
        folder = Path(tmp) / "unpacked"
        bundle.unpack(archive, folder)
        meta, pairs, control, shared = cell_data(folder, bind)
    record = dict(an.cell(pairs, control, meta["steady"]),
                  steady=meta["steady"], pairs=meta["pairs"])
    return dict(record=record, observed=(pairs, control), shared=shared)


def cell_status(record):
    if record is None:
        return "unresolved"
    return an.status([m["decision"] for p in record["phases"].values()
                      for m in p.values()])


def work_section(cases, unresolved=()):
    """The structural evidence of all cells (None for an archive without
    it): each cell's status, and the rows that are not reproducible. A grid
    with a cell that has no work rows or is unresolved is `inconclusive`
    (unless a cell already differs), as the words do not pass then either;
    `missing` and `unresolved` name those cells."""
    section = dict(status=None, cells={}, nondeterminism=[], missing=[],
                   unresolved=list(unresolved))
    for case, record in cases.items():
        for size, cell in record["cells"].items():
            rows = cell.get("work")
            if rows is None:
                section["missing"].append(name_of(case, size))
                continue
            section["cells"][name_of(case, size)] = an.work_status(
                r["decision"] for r in rows.values())
            for name, row in rows.items():
                for what, ok in (("control", row["control_identical"]),
                                 ("baseline",
                                  row["deterministic"]["baseline"]),
                                 ("candidate",
                                  row["deterministic"]["candidate"])):
                    if not ok:
                        section["nondeterminism"].append(
                            [case, size, name, what])
    if not section["cells"]:
        return None
    status = an.work_status(section["cells"].values())
    if status == "equal" and (section["missing"] or section["unresolved"]):
        status = "inconclusive"
    section["status"] = status
    return section


def assemble(cells, records, observed, baseline=a.BASE, task=None,
             candidate=None):
    """decisions.json content from analyzed cells (all or a subset). A task
    with `rows` also binds them to the `candidate` and `baseline` revisions
    (see cell_rows)."""
    task = task or TASKS[DEFAULT_TASK]
    cases = task.cases
    out = dict(schema="task29b-decisions-v1", cases={}, nondeterminism=[],
               published_varying=[], code_visible=[], unresolved=[])
    every = []
    for case in cases:
        every_size = task.sizes(case)
        sizes = [n for n in every_size if (case, n) in cells]
        if not sizes:
            continue
        record = dict(cells={}, slopes=None, constants=None)
        for size in sizes:
            cell = records.get((case, size))
            if cell is None:
                out["unresolved"].append(name_of(case, size))
                continue
            record["cells"][size] = cell
            for phase, metrics in cell["published"].items():
                for metric, m in metrics.items():
                    out["published_varying"] += [
                        [case, size, phase, metric, side]
                        for side in ("baseline", "candidate", "control")
                        if len(m[side]) > 1]
            for phase, metrics in cell["phases"].items():
                for metric, m in metrics.items():
                    for what, ok in (("control", m["control_identical"]),
                                     ("baseline", m["deterministic"]
                                      ["baseline"]),
                                     ("candidate", m["deterministic"]
                                      ["candidate"])):
                        if not ok:
                            out["nondeterminism"].append(
                                [case, size, phase, metric, what])
                    if any(k != "0" for k in (*m["baseline"], *m["candidate"])
                           ) and metric == "code":
                        out["code_visible"].append([case, size, phase])
        if len(record["cells"]) == len(every_size):
            data = {n: observed[case, n] for n in every_size}
            record["slopes"] = an.slopes(record["cells"], list(every_size),
                                         data)
            record["constants"] = an.constants(record["cells"])
            every += an.case_decisions(record)
        else:
            for c in record["cells"].values():
                every += [m["decision"] for p in c["phases"].values()
                          for m in p.values()]
        out["cases"][case] = record
    complete = len(out["cases"]) == len(cases) and not out["unresolved"] and \
        all(r["slopes"] is not None for r in out["cases"].values())
    pairs = {c["pairs"] for r in out["cases"].values()
             for c in r["cells"].values()}
    work = work_section(out["cases"], out["unresolved"])
    if work is not None:
        # Beside the words, never inside them: neither the status below
        # nor the nondeterminism list reads a work row.
        out["work"] = work
        out["work_status"] = work["status"]
    out["complete"] = complete
    out["acceptance_pairs"] = bool(pairs) and min(pairs) >= task.pairs
    # Only the pinned develop commit is the baseline of an acceptance.
    out["acceptance_baseline"] = baseline == a.BASE
    if task.rows:
        # A smoke or a grid against another baseline is never complete.
        out["complete"] = complete and out["acceptance_pairs"] and \
            out["acceptance_baseline"]
        out["candidate"], out["baseline"] = candidate, baseline
        out["rows"] = cell_rows(task, out)
        out["infeasible"] = sorted(name_of(*k) for k in task.infeasible)
    # A definite failure is reported as such even when the grid is
    # incomplete or a smoke; a pass needs a complete, deterministic grid.
    out["status"] = an.status(every)
    if out["status"] == "pass" and (
            out["unresolved"] or not complete or not out["acceptance_pairs"]
            or not out["acceptance_baseline"] or out["nondeterminism"]):
        out["status"] = "inconclusive"
    return out


def cell_rows(task, decisions):
    """The disposition's rows of a task with `rows`: a list with one row per
    cell that was measured or tried, in the order of the cases and sizes:

        {case, size, pairs, decision, work}

    `decision` is the allocation words' decision for the cell: `pass` only
    when every gated phase and metric of the cell passes, the cell has at
    least `task.pairs` pairs, the baseline is the pinned one and none of
    its rows is nondeterministic; `fail` when one fails; `inconclusive`
    otherwise (also for a cell without an analysis). `work` is the
    structural work row beside the words (`equal`, `differs`,
    `inconclusive`, or None
    without work rows); the disposition requires it equal for a pass. The
    slopes of a case are differences of the cells', so they are not in a
    row."""
    varying = {name_of(case, size)
               for case, size, *_ in decisions["nondeterminism"]}
    rows = {}
    for case, record in decisions["cases"].items():
        for size, cell in record["cells"].items():
            name = name_of(case, size)
            status = cell_status(cell)
            if status == "pass" and not (
                    cell["pairs"] >= task.pairs and name not in varying and
                    decisions["acceptance_baseline"]):
                status = "inconclusive"
            rows[name] = dict(
                case=case, size=size, pairs=cell["pairs"],
                decision=status if status in ("pass", "fail")
                else "inconclusive",
                work=an.work_status(r["decision"] for r in
                                    cell["work"].values())
                if cell.get("work") is not None else None)
    for name in decisions["unresolved"]:
        case, size = name.rsplit("-", 1)
        rows[name] = dict(case=case, size=int(size), pairs=None,
                          decision="inconclusive", work=None)
    return [rows[name_of(*key)] for key in keys(task)
            if name_of(*key) in rows]


def counts_text(counts):
    return ", ".join("%s x%d" % (k, n) for k, n in counts.items())


def results_markdown(decisions, label="TASK29B"):
    lines = ["# %s allocation matrix" % label, "",
             "Status: **%s** (complete: %s). No allowance, no subtraction."
             % (decisions["status"], decisions["complete"]), "",
             "Decisions are counts of phase/metric rows per cell "
             "(pass/fail/inconclusive); slopes and constants per case.", "",
             "| case | size | pass | fail | inconclusive |",
             "|---|---:|---:|---:|---:|"]
    for case, record in decisions["cases"].items():
        for size, cell in record["cells"].items():
            found = [m["decision"] for p in cell["phases"].values()
                     for m in p.values()]
            lines.append("| %s | %s | %d | %d | %d |" % (
                case, size, found.count("pass"), found.count("fail"),
                found.count("inconclusive")))
    lines += ["", "| case | slope pass | slope fail | slope inconclusive |",
              "|---|---:|---:|---:|"]
    for case, record in decisions["cases"].items():
        if record["slopes"] is None:
            continue
        found = [r["decision"] for p in record["slopes"].values()
                 for rows in p.values() for r in rows]
        lines.append("| %s | %d | %d | %d |" % (
            case, found.count("pass"), found.count("fail"),
            found.count("inconclusive")))
    lines += ["", "Published, ungated total words (startup is the process "
              "load; the candidate-minus-baseline and control-minus-"
              "baseline differences are per pair):", "",
              "| case | size | phase | baseline | candidate | cand-base "
              "| ctrl-base |", "|---|---:|---|---|---|---|---|"]
    for case, record in decisions["cases"].items():
        for size, cell in record["cells"].items():
            for phase, metrics in cell["published"].items():
                m = metrics["total"]
                lines.append("| %s | %s | %s | %s | %s | %s | %s |" % (
                    case, size, phase, counts_text(m["baseline"]),
                    counts_text(m["candidate"]),
                    counts_text(m["difference"]),
                    counts_text(m["control_difference"])))
    work = decisions.get("work")
    if work is not None:
        found = list(work["cells"].values())
        lines += ["", "Structural evidence (work phase; trace, kernel and "
                  "callback counts and the result digest, never part of the "
                  "status above): **%s**. Cells equal %d, differ %d, "
                  "inconclusive %d, without work rows %d, unresolved %d; "
                  "rows not reproducible: %d."
                  % (work["status"], found.count("equal"),
                     found.count("differs"), found.count("inconclusive"),
                     len(work["missing"]), len(work["unresolved"]),
                     len(work["nondeterminism"])), "",
                  "| case | size | work |", "|---|---:|---|"]
        for case, record in decisions["cases"].items():
            for size in record["cells"]:
                lines.append("| %s | %s | %s |" % (
                    case, size, work["cells"].get(name_of(case, size), "-")))
    if "rows" in decisions:
        found = Counter(r["decision"] for r in decisions["rows"])
        lines += ["", "Cell rows (`rows` of decisions.json): %s; %d cells "
                  "infeasible and not run (`infeasible`)." % (
                      counts_text(dict(sorted(found.items()))) or "none",
                      len(decisions["infeasible"]))]
    lines += ["", "Nondeterministic gated rows: %d. Varying published "
              "rows: %d. Nonzero code-space rows: %d. Unresolved cells: %d."
              % (len(decisions["nondeterminism"]),
                 len(decisions["published_varying"]),
                 len(decisions["code_visible"]),
                 len(decisions["unresolved"])), ""]
    return "\n".join(lines)


def checkpoint(path, value):
    partial = path.with_name(path.name + ".partial")
    partial.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    partial.replace(path)


def check_pairs(inventory, task):
    """The pairs an inventory claims must be those of its cells and the
    acceptance flag it carries must be the task's rule: a record of fewer
    pairs than the task's is a smoke and must say so, one that says
    otherwise (or a flag from the rule of another task) is refused. A cell
    archive whose own pairs differ from the header's is refused by its
    binding (see binding, checked_cell)."""
    pairs = inventory.get("pairs")
    sc.require(isinstance(pairs, int) and not isinstance(pairs, bool) and
               pairs >= 2, "inventory without a valid pair count")
    if "acceptance_pairs" in inventory:
        sc.require(inventory["acceptance_pairs"] == (pairs >= task.pairs),
                   "the inventory's acceptance flag is not the rule of %s "
                   "(%d pairs; at least %d are an acceptance)" % (
                       task.name, pairs, task.pairs))


def finish(root, inventory):
    """Recompute everything from the archives; write decisions + results."""
    cells, records, observed, shared = {}, {}, {}, {}
    task = task_of(inventory)
    check_pairs(inventory, task)
    controls_copy(root, inventory)
    for row in inventory["runs"]:
        key = row["case"], row["size"]
        sc.require(key in keys(task) and key not in cells,
                   "wrong/duplicate cell")
        archive = a.safe_child(root, row["archive"])
        sc.require(a.seal(archive) == row["seal"], "changed archive")
        cells[key] = row
        if row["rejected"]:
            records[key] = None
            continue
        bind = row_binding(inventory, row)
        sc.require(row["steady"] == bind["steady"], "wrong steady count")
        cell = replay_cell(archive, bind)
        merge_shared(shared, cell["shared"])
        records[key], observed[key] = cell["record"], cell["observed"]
        sc.require(row["status"] == cell_status(records[key]),
                   "changed cell outcome")
        print("REPLAY %s %d" % key, flush=True)
    sc.require(len({json.dumps(place_lengths(r.get("places") or {}))
                    for r in inventory["runs"]}) <= 1,
               "cells measured at scratch paths of different lengths")
    return assemble(set(cells), records, observed, inventory["baseline"],
                    task, inventory.get("candidate"))


PARTIAL_FILES = ("decisions-partial.json", "RESULTS-partial.md")


def write_results(root, decisions, partial, label="TASK29B"):
    suffix = "-partial" if partial else ""
    # Either write replaces the partial decision, derived from the archives:
    # a partial write recomputes it, and a complete grid owns none (an
    # earlier --only run left it, and it would be stale).
    for name in PARTIAL_FILES:
        (root / name).unlink(missing_ok=True)
    a.save(root / ("decisions%s.json" % suffix), decisions)
    (root / ("RESULTS%s.md" % suffix)).write_text(
        results_markdown(decisions, label))


def status_code(decisions):
    return {"pass": 0, "fail": 1}.get(decisions["status"], 2)


def run(args):
    root = args.output.resolve()
    task = task_named(getattr(args, "task", DEFAULT_TASK))
    counts = load_iterations(task=task)
    wanted = keys(task)
    if args.only:
        wanted = [k for k in wanted if name_of(*k) in args.only]
        sc.require(len(wanted) == len(args.only), "unknown --only cell")
    with Grid(args) as grid:
        inventory = dict(grid.header, iterations=counts, jobs=[], runs=[])
        if args.resume:
            old = a.load(root / "inventory.json")
            sc.require(not (root / "decisions.json").exists(),
                       "run already complete")
            differ = changed_settings(old, inventory)
            sc.require(not differ, "resume with different settings: " +
                       ",".join(differ))
            inventory["jobs"] = old["jobs"]
            inventory["runs"] = old["runs"]
            for leftover in root.glob("*.partial"):
                leftover.unlink()
            finish(root, dict(old, runs=old["runs"]))
        else:
            root.mkdir(parents=True, exist_ok=False)
            # The archives alone must be able to re-verify the controls.
            shutil.copyfile(args.controls_receipt,
                            root / inventory["controls"]["file"])
        done = {(r["case"], r["size"]) for r in inventory["runs"]}
        todo = sorted((k for k in wanted if k not in done),
                      key=lambda k: -k[1])
        jobs = max(1, min(args.jobs, len(todo)))
        inventory["jobs"] = inventory["jobs"] + [jobs]  # workers really used
        build = root / ("build-%d.json.gz" % len(inventory["jobs"]))
        pool = queue.Queue()
        try:
            with ThreadPoolExecutor(max_workers=jobs) as setup:
                for job in setup.map(grid.make_job, range(jobs)):
                    pool.put(job)
        finally:  # private Holmake commands and exits, even when one fails
            build.write_bytes(compact(grid.report))
        lock = threading.Lock()

        def work(key):
            job = pool.get()
            try:
                print("START " + name_of(*key), flush=True)
                row = grid.cell(job, *key, root, counts)
            finally:
                pool.put(job)
            with lock:
                inventory["runs"].append(row)
                checkpoint(root / "inventory.json", inventory)
            print("END %s %s" % (name_of(*key), row["status"]), flush=True)

        executor = ThreadPoolExecutor(max_workers=jobs)
        try:
            futures = [executor.submit(work, k) for k in todo]
            finished, _ = wait(futures, return_when=FIRST_EXCEPTION)
            for future in finished:
                future.result()
        except BaseException:
            executor.shutdown(wait=True, cancel_futures=True)
            raise
        finally:
            checkpoint(root / "inventory.json", inventory)
        executor.shutdown()
    decisions = finish(root, inventory)
    write_results(root, decisions, not decisions["complete"], task.label)
    return status_code(decisions)


def replay(args):
    root = args.output.resolve()
    inventory = a.load(root / "inventory.json")
    decisions = finish(root, inventory)
    partial = not decisions["complete"]
    name = "decisions%s.json" % ("-partial" if partial else "")
    sc.require(json.loads(json.dumps(decisions)) == a.load(root / name),
               "changed decisions")
    label = task_of(inventory).label
    sc.require(results_markdown(decisions, label) == (root / (
        "RESULTS-partial.md" if partial else "RESULTS.md")).read_text(),
        "changed results table")
    print("%s archives and decisions replayed: %s" % (
        label, decisions["status"]))
    return status_code(decisions)


def check_jobs(args):
    """Same cells serially and in parallel must give identical raw counts."""
    cells = args.cells
    sc.require(len(set(cells)) == len(cells) >= 2 and args.jobs >= 2,
               "check-jobs needs two distinct cells and --jobs >= 2")
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=False)
    reports, workers = {}, {}
    for label, jobs in (("serial", 1), ("parallel", args.jobs)):
        sub = argparse.Namespace(**dict(vars(args), only=cells,
                                        resume=False, jobs=jobs,
                                        output=root / label))
        run(sub)
        inventory = a.load(root / label / "inventory.json")
        workers[label] = inventory["jobs"][-1]
        reports[label] = {}
        for name in cells:
            case, size = name.rsplit("-", 1)
            row = [r for r in inventory["runs"]
                   if (r["case"], r["size"]) == (case, int(size))][0]
            reports[label][name] = replay_cell(
                root / label / (name + ".json.xz"),
                row_binding(inventory, row))["observed"]
    sc.require(workers["serial"] == 1 and 1 < workers["parallel"],
               "the parallel run did not use several workers")
    same = reports["serial"] == reports["parallel"]
    a.save(root / "jobs-check.json", dict(
        schema="task29b-jobs-check-v1", jobs=args.jobs, workers=workers,
        cells=cells, identical=same))
    print("parallel counts identical to serial: %s" % same)
    return 0 if same else 2


def toolchain(args):
    """Source-built native Poly/ML compiling HOL at HEAD, kept for reuse."""
    from bootstrap_probe import build_native_hol
    repo = args.repo.resolve(strict=True)
    root = args.toolchain.resolve()
    env = dict(PATH=pr.PATH, HOME="/nonexistent",
               TMPDIR=os.environ.get("TMPDIR", "/tmp"), TERM="dumb",
               LC_ALL="C", TZ="UTC", CONFIG_SITE="/dev/null")
    for key, name in (("CC", "gcc"), ("CXX", "g++")):
        env[key] = shutil.which(name, path=env["PATH"]) or ""
        sc.require(bool(env[key]), "missing compiler: " + name)
    sc.require(platform.machine() == "aarch64", "unsupported host")
    report = dict(schema="task29b-toolchain-v1", commands=[],
                  environment=env, head=a.git(repo, "rev-parse", "HEAD"))
    with a.serial_lock(repo) as fds:
        root.mkdir(parents=True, exist_ok=False)

        def run_command(command, cwd):
            print("RUN", " ".join(command), flush=True)
            receipt = loading.execute(command, cwd, env, args.timeout, fds)
            report["commands"].append(trimmed(receipt))
            sc.require(receipt["exit"] == 0 and not receipt["timed_out"],
                       "failed command: " + str(command))
            return receipt
        lineage = {}
        try:
            build_native_hol(args.source or DEFAULT_SOURCE, root, repo, env,
                             run_command, lineage)
            report.update(lineage=lineage, success=True)
            name = "lineage.json"
        except BaseException:
            # Kept for diagnosis; prepare() only ever reads lineage.json.
            report.update(lineage=lineage, success=False)
            name = "lineage-failed.json"
            raise
        finally:
            with (root / name).open("x") as stream:
                json.dump(report, stream, indent=2, allow_nan=False)
    return 0


def main(argv=None):
    # Every process this driver starts, git included, resolves its program
    # on pr.PATH, not the caller's; the tools found there are sealed.
    pr.use_fixed_path()
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)

    def common(p, measuring=True):
        p.add_argument("--output", type=Path, required=True)
        p.add_argument("--repo", type=Path, default=HERE.parents[3])
        p.add_argument("--timeout", type=int, default=3600)
        if measuring:
            p.add_argument("--task", choices=sorted(TASKS),
                           default=DEFAULT_TASK,
                           help="cases and steady counts of this task")
            p.add_argument("--baseline", default=a.BASE)
            p.add_argument("--candidate", required=True)
            p.add_argument("--toolchain", type=Path, required=True)
            p.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
            p.add_argument("--jobs", type=int, default=8)
            p.add_argument("--controls-receipt", type=Path, required=True,
                           help="successful run_controls.py receipt (json "
                           "or json.gz) for this grid's private runtime")
            p.add_argument("--authorize-experimental-runtime",
                           action="store_true")

    r = sub.add_parser("run")
    common(r)
    r.add_argument("--pairs", type=int, default=None,
                   help="pairs per cell (default: the task's, %d for the "
                   "legacy tasks, %d for TASK37); fewer than the task's is "
                   "a smoke, never a decision" % (PAIRS, TASK37_PAIRS))
    r.add_argument("--resume", action="store_true")
    r.add_argument("--only", nargs="*", default=[],
                   help="measure only these case-size cells (partial)")
    c = sub.add_parser("check-jobs")
    common(c)
    c.add_argument("--cells", nargs="+", required=True)
    c.add_argument("--pairs", type=int, default=None)
    p = sub.add_parser("replay")
    p.add_argument("--output", type=Path, required=True)
    t = sub.add_parser("toolchain")
    t.add_argument("--toolchain", type=Path, required=True)
    t.add_argument("--repo", type=Path, default=HERE.parents[3])
    t.add_argument("--source", type=Path)
    t.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args(argv)
    if args.action in ("run", "check-jobs"):
        sc.require(args.pairs is None or args.pairs >= 2,
                   "need an AB and a BA pair and a positive job count")
        sc.require(args.jobs >= 1,
                   "need an AB and a BA pair and a positive job count")
        sc.require(args.jobs <= MAX_JOBS,
                   "--jobs above %d would lengthen a job path" % MAX_JOBS)
    return {"run": run, "replay": replay, "check-jobs": check_jobs,
            "toolchain": toolchain}[args.action](args)


if __name__ == "__main__":
    sys.exit(main())
