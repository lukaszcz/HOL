"""Synthetic TASK29B fixtures for the matrix tests.

A sandbox of real (tiny) files stands in for the toolchain and the private
selection directories, so loader inventories, process receipts, archived
cells and the driver's own sealing code can be exercised without a runtime.
Nothing here is evidence, and nothing is read from or written to the repo.
"""
import json
from pathlib import Path
import sys

import acceptance as a
import allocation_boundary as bd
import allocation_matrix as m
import allocation_schema as sc
import evidence_bundle as bundle
import path_schema
import test_allocator_paths as paths_fixture

sys.path.insert(0, str(m.HERE.parent / "compatibility"))
import run_paired as rp

LIB = "/scratch/libpolyml.so.16.0.0"
ALIAS = LIB + ".alias"
CATEGORIES = ("native", "rts", "interpreter", "code")
CASE, SIZE, STEADY, REPEATS = "frag_create", 0, 4, 3
BASE_PIN, CAND_PIN = "a" * 40, "b" * 40
SELECTED = ("Traverse.sml", "simpLib.sml")  # elaborated by every process


def point(counts, overflow=0, word=8, abi=1):
    cats = [counts.get(k, 0) for k in CATEGORIES]
    return [abi, word, overflow, sum(cats), *cats]


# Everything shared by the cells of one grid, as a literal: tests iterate
# this, never the driver's own list, so a dropped key cannot hide itself.
EXPECTED_GRID_KEYS = (
    "schema", "baseline", "candidate", "pairs", "runtime", "shim", "repo",
    "toolchain_head", "toolchain_products", "tools", "inputs", "controls",
    "sources", "revisions", "fixtures", "word_bytes", "canary",
    "iterations", "environment", "boundary", "harness")
# Manifest prefixes of the synthetic boundary: directories of the sandbox
# toolchain that no process may load from.
PREFIXES = ("src/boss/", "help/Docfiles/")
# Where a run's private runtime and shim stand: never compared on resume.
EXPECTED_PLACE_KEYS = ("shim_path", "library", "aliases", "tmpdir")
EXPECTED_LENGTH_KEYS = ("tmpdir", "library")
RUNTIME = dict(sha256="r" * 64, bytes=7)
TREE = "d" * 64  # invented: tree identity outside the performance area


def controls_data(**change):
    """An invented, internally consistent controls receipt: the three path
    launchers carry synthetic (parser-test) transcripts, replayed here by
    the real path schema; every harness file is sealed from this checkout."""
    commands, observed = [], {}
    for key, profile, program in m.PATH_LAUNCHERS:
        row = paths_fixture.receipt(profile)
        row["command"] = ["/x/fixture/" + program, *row["command"][1:]]
        commands.append(row)
        observed[key + "_observations"] = json.loads(json.dumps(
            path_schema.validate_receipt(row, profile, timeout=1)))
    data = dict(
        schema=m.CONTROLS_SCHEMA, success=True, runtime=dict(RUNTIME),
        inputs={str(p): a.seal(p) for p in m.pr.harness_inputs()},
        head=CAND_PIN, commands=commands,
        harness=dict(head=CAND_PIN, dirty=False, reference="simplifier",
                     reference_commit="c" * 40, tree_outside_performance=TREE),
        lineage=dict(hol_snapshot=CAND_PIN, native_configuration="config\n",
                     hol_products={"/x/bin/hol": dict(sha256="1", bytes=1)},
                     native_products={"/x/bin/poly": dict(sha256="2",
                                                          bytes=2)}),
        instrumented_libraries={
            "/lib/libc.so.6": dict(resolved="/lib/libc.so.6", sha256="c" * 64,
                                   bytes=3),
            LIB.rsplit(".", 2)[0]: dict(
                resolved=LIB, sha256=RUNTIME["sha256"],
                bytes=RUNTIME["bytes"])},
        **observed)
    data.update(change)
    return {k: v for k, v in data.items() if v is not ...}


def toolchain_libraries():
    """The matrix toolchain's ldd result that controls_data() must match
    (raw paths differ; names and seals are compared)."""
    return {"/usr/lib/libc.so.6": dict(resolved="/x", sha256="c" * 64,
                                       bytes=3),
            "/other/libpolyml.so.16": dict(resolved="/y",
                                           sha256=RUNTIME["sha256"],
                                           bytes=RUNTIME["bytes"])}


def text(values):
    return ",".join(map(str, values))


def default_cost(name):
    """Words of each bracket in a valid process: 3, the no-op bracket 4,
    and the canary exactly its known extra over the no-op bracket."""
    if name == "empty":
        return {"native": 4}
    if name == "canary":
        return {k: v + (4 if k == "native" else 0)
                for k, v in sc.CANARY.items()}
    return {"native": 3}


def process_events(case=CASE, size=SIZE, steady=STEADY, repeats=REPEATS,
                   work=None, mutate=None, start=1000):
    """Allocation events of one valid process; work maps bracket to a dict."""
    work = work or {}
    rows, now, steady_index = [], dict.fromkeys(CATEGORIES, start), 0
    for name in sc.names(repeats):
        index = steady_index if name == "operation_steady" else 0
        steady_index += name == "operation_steady"
        begin = dict(now)
        cost = work.get(name, default_cost(name))
        if isinstance(cost, list):  # one entry per steady repeat
            cost = cost[index]
        for k, v in cost.items():
            now[k] = now[k] + v
        rows.append([name, index, point(begin), point(now)])
    if mutate:
        mutate(rows)
    events = [["observation", "alloc.config",
               ",".join([case, str(size), str(steady), str(repeats),
                         str(sc.ABI), str(sc.CANARY_ARRAY)])]]
    for name, index, s, e in rows:
        events.append(["observation", "alloc." + name,
                       "%d;%s;%s" % (index, text(s), text(e))])
    events.append(["observation", "alloc.foreign", sc.FOREIGN])
    events.append(["check", "allocation brackets", "pass"])
    return events


def parse_kw(**kw):
    return dict(case=kw.get("case", CASE), size=kw.get("size", SIZE),
                steady=kw.get("steady", STEADY),
                repeats=kw.get("repeats", REPEATS))


def parsed(**kw):
    events = process_events(**{k: v for k, v in kw.items() if k in (
        "case", "size", "steady", "repeats", "work", "mutate", "start")})
    return sc.parse(events, **parse_kw(**kw))


def delta(words):
    cats = {"native": words} if isinstance(words, int) else dict(words)
    d = {k: cats.get(k, 0) for k in CATEGORIES}
    d["total"] = sum(d.values())
    d["heap"] = d["total"] - d["code"]
    return d


def observation(totals, steady=STEADY):
    """phase -> raw delta; a value is native words, a category dict or (for
    operation_steady) one such value per repeat."""
    phases = {}
    for phase in sc.PHASES + sc.PUBLISHED:
        words = totals.get(phase, 1)
        reps = 3 if phase == "operation_steady" else 1
        value = words if isinstance(words, list) else [words] * reps
        phases[phase] = [delta(w) for w in value]
    return dict(steady=steady, phases=phases)


def experiment(base, cand, ctrl=None, pairs=10, steady=STEADY):
    """pairs/control lists; ctrl varies the control side by pair."""
    b, c = observation(base, steady), observation(cand, steady)
    ctrl = ctrl or (lambda i: observation(base, steady))
    return ([dict(baseline=b, candidate=c) for _ in range(pairs)],
            [dict(baseline=b, control=ctrl(i)) for i in range(pairs)])


def seal(path):
    return a.seal(path)


def counts(steady=STEADY, repeats=REPEATS):
    return dict(schema="task29b-iterations-v1", repeats=repeats,
                steady={m.name_of(*k): steady for k in m.keys()})


class Sandbox:
    """Real files for one job: a toolchain tree and the private sides."""

    def __init__(self, root, pairs=10):
        root = Path(root)
        self.root, self.pairs = root, pairs
        self.tmpdir = str(root)  # a place; cells may be made elsewhere
        self.repo = root / "hol"
        (self.repo / "sigobj").mkdir(parents=True)
        (self.repo / "src").mkdir()
        self.heap = self.repo / "src/Heap1.sml"
        self.heap.write_text("val heap = 1\n")
        (self.repo / "src/Heap1.uo").write_text("uo\n")
        self.shim = root / "bracket.so"
        self.shim.write_text("shim\n")
        self.private = {}
        for side, label in m.SIDES.items():
            directory = root / "scratch/j00" / label
            directory.mkdir(parents=True)
            body = "val x = 2\n" if side == "candidate" else "val x = 1\n"
            for name in SELECTED:
                (directory / name).write_text("(* %s *)\n%s" % (name, body))
            (directory / "MatrixSupport.sml").write_text("val support = 1\n")
            (directory / "Performance.sml").write_text("val perf = 1\n")
            self.private[side] = directory
        self.write_controls()

    def sources(self):
        return {side: {name: dict(
            seal(self.private[side] / name),
            git_blob=("2" if side == "candidate" else "1") * 40)
            for name in SELECTED} for side in m.SIDES}

    def fixtures(self):
        base = self.private["baseline"]
        return {n: seal(base / n) for n in ("Performance.sml",
                                            "MatrixSupport.sml")}

    def real_grid(self, library=LIB, aliases=None, shim=None, tmpdir=None,
                  **env):
        """A real Grid with just the attributes make_header reads, as if
        prepared with the private runtime at `library`, the shim at `shim`
        and the scratch trees in `tmpdir`: two of them differ only by where
        they stand. `env` overrides variables of the environment."""
        import argparse
        from unittest import mock
        header = self.header()
        grid = m.Grid.__new__(m.Grid)
        grid.args = argparse.Namespace(
            baseline=BASE_PIN, candidate=CAND_PIN,
            controls_receipt=self.controls_path)
        grid.pairs, grid.shim = self.pairs, Path(shim or self.shim)
        grid.lib, grid.hol, grid.repo = Path(library), self.repo, self.repo
        grid.aliases = [library + ".alias"] if aliases is None else aliases
        grid.tools = dict(header["tools"], **{
            str(library): dict(sha256=RUNTIME["sha256"],
                               bytes=RUNTIME["bytes"]),
            str(Path(library).parent / "libc.so.6"): dict(sha256="c" * 64,
                                                          bytes=3)})
        grid.inputs, grid.sources = header["inputs"], header["sources"]
        grid.revisions, grid.fixtures = (header["revisions"],
                                         header["fixtures"])
        grid.env = dict(self.base_environment(), **env)
        if tmpdir is not None:
            grid.env["TMPDIR"] = str(tmpdir)
        grid.libraries = toolchain_libraries()
        grid.native_configuration = "config\n"
        grid.boundary, grid.harness = header["boundary"], header["harness"]
        grid.report = dict(runtime=dict(RUNTIME), shim=header["shim"])
        grid.make = lambda: mock.patch.object(
            m.pr, "tree_outside_performance", return_value=TREE)
        return grid

    def write_controls(self, **change):
        """The controls receipt file of this sandbox and its header entry."""
        path = self.root / "controls.json"
        path.write_text(json.dumps(controls_data(**change)))
        self.controls_path = path
        facts = m.controls_facts(a.load(path), dict(RUNTIME), TREE)
        return dict(facts, receipt=seal(path), file="controls-receipt.json")

    def base_environment(self):
        """The whole environment of the driver and its processes."""
        return dict(self.content_environment(), TMPDIR=self.tmpdir)

    def content_environment(self):
        """What the header records as content: no place (TMPDIR)."""
        return dict(PATH=m.pr.PATH, HOME="/nonexistent", HOLDIR=str(self.repo),
                    TERM="dumb", LC_ALL="C", TZ="UTC",
                    CONFIG_SITE="/dev/null", CC="/usr/bin/gcc",
                    CXX="/usr/bin/g++")

    def header(self, steady=STEADY, repeats=REPEATS, **override):
        value = dict(
            schema=m.SCHEMA, baseline=BASE_PIN, candidate=CAND_PIN,
            pairs=self.pairs, runtime=dict(RUNTIME),
            shim=seal(self.shim), shim_path=str(self.shim), library=LIB,
            aliases=[ALIAS], repo=str(self.repo), toolchain_head=CAND_PIN,
            toolchain_products={"hol": dict(sha256="h" * 64, bytes=1)},
            tools={"poly": dict(sha256="p" * 64, bytes=2)},
            inputs={"driver": dict(sha256="d" * 64, bytes=3)},
            controls=self.write_controls(),
            sources=self.sources(),
            revisions=dict(baseline=BASE_PIN, control=BASE_PIN,
                           candidate=CAND_PIN),
            fixtures=self.fixtures(), word_bytes=sc.WORD_BYTES,
            canary=dict(array=sc.CANARY_ARRAY, words=sc.CANARY),
            environment=self.content_environment(), tmpdir=self.tmpdir,
            boundary=dict(schema=bd.SCHEMA, changed=0,
                          manifest_prefixes=list(PREFIXES)),
            harness=dict(head=CAND_PIN, tree_outside_performance=TREE,
                         blobs={}, fixtures=[]),
            iterations=counts(steady, repeats),
            acceptance_pairs=self.pairs >= m.PAIRS)
        value.update(override)
        return value

    def bind(self, case=CASE, size=SIZE, **override):
        return m.binding(self.header(**override), case, size)

    def job(self):
        job = m.Job(self.root / "scratch/j00")
        job.dirs = dict(self.private)
        job.names = {Path(n).stem for n in SELECTED}
        job.sources = {str(f.resolve()): rp.fingerprint(f)
                       for d in job.dirs.values() for f in d.iterdir()}
        job.tree = {s: m.sealed_tree(d) for s, d in job.dirs.items()}
        job.inventory = {
            side: [dict(git_path="src/simp/src/" + name, **seals)
                   for name, seals in src.items()]
            for side, src in self.sources().items()}
        return job

    def environment(self, side, case=CASE, size=SIZE, steady=STEADY,
                    repeats=REPEATS):
        return dict(
            self.base_environment(),
            LD_LIBRARY_PATH=str(Path(LIB).parent),
            PAIR_SELECTION=m.SIDES[side], PAIR_FIXTURE="performance",
            PAIR_CONTROL="none", PAIR_PRIVATE=str(self.private[side]),
            PAIR_TARGET="Performance", PERF_CASE=case, PERF_SIZE=str(size),
            ALLOC_STEADY=str(steady), ALLOC_REPEATS=str(repeats),
            TASK29_ALLOC_SHIM=str(self.shim))

    def loader(self, side, observations):
        p, repo = str(self.private[side]), str(self.repo)
        heap = str(self.heap)
        selected = [p + "/" + name for name in SELECTED]
        support, perf = p + "/MatrixSupport.sml", p + "/Performance.sml"
        return [["begin", m.SIDES[side], "performance", "none"],
                ["cwd", p], ["holdir", repo, repo],
                ["preloaded", "Lib,Thm"], ["heapfile", heap],
                ["search", p], ["search", repo + "/sigobj"],
                *[e for f in selected for e in (["use", f], ["used", f])],
                ["use", support], ["used", support], ["use", perf],
                *observations, ["used", perf], ["loaded", heap],
                *[["loaded", f] for f in selected], ["loaded", support],
                ["loaded", perf], ["end", "pass", "1"]], \
            [heap, *selected, support, perf]

    def paths(self, raws):
        out = {}
        for raw in raws:
            related = {}
            uo = Path(raw).with_suffix(".uo")
            if uo.exists():
                related[str(uo)] = seal(uo)
            out[raw] = dict(physical=raw, **seal(Path(raw)),
                            related_products=related, origin="x")
        return out

    def receipt(self, experiment, side, pair, position, case=CASE, size=SIZE,
                steady=STEADY, repeats=REPEATS, work=None, rows=None,
                mutate=None, library=LIB, start=1000):
        """rows mutates bracket rows, mutate the whole event list."""
        events, raws = self.loader(side, process_events(
            case, size, steady, repeats, work, rows, start))
        if mutate:
            mutate(events)
        lines = ["@@PAIR\t%d\t%s" % (i, "\t".join(e))
                 for i, e in enumerate(events)]
        lines.append("@@TASK29_ALLOC_RUNTIME_V1\t" + library)
        lines.append("@@TASK29_ALLOC_MAP_V1\t0-1 r-xp 0 00:00 1 " + library)
        return dict(
            experiment=experiment, side=side, selection=m.SIDES[side],
            pair=pair, position=position, accepted=True, exit=0,
            timed_out=False, stdout="\n".join(lines) + "\n",
            environment=self.environment(side, case, size, steady, repeats),
            paths=self.paths(raws))

    def write_cell(self, folder, build=None, case=CASE, size=SIZE,
                   steady=STEADY, repeats=REPEATS, **override):
        """build(experiment, side, pair) -> keyword overrides of receipt()."""
        folder = Path(folder)
        for experiment, sides in m.EXPERIMENTS.items():
            for pair in range(self.pairs):
                order = sides if pair % 2 == 0 else sides[::-1]
                for position, side in enumerate(order):
                    extra = (build(experiment, side, pair) if build
                             else None) or {}
                    m.write_receipt(
                        folder / experiment, "pair-%02d-%s" % (
                            pair, m.SIDES[side]), self.receipt(
                                experiment, side, pair, position, case,
                                size, steady, repeats, **extra))
        meta = dict(self.bind(case, size, **override), schema=m.SCHEMA,
                    rejected=None)
        m.write_receipt(folder, "meta", meta)

    def archive(self, tmp, build=None, name="cell", case=CASE, size=SIZE,
                where=None, **kw):
        folder = Path(tmp) / ("dir-" + name)
        self.write_cell(folder, build, case, size, **kw)
        out = Path(where or tmp) / (name + ".json.xz")
        bundle.pack(folder, out)
        return out

    def inventory_row(self, archive, case=CASE, size=SIZE):
        record = m.replay_cell(archive, self.bind(case, size))["record"]
        return dict(case=case, size=size, steady=STEADY, rejected=None,
                    archive=archive.name, seal=seal(archive), files=0,
                    places=m.places(self.header()),
                    status=m.cell_status(record))


def rewrite(path, change):
    """Rewrite one archived receipt in place after change(record)."""
    path = Path(path)
    record = a.load(path)
    change(record)
    path.unlink()
    m.write_receipt(path.parent, path.name[:-len(".json.gz")], record)


def dump(value):
    return json.dumps(value, sort_keys=True)
