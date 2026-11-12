"""Strict parser and validator of the `@@T33` records of the TASK33 probes
(task33/*.sml and task33/*.ML, written by T33.sml and T33Kind.ML).

Every probe prints one record per line:

    @@T33<TAB>{json object}

Invocation (S1): the probe is a bare module name run by `hol run` with the
probe directory as cwd (the probes `use` T33*.ML by relative name), built
there by Holmake in its final directory. The compiled unit is in
`.hol/objs/`, so nothing may test for `<dir>/T33Load.uo`, and the probe
directory is as much a root to mask as the snapshot root. The timed kinds
run T33Load (state*-empty, load-*, first-use), which compiles only
T33Load.sml, T33Kind.ML and one check file; T33Trivial measures the rest.

Other stdout lines (compiler noise, the `@@MATRIX_RELEASE` line of
RuntimeMetrics.sml) are ignored. A line that starts with `@@T33` and is not
exactly this format is an error. The reporter's stats still go to
$T32_STATS and are not read here.

Record types (the field `record`); every record also has `probe` and `kind`
(the process kind, T33_KIND for the load and registry probes) and exactly
the fields below, no more and no fewer:

  probe     holdir:str, switches:{graph_extra,leak,hook:bool}, params:obj
            params: load/registry/trivial {module:str|null}; graph
            {sizes:[uint]}; release {m:uint>=1}; ext {m:uint>=1,
            sizes:[uint]}
  check     check:str, ok:bool, value:str   (a kernel check; ok must hold;
            value is evidence: the printed theorems)
  time      label:str, cpu:real s, wall:real s  (in-process bracket)
  live      phase:str, size_heap, free_full, alloc, alloc_free:uint bytes,
            gc_share:uint, extent:int, log_start:uint, log_end:uint,
            words:int. words is the garbage collector's marked live total
            of the reading's third own full GC, read by the probe from the
            GC log (see The GC log); extent = (size_heap - free_full -
            alloc) // 8 is the heap extent, live data plus holes, reported
            only (the validator recomputes it); log_start is the byte
            length of the log before the reading's own GCs and log_end the
            offset just past the line of the third total.
  registry  loaded, listeners, attributes, set_types, structures,
            signatures, functors:[str]; files:[[file,dir]];
            sizes:[{name,struct:uint|null,sig:uint|null}] (absolute
            objSize words, reported only); anchored: {d:[str], d_vals:
            [uint]*3|null, total:[uint]*3|null, rows:[{name, vals:[uint]*3|
            null}], repeat_ok:bool|null}. total and repeat_ok are null when
            D is not loaded (d_vals null): not applicable, not
            non-repeatable. D is ThmAttribute and Cond_rewr (structure
            and signature) plus Context.snapshot (). rows are the exclusive
            parts objSize((D, X)) - objSize((D, D)) of the structures X
            outside D. total is the closure total U = objSize((D, [X1, ...,
            Xn])) over all of them (a list: its n cons cells are constant).
            Each is repeated REPEATS times in one image; repeat_ok: the
            repeats agree. Per repeat the arithmetic holds: with u = U -
            objSize((D, D)) - 3n (n structures, a cons cell is 3 words),
            max(rows) <= u <= sum(rows) (the union of the exclusive parts
            lies between the largest and the sum).
  graph     graph:str, n:uint; as built: anchor (before the objects were
            built, and after PolyML.shareCommonData on the anchor inputs:
            the canonical pre-anchor), anchor_post (after the rows), union,
            words = union - anchor, share (the GC share-pass count when
            measured); canonical (after PolyML.shareCommonData on every
            root): canon_anchor, canon_anchor_post, canon_union,
            canon_words, canon_share. All uint except the words, and
            union >= anchor.
  phase     n:uint, share_start, share_built, share_shared, share_canon:
            uint (share counts at the start of the size, after the as-built
            rows, after the forced sharing, after the canonical rows);
            share_tries:uint 1..SHARE_TRIES_MAX, converged:bool (the
            sharing of the anchor inputs that precedes the canonical
            pre-anchor ran share_tries rounds and the anchors stopped
            changing; a probe that did not converge is NotComparable, not a
            moved anchor);
            build, rows: peak windows {reset_ok:bool, rss_before,
            hwm_before, rss_reset, hwm_reset, rss_after, hwm_after:
            uint|null bytes, status:"ok"|"unsupported"}. build is the
            construction and the kernel checks (VmHWM reset before it); rows
            is the probe's own measurement (a second reset before it). A
            reset is verified (status ok) only if its write succeeded, VmHWM
            was above VmRSS by more than RESET_SLACK before it (something to
            reset), and VmHWM is within RESET_SLACK of VmRSS after it.
  step      graph:str, mode:"built"|"canonical", first, rest:int, span:uint
            (graph kinds at sizes 0, 1, 10 only): first = words(1) -
            words(0), rest = words(10) - words(1), span = 9. Equal per
            object when the rows count per-object data only; the summary
            reports `match` (rest = span * first), the verdict is S4's.
  release   release:str, m:uint, before, after, held:uint live words;
            residual (after - before) / m; held size (held - after) / m.
            The leading kind (FLOOR_KIND, `noop`) is the in-process noise
            floor: T33_LEAK does not retain its objects, and its residual
            must be exact (see Share passes).
  weak      scope:str, retained, collected:bool, full_gcs:uint>=4, status
  done      (last record)

Share passes. Poly/ML's GC share pass (gcSharePasses) is timing-driven and
cannot be switched off; it deduplicates equal immutable data. So the
as-built rows of a size are gateable only when share_start = share_built (no
pass inside the window), and the canonical rows (forced sharing, then
measured) only when share_shared = share_canon; `summary["gateable"][n]`
says which, and `summary["gateable_coverage"][kind]` lists the sizes whose
as-built rows are gateable. The anchors must not move (released = anchor):
the canonical pre-anchor (`anchor`, measured on fully shared inputs) must
equal the canonical post-anchor whatever share passes ran, and the as-built
post-anchor must equal it where no pass ran. A moved anchor is data, not a
malformed record: it is listed in `summary["anchor_moved"]` as {kind, n,
mode, pre, post} (a retention finding about the candidate, for S4 to
judge).

The GC log. A storage probe runs under `--debug gc --logfile $T33_GCLOG`
(GCLOG_ENV; the driver sets both, and a timing process has neither). Poly/ML
5.9.2 writes one line per full GC (and none for a minor GC) of the form

    GC: Full GC, <n> words required <k> spaces  (FULL_GC_HEAD)
    GC: Mark: Total live data <N> words        (LOG_TOTAL, N decimal digits)

(n and k decimal; PolyML.fullGC says `0 words required`, a full GC set off
by the run time says `n words required`, n > 0.)

The marked live total is exact, while the heap extent includes holes: the
copy phase places immutable data by the first object it copies and a later
GC can move it, leaving a counted hole, and new objects fill old holes (the
~509-word jump of the no-op kind, the held deficits;
.agent-files/evidence/task33/noop-offset-diagnosis.md). T33.sml `live` takes
the total of the third of its own full GCs: it records the log length
`log_start` just before them, reads the log from there after them, takes the
third total line and records the offset `log_end` just past it. A full GC
the run time sets off between `log_start` and the first own one, or after
the third own total (e.g. by reading the log, whose buffers it would count),
is not the third total. `gc_log_totals` and `check_gc_log` are the one place
that parses the log in Python: `validate(..., gclog)` takes the slice
`log[log_start:log_end]` of every record and requires prev log_end <=
log_start < log_end <= len(log), line boundaries at both ends, exactly
OWN_FULL_GCS (three) totals with the last line a total, and `words` equal
to the third. A slice that is not exactly three FULL_GC_HEAD lines, all
`0 words required`, is NotComparable (a redraw): a foreign run-time GC in
the slice, or more totals than headers (a repeated mark: a retry after a
Count error). The NotComparable reasons are raised after every record is
checked, so that a later malformed record is not taken for a redraw. The
gap between a record's log_end and the next log_start (quiet readings, GCs
in between) is not examined.
The log is a receipt field with its sha256 (task32_downstream `validate`
checks the digest). A process with `live` records and no log is refused.

Release readings and share passes. A GC share pass merges equal
immutable cells and never adds a word, so for two readings x, y with the
same `alloc` and more share passes at y, `y - x` is a lower bound of the
difference without the passes. Poly/ML runs the passes on its own (more as a
leaked heap grows), so requiring equal gc_share would redraw every leaking
process. Per release kind, the residual (after - before) / m is exact when
(alloc, gc_share) are equal, a bound (`residual_bound[kind]`) when alloc is
equal and gc_share grew, and then admitted only when >= HALF, else the
process is NotComparable (a redraw). A differing alloc, a gc_share that
shrank, and a bound on the floor kind (the noise floor must be exact) are
NotComparable. Invariant relied on by task33_rules (R1, E2 (b)): an admitted
bound is positive and >= HALF, so a candidate bound fails the kind (a lower
bound >= 1/2 is a retained word), a baseline bound is inconclusive (a
baseline at or over 1/2), and the stability checks (spread <= RESOLUTION),
which a lower bound would not support, are never reached with a bound. The
held size (held - after) / m is compared with the `after` reading (the one
it is a difference of): `held_comparable[kind]` is the held reading being
either exact or a bound (`held_bound[kind]`) >= H_MIN (a lower bound >=
H_MIN proves the sensitivity requirement; one below it proves nothing and
is not used). That share-pass rule is the whole of a reading's
comparability: the words are the marked live total, so no allocation-area
freshness condition applies (alloc equality and gc_share are judged by
this rule). A NotComparable process is a redraw, not a malformed record.

The exact sequence of records of a process is fixed by its probe, kind and
params (`expected_keys`), so a missing, extra or reordered record is an
error. `validate` returns a summary. Control switches (T33_GRAPH_EXTRA,
T33_LEAK, T33_HOOK) are part of the `probe` record; `validate` takes the set
of switches the process is expected to run with (`controls`) and requires
exactly that set, each applicable to the probe (CONTROL_PROBES).

For S1/S4: `normalized_checks(stdout_text) -> list[str]` is the normalized
digest input of a probe unit (one line per kernel check with its evidence,
no timing), and `digest(stdout_text) -> str` its sha256. Both parse strictly
and refuse a failed check.
"""
import hashlib
import json
import re
import sys
from fractions import Fraction

sys.dont_write_bytecode = True

SCHEMA = "task33-records-v6"
PREFIX = "@@T33\t"

# Files a probe directory needs (copied from task33/ and from the
# performance directory) and the Holmake targets per probe. The probes are
# built in their final directory and run there with a bare module name.
PROBE_SOURCES = ("T33.sml", "T33Kind.ML", "T33Load.sml", "T33Trivial.sml",
                 "T33Registry.sml", "T33GraphLib.sml", "T33Graph.sml",
                 "T33Release.sml", "T33Ext.sml", "T33CheckSimp.ML",
                 "T33CheckCong.ML", "T33CheckFirst.ML", "T33ExtUse.ML")
PROBE_REUSED = ("RuntimeMetrics.sml",)  # unchanged, ../RuntimeMetrics.sml
PROBE_TARGETS = dict(load="T33Load.uo", trivial="T33Trivial.uo",
                     registry="T33Registry.uo", graph="T33Graph.uo",
                     release="T33Release.uo",
                     ext="T33Ext.uo")  # ext: candidate only
# The probe module (the bare name `hol run` is given) -> the record probe.
PROBE_OF_MODULE = {t[:-3]: p for p, t in PROBE_TARGETS.items()}
# The variable that names the GC log of a storage probe (T33.sml gclog_env;
# a test compares the two).
GCLOG_ENV = "T33_GCLOG"
CONTROLS = ("T33_GRAPH_EXTRA", "T33_LEAK", "T33_HOOK")
SWITCHES = ("graph_extra", "leak", "hook")
# The probes in which a control switch is visible in the records.
CONTROL_PROBES = dict(graph_extra=("graph", "ext"), leak=("release", "ext"),
                      hook=("registry", "ext"))

# The registry lists L3 compares (the ordered listeners, the sorted rest).
L3_LISTS = ("listeners", "attributes", "set_types", "structures",
            "signatures", "functors")
STARTUP_KINDS = ("state0-empty", "state-empty")
LOAD_KINDS = STARTUP_KINDS + ("load-simpLib", "load-congLib", "first-use")
PROBE_KINDS = dict(load=LOAD_KINDS, registry=LOAD_KINDS,
                   trivial=STARTUP_KINDS, graph=("graph",),
                   release=("release",), ext=("ext",))
DEFAULT_SIZES = (0, 1, 10, 100, 1000, 10000)
STEP_SIZES = (0, 1, 10)
STEP_SPAN = 9  # objects between the sizes 1 and 10
GRAPH_CHECKS = ("fragment", "compiled", "compiled_bool", "merge",
                "projection", "tactic", "exclusion", "removed", "cong")
GRAPH_KINDS = ("fragment", "compiled", "compiled_bool", "merge",
               "projection", "conversion", "tactic", "exclusion", "removed",
               "cong", "cells_cons", "cells_ref")
STEP_MODES = ("built", "canonical")
# The release kind that is the harness's noise floor, not code under test:
# T33_LEAK does not retain its objects and its residual must be exact. The
# SML probes define it once (T33.floor_kind; a test compares the two).
FLOOR_KIND = "noop"
# A GC share-pass lower bound of a residual is admitted only when it is at
# least HALF (words per object): the least residual R1 treats as retained.
# A held size (R1 sensitivity) needs H_MIN words per object. One definition,
# used by `validate` and by task33_rules (`records.HALF`, `records.H_MIN`).
HALF = Fraction(1, 2)
H_MIN = 20
RELEASE_KINDS = (FLOOR_KIND, "simpset", "conversion", "tactic", "traversedata",
                 "exclusion", "removed", "cong")
EXT_CHECKS = ("ext tracked", "ext views", "ext bundle")
EXT_RELEASE_KINDS = (FLOOR_KIND, "ext_tracked", "ext_views", "ext_bundle",
                     "ext_projection", "ext_xprojection")
SIZED = ("ThmAttribute", "Cond_rewr", "simpLib", "Traverse", "Travrules",
         "Opening", "boolSimps", "pureSimps")
DECLARED = ("ThmAttribute", "Cond_rewr")  # D: structure and signature
REPEATS = 3
SHARE_TRIES_MAX = 9  # T33GraphLib `shared`: the first round and 8 more
CONS = 3  # words of a list cell (header, head, tail)
LOAD_CHECK = {"load-simpLib": "SIMP_CONV rule",
              "load-congLib": "CONGRUENCE_EQ_SIMP_CONV rule"}
FIRST_USE = ("first-conv", "second-conv", "first-tac", "second-tac")
HOOK_NAME = "t33.hook"
# A VmHWM reset is verified when VmHWM was above VmRSS by more than this
# before it and is within it of VmRSS after it (a few pages);
# T33GraphLib.sml uses the same constant.
RESET_SLACK = 65536
# The line a full GC writes to the GC log (T33.sml log_marker, log_unit).
LOG_TOTAL = re.compile(r"GC: Mark: Total live data ([0-9]+) words")
# The header of a full GC (T33.sml does not parse it). PolyML.fullGC says
# `0 words required`; a full GC the run time sets off says `n > 0`.
FULL_GC_HEAD = re.compile(
    r"GC: Full GC, ([0-9]+) words required [0-9]+ spaces")
OWN_FULL_GCS = 3  # the full GCs of one reading (T33.sml own_gcs)
WEAK_MIN_FULL_GCS = 4  # one explicit collection, then three


class RecordError(ValueError):
    """A line, record or run that is not well-formed."""


class NotComparable(ValueError):
    """A well-formed process whose readings cannot be compared (alloc or
    gc_share changed inside a release kind, see check_comparable). The
    process is redrawn; it is not a result and not a malformed record."""


def fail(message):
    raise RecordError(message)


# --- field types --------------------------------------------------------

def is_int(value):
    return isinstance(value, int) and not isinstance(value, bool)


def is_uint(value):
    return is_int(value) and value >= 0


def is_real(value):
    return (isinstance(value, (int, float)) and not isinstance(value, bool)
            and value >= 0)


def is_str(value):
    return isinstance(value, str)


def is_bool(value):
    return isinstance(value, bool)


def is_null(test):
    return lambda value: value is None or test(value)


def is_list(test):
    return lambda value: isinstance(value, list) and all(map(test, value))


def is_pair(value):
    return (isinstance(value, list) and len(value) == 2
            and all(map(is_str, value)))


def is_switches(value):
    return (isinstance(value, dict) and set(value) == set(SWITCHES)
            and all(map(is_bool, value.values())))


def is_sizes(value):
    return (isinstance(value, list) and all(
        isinstance(x, dict) and set(x) == {"name", "struct", "sig"}
        and is_str(x["name"]) and is_null(is_uint)(x["struct"])
        and is_null(is_uint)(x["sig"]) for x in value))


def is_anchored(value):
    return (isinstance(value, dict) and
            set(value) == {"d", "d_vals", "total", "rows", "repeat_ok"} and
            is_list(is_str)(value["d"]) and
            is_null(is_list(is_uint))(value["d_vals"]) and
            is_null(is_list(is_uint))(value["total"]) and
            is_null(is_bool)(value["repeat_ok"]) and
            isinstance(value["rows"], list) and all(
                isinstance(x, dict) and set(x) == {"name", "vals"} and
                is_str(x["name"]) and is_null(is_list(is_uint))(x["vals"])
                for x in value["rows"]))


WINDOW_FIELDS = ("rss_before", "hwm_before", "rss_reset", "hwm_reset",
                 "rss_after", "hwm_after")


def is_window(value):
    return (isinstance(value, dict) and
            set(value) == set(WINDOW_FIELDS) | {"reset_ok", "status"} and
            is_bool(value["reset_ok"]) and is_str(value["status"]) and
            all(is_null(is_uint)(value[k]) for k in WINDOW_FIELDS))


FIELDS = dict(
    probe=dict(holdir=is_str, switches=is_switches,
               params=lambda v: isinstance(v, dict)),
    check=dict(check=is_str, ok=is_bool, value=is_str),
    time=dict(label=is_str, cpu=is_real, wall=is_real),
    live=dict(phase=is_str, size_heap=is_uint, free_full=is_uint,
              alloc=is_uint, alloc_free=is_uint, gc_share=is_uint,
              extent=is_int, log_start=is_uint,
              log_end=is_uint, words=is_int),
    registry=dict(loaded=is_list(is_str), files=is_list(is_pair),
                  listeners=is_list(is_str), attributes=is_list(is_str),
                  set_types=is_list(is_str), structures=is_list(is_str),
                  signatures=is_list(is_str), functors=is_list(is_str),
                  sizes=is_sizes, anchored=is_anchored),
    graph=dict(graph=is_str, n=is_uint, anchor=is_uint, anchor_post=is_uint,
               union=is_uint, words=is_int, share=is_uint,
               canon_anchor=is_uint, canon_anchor_post=is_uint,
               canon_union=is_uint, canon_words=is_int, canon_share=is_uint),
    phase=dict(n=is_uint, share_start=is_uint, share_built=is_uint,
               share_shared=is_uint, share_canon=is_uint,
               share_tries=is_uint, converged=is_bool, build=is_window,
               rows=is_window),
    step=dict(graph=is_str, mode=is_str, first=is_int, rest=is_int,
              span=is_uint),
    release=dict(release=is_str, m=is_uint, before=is_uint, after=is_uint,
                 held=is_uint),
    weak=dict(scope=is_str, retained=is_bool, collected=is_bool,
              full_gcs=is_uint, status=is_str),
    done=dict(),
)
COMMON = dict(record=is_str, probe=is_str, kind=is_str)


# --- parsing ------------------------------------------------------------

def pairs(items):
    keys = [k for k, _ in items]
    if len(set(keys)) != len(keys):
        fail("duplicate key in a record")
    return dict(items)


def reject_constant(name):
    fail("non-finite number " + name)


def parse_line(line):
    body = line[len(PREFIX):] if line.startswith(PREFIX) else None
    if body is None:
        fail("malformed @@T33 line: " + line[:80])
    try:
        record = json.loads(body, object_pairs_hook=pairs,
                            parse_constant=reject_constant)
    except ValueError as error:
        fail("bad JSON in a @@T33 line: %s" % error)
    if not isinstance(record, dict):
        fail("a record is not an object")
    check_fields(record)
    return record


def check_fields(record):
    name = record.get("record")
    if name not in FIELDS:
        fail("unknown record type %r" % (name,))
    spec = dict(COMMON, **FIELDS[name])
    if set(record) != set(spec):
        fail("%s: fields %s, expected %s" % (
            name, sorted(record), sorted(spec)))
    for key, test in spec.items():
        if not test(record[key]):
            fail("%s: bad %s: %r" % (name, key, record[key]))


def parse(text):
    """All records of a stdout text, each checked for its own fields."""
    return [parse_line(line) for line in text.splitlines()
            if line.startswith("@@T33")]


# --- the fixed sequence of a process ------------------------------------

def key_of(record):
    name = record["record"]
    if name == "check":
        return (name, record["check"])
    if name == "time":
        return (name, record["label"])
    if name == "live":
        return (name, record["phase"])
    if name == "graph":
        return (name, record["graph"], record["n"])
    if name == "phase":
        return (name, record["n"])
    if name == "step":
        return (name, record["graph"], record["mode"])
    if name == "release":
        return (name, record["release"])
    return (name,)


def has_steps(sizes):
    return all(n in sizes for n in STEP_SIZES)


def size_keys(sizes):
    keys = [("live", "start")]
    for n in sizes:
        keys += [("check", "%s %d" % (c, n)) for c in GRAPH_CHECKS]
        keys += [("graph", g, n) for g in GRAPH_KINDS]
        keys += [("live", "graph.%d" % n), ("phase", n)]
    if has_steps(sizes):
        keys += [("step", g, m) for m in STEP_MODES for g in GRAPH_KINDS]
    return keys + [("live", "end")]


def release_keys(kinds):
    keys = []
    for k in kinds:
        keys += [("live", k + ".before"), ("live", k + ".after"),
                 ("live", k + ".held"), ("release", k)]
    return keys


def load_keys(kind):
    if kind in LOAD_CHECK:
        return [("time", "load"), ("check", LOAD_CHECK[kind])]
    if kind == "first-use":
        return [key for label in FIRST_USE
                for key in (("time", label), ("check", label))]
    return []


def expected_keys(probe, kind, params):
    """The exact key sequence of a well-formed process."""
    if probe in ("load", "registry"):
        keys = load_keys(kind)
        if probe == "registry":
            keys += [("live", "registry"), ("registry",)]
    elif probe == "trivial":
        keys = []
    elif probe == "graph":
        keys = size_keys(params["sizes"])
    elif probe == "release":
        keys = ([("live", "start")] + release_keys(RELEASE_KINDS) +
                [("weak",)])
    elif probe == "ext":
        keys = ([("check", c) for c in EXT_CHECKS] +
                [("live", "ext.start")] + release_keys(EXT_RELEASE_KINDS) +
                size_keys(params["sizes"]) +
                [("live", "registry"), ("registry",)])
    else:
        fail("unknown probe %r" % probe)
    return [("probe",)] + keys + [("done",)]


def check_params(probe, kind, params):
    def sizes_ok(sizes):
        return (is_list(is_uint)(sizes) and sizes and
                all(a < b for a, b in zip(sizes, sizes[1:])))
    if probe in ("load", "registry", "trivial"):
        module = kind[5:] if kind.startswith("load-") else None
        ok = params == {"module": module}
    elif probe == "graph":
        ok = set(params) == {"sizes"} and sizes_ok(params["sizes"])
    elif probe == "release":
        ok = (set(params) == {"m"} and is_uint(params["m"]) and
              params["m"] >= 1)
    else:
        ok = (set(params) == {"m", "sizes"} and sizes_ok(params["sizes"])
              and is_uint(params["m"]) and params["m"] >= 1)
    if not ok:
        fail("%s/%s: bad params %r" % (probe, kind, params))


# --- invariants ---------------------------------------------------------

def check_live(record):
    """The extent is the formula of its fields (reported only), words is a
    non-negative count (the log check compares it with the log)."""
    extent = (record["size_heap"] - record["free_full"] -
              record["alloc"]) // 8
    if record["extent"] != extent:
        fail("live %s: extent %d, formula gives %d" % (
            record["phase"], record["extent"], extent))
    if record["words"] < 0:
        fail("live %s: words %d" % (record["phase"], record["words"]))


def gc_log_totals(text):
    """The marked live totals of the full GCs in a piece of GC log, in
    order: one per line that is exactly `GC: Mark: Total live data <N>
    words`."""
    return [int(m.group(1)) for line in text.split("\n")
            for m in [LOG_TOTAL.fullmatch(line)] if m]


def check_gc_log(live, log):
    """Check every `live` record (`live`: the records in output order)
    against the GC log `log`, the slice log[log_start:log_end] of each (see
    The GC log). RecordError when `prev <= log_start < log_end <= len(log)`
    fails (prev: the previous record's log_end, 0 at first), a slice
    does not start and end on line boundaries, does not end with a total
    line, does not hold exactly OWN_FULL_GCS totals, or words is not the
    last. NotComparable, raised after all records are checked, when a
    slice is not exactly OWN_FULL_GCS headers `0 words required`."""
    if not isinstance(log, str):
        fail("missing GC log")
    prev = 0
    redraws = []
    for r in live:
        name, start, end = r["phase"], r["log_start"], r["log_end"]
        if not prev <= start < end <= len(log):
            fail("live %s: log_start %d, log_end %d, not %d <= start < "
                 "end <= %d (the GC log's length)" % (
                     name, start, end, prev, len(log)))
        if start and log[start - 1] != "\n":
            fail("live %s: log_start %d is not a line start" % (
                name, start))
        if log[end - 1] != "\n":
            fail("live %s: log_end %d is not a line end" % (name, end))
        lines = log[start:end - 1].split("\n")
        totals = gc_log_totals("\n".join(lines))
        if len(totals) != OWN_FULL_GCS or not LOG_TOTAL.fullmatch(lines[-1]):
            fail("live %s: %d full GC total(s) in its GC log slice, not "
                 "exactly %d with the last line a total" % (
                     name, len(totals), OWN_FULL_GCS))
        if r["words"] != totals[-1]:
            fail("live %s: words %d, the GC log's marked total (of the "
                 "slice's third full GC) is %d" % (
                     name, r["words"], totals[-1]))
        heads = [int(m.group(1)) for line in lines
                 for m in [FULL_GC_HEAD.fullmatch(line)] if m]
        if len(heads) != OWN_FULL_GCS or any(heads):
            redraws.append(
                "live %s: the GC log slice has full GC headers with "
                "words required %s, not %d own ones (0): a run-time GC "
                "or a repeated mark in the reading" % (
                    name, heads, OWN_FULL_GCS))
        prev = end
    if redraws:
        raise NotComparable("; ".join(redraws))


def check_graph(record):
    n = record["n"]
    for mode, a, u, w in (("built", "anchor", "union", "words"),
                          ("canonical", "canon_anchor", "canon_union",
                           "canon_words")):
        if record[u] < record[a] or record[w] != record[u] - record[a]:
            fail("graph %s %d (%s): union %d, anchor %d, words %d" % (
                record["graph"], n, mode, record[u], record[a], record[w]))
        if record["graph"] == "cells_cons" and record[w] != 3 * n:
            fail("cells_cons %d (%s): %d words, expected 3 per input" % (
                n, mode, record[w]))
    if not record["share"] <= record["canon_share"]:
        fail("graph %s %d: share counts decrease" % (record["graph"], n))


def check_cells(rows):
    for n, cons in rows["cells_cons"].items():
        ref = rows["cells_ref"][n]
        for mode, a, w in (("built", "anchor", "words"),
                           ("canonical", "canon_anchor", "canon_words")):
            if ref[a] != cons[a]:
                fail("cells %d (%s): different anchors" % (n, mode))
            if ref[w] - cons[w] != 2 * n:
                fail("cells %d (%s): a reference is not 2 words per input"
                     % (n, mode))


def reset_verified(window):
    """A reset counts only if the write succeeded, there was something to
    reset (VmHWM above VmRSS by more than the slack before it) and VmHWM is
    back within the slack of VmRSS after it."""
    values = [window[k] for k in WINDOW_FIELDS]
    return (window["reset_ok"] and None not in values and
            window["hwm_before"] - window["rss_before"] > RESET_SLACK and
            abs(window["hwm_reset"] - window["rss_reset"]) <= RESET_SLACK)


def check_window(n, name, window):
    for stage in ("before", "reset", "after"):
        rss, hwm = window["rss_" + stage], window["hwm_" + stage]
        # VmHWM is max(peak, current RSS) in any single read.
        if rss is not None and hwm is not None and hwm < rss:
            fail("phase %d %s: VmHWM below VmRSS (%s)" % (n, name, stage))
    wanted = "ok" if reset_verified(window) else "unsupported"
    if window["status"] != wanted:
        fail("phase %d %s: status %r, values give %r" % (
            n, name, window["status"], wanted))


def check_phase(record):
    shares = [record[k] for k in ("share_start", "share_built",
                                  "share_shared", "share_canon")]
    if shares != sorted(shares):
        fail("phase %d: share counts decrease" % record["n"])
    if not 1 <= record["share_tries"] <= SHARE_TRIES_MAX:
        fail("phase %d: share_tries %d outside 1..%d" % (
            record["n"], record["share_tries"], SHARE_TRIES_MAX))
    if not record["converged"] and record["share_tries"] != SHARE_TRIES_MAX:
        fail("phase %d: not converged after %d sharing rounds, but the "
             "probe stops only after %d" % (
                 record["n"], record["share_tries"], SHARE_TRIES_MAX))
    for name in ("build", "rows"):
        check_window(record["n"], name, record[name])


def check_weak(record):
    if record["status"] not in ("pass", "blocked"):
        fail("weak: status %r" % record["status"])
    if (record["status"] == "pass") != (record["collected"] and
                                        record["retained"]):
        fail("weak: status %r with retained=%s collected=%s" % (
            record["status"], record["retained"], record["collected"]))
    if record["full_gcs"] < WEAK_MIN_FULL_GCS:
        fail("weak: %d full GCs, at least %d expected" % (
            record["full_gcs"], WEAK_MIN_FULL_GCS))


def constant(values):
    return all(v == values[0] for v in values)


def check_anchored(record):
    """The anchored structure decomposition; returns its summary."""
    anchored = record["anchored"]
    sizes = {x["name"]: x for x in record["sizes"]}
    if anchored["d"] != list(DECLARED):
        fail("registry: anchor set %r, expected %r" % (
            anchored["d"], list(DECLARED)))
    others = [n for n in SIZED if n not in DECLARED]
    if [x["name"] for x in anchored["rows"]] != others:
        fail("registry: anchored rows are not for %s" % (others,))
    d_vals = anchored["d_vals"]
    if d_vals is not None and len(d_vals) != REPEATS:
        fail("registry: d_vals has %d repeats, expected %d" % (
            len(d_vals), REPEATS))
    values = {}
    for row in anchored["rows"]:
        vals = row["vals"]
        if vals is not None and len(vals) != REPEATS:
            fail("registry: %s has %d repeats" % (row["name"], len(vals)))
        if (vals is None) != (d_vals is None or
                              sizes[row["name"]]["struct"] is None):
            fail("registry: %s anchored values and sizes disagree" %
                 row["name"])
        values[row["name"]] = vals
    total = anchored["total"]
    if total is not None and len(total) != REPEATS:
        fail("registry: total has %d repeats, expected %d" % (
            len(total), REPEATS))
    if d_vals is None and total is not None:
        fail("registry: a total without D")
    if (total is None) != (d_vals is None or any(
            v is None for v in values.values())):
        fail("registry: the total and the anchored values disagree")
    if total is not None:
        for i in range(REPEATS):
            rows = [v[i] for v in values.values()]
            union = total[i] - d_vals[i] - CONS * len(rows)
            if not max(rows) <= union <= sum(rows):
                fail("registry: total %d (repeat %d) is not between the "
                     "largest and the sum of the exclusive parts (%d, %d)"
                     % (total[i], i, max(rows), sum(rows)))
    repeat = None if d_vals is None else (
        constant(d_vals) and (total is None or constant(total)) and
        all(constant(v) for v in values.values() if v is not None))
    if anchored["repeat_ok"] != repeat:
        fail("registry: repeat_ok %s, values give %s" % (
            anchored["repeat_ok"], repeat))
    return dict(d=d_vals, total=total, rows=values, repeat_ok=repeat)


def check_registry(record, switches):
    if (HOOK_NAME in record["listeners"]) != switches["hook"]:
        fail("registry: %s listener does not match the hook switch" %
             HOOK_NAME)
    if [x["name"] for x in record["sizes"]] != list(SIZED):
        fail("registry: sizes are not for %s" % (SIZED,))
    for key in ("structures", "signatures", "functors"):
        if record[key] != sorted(record[key]):
            fail("registry: %s not sorted" % key)
    return check_anchored(record)


def check_steps(steps, graph):
    """steps: {graph: {mode: record}}. Cross-check against the rows and
    return {graph: {mode: dict(first, rest, span, match)}}."""
    out = {}
    for g, modes in steps.items():
        for mode, r in modes.items():
            field = "words" if mode == "built" else "canon_words"
            w = [graph[g][n][field] for n in STEP_SIZES]
            if (r["first"], r["rest"], r["span"]) != (
                    w[1] - w[0], w[2] - w[1], STEP_SPAN):
                fail("step %s %s: record disagrees with the rows" % (
                    g, mode))
            out.setdefault(g, {})[mode] = dict(
                first=r["first"], rest=r["rest"], span=r["span"],
                match=r["rest"] == r["span"] * r["first"])
    return out


def check_gateable(graph, phase):
    """Per size: which windows are free of GC share passes. Returns
    (gateable, coverage, moved). The anchors must not move (released =
    anchor): the canonical pre-anchor (`anchor`, measured on fully shared
    inputs) against the canonical anchor of the rows whatever passes ran,
    that against the canonical post-anchor and the as-built post-anchor
    against `anchor` where no pass ran. A move is not an error: `moved`
    lists {kind, n, mode, pre, post}, and the as-built rows of a moved
    kind and size are not gateable (`coverage`: kind -> sorted sizes
    whose as-built rows are gateable)."""
    gateable, moved = {}, []
    coverage = {g: [] for g in graph}
    for n, p in phase.items():
        built = p["share_start"] == p["share_built"]
        canonical = p["share_shared"] == p["share_canon"]
        for g, by_size in graph.items():
            r = by_size[n]
            if not p["share_start"] <= r["share"] <= p["share_built"]:
                fail("graph %s %d: share %d outside its window" % (
                    g, n, r["share"]))
            if r["canon_share"] != p["share_canon"]:
                fail("graph %s %d: canon_share %d, phase says %d" % (
                    g, n, r["canon_share"], p["share_canon"]))
            built_moved = built and r["anchor_post"] != r["anchor"]
            if built_moved:
                moved.append(dict(kind=g, n=n, mode="built",
                                  pre=r["anchor"], post=r["anchor_post"]))
            if r["canon_anchor"] != r["anchor"]:
                moved.append(dict(kind=g, n=n, mode="canonical",
                                  pre=r["anchor"], post=r["canon_anchor"]))
            elif canonical and r["canon_anchor_post"] != r["canon_anchor"]:
                moved.append(dict(kind=g, n=n, mode="canonical",
                                  pre=r["canon_anchor"],
                                  post=r["canon_anchor_post"]))
            if built and not built_moved:
                coverage[g].append(n)
        gateable[n] = dict(built=built, canonical=canonical)
    return gateable, coverage, moved


def check_controls(probe, active, controls):
    expected = set(controls)
    if not expected <= set(SWITCHES):
        fail("unknown control switches %s" % sorted(expected - set(SWITCHES)))
    if set(active) != expected:
        fail("control switches %s, expected %s" % (
            ",".join(active) or "none", ",".join(sorted(expected)) or "none"))
    for name in expected:
        if probe not in CONTROL_PROBES[name]:
            fail("control %s is inert in the %s probe" % (name, probe))


def validate(text, controls=(), root=None, gclog=None):
    """Parse and validate the stdout of one probe process; return the
    summary. `controls`: the control switches (names of SWITCHES) the
    process is expected to run with, exactly. `root`: the snapshot root the
    process must report as holdir. `gclog`: the process's GC log (a str),
    required when it has `live` records (check_gc_log). Raises RecordError
    for a malformed run and NotComparable for a well-formed one whose
    readings cannot be compared."""
    records = parse(text)
    if not records or records[0]["record"] != "probe":
        fail("the first record is not the probe header")
    head = records[0]
    probe, kind, params = head["probe"], head["kind"], head["params"]
    if probe not in PROBE_KINDS or kind not in PROBE_KINDS[probe]:
        fail("unknown probe/kind %r/%r" % (probe, kind))
    if root is not None and head["holdir"] != str(root):
        fail("holdir %r is not %r" % (head["holdir"], str(root)))
    active = [s for s in SWITCHES if head["switches"][s]]
    check_controls(probe, active, controls)
    check_params(probe, kind, params)
    for record in records:
        if record["probe"] != probe or record["kind"] != kind:
            fail("a record of %s/%s inside %s/%s" % (
                record["probe"], record["kind"], probe, kind))
    want = expected_keys(probe, kind, params)
    got = [key_of(r) for r in records]
    for i, (a, b) in enumerate(zip(got, want)):
        if a != b:
            fail("record %d is %r, expected %r" % (i, a, b))
    if len(got) != len(want):
        fail("%d records, expected %d (next %r)" % (
            len(got), len(want),
            want[len(got)] if len(got) < len(want) else got[len(want)]))
    summary = dict(probe=probe, kind=kind, switches=head["switches"],
                   params=params, holdir=head["holdir"], checks=[],
                   times={}, live={}, share={}, alloc={}, graph={},
                   release={}, residual={}, held={}, phase={}, step={},
                   residual_bound={}, held_bound={},
                   gateable={}, gateable_coverage={}, anchor_moved=[],
                   held_comparable={}, unconverged=[], weak=None,
                   registry=None, anchored=None)
    steps = {}
    for r in records:
        name = r["record"]
        if name == "check":
            if not r["ok"]:
                fail("failed check: " + r["check"])
            summary["checks"].append(r["check"])
        elif name == "time":
            summary["times"][r["label"]] = dict(cpu=r["cpu"], wall=r["wall"])
        elif name == "live":
            check_live(r)
            summary["live"][r["phase"]] = r["words"]
            summary["share"][r["phase"]] = r["gc_share"]
            summary["alloc"][r["phase"]] = r["alloc"]
        elif name == "graph":
            check_graph(r)
            summary["graph"].setdefault(r["graph"], {})[r["n"]] = r
        elif name == "phase":
            check_phase(r)
            summary["phase"][r["n"]] = r
            if not r["converged"]:
                summary["unconverged"].append(r["n"])
        elif name == "step":
            if r["mode"] not in STEP_MODES or r["span"] != STEP_SPAN:
                fail("step %s: bad mode or span" % r["graph"])
            steps.setdefault(r["graph"], {})[r["mode"]] = r
        elif name == "release":
            summary["release"][r["release"]] = r
        elif name == "weak":
            check_weak(r)
            summary["weak"] = r
        elif name == "registry":
            summary["anchored"] = check_registry(r, head["switches"])
            summary["registry"] = r
    if summary["graph"]:
        check_cells(summary["graph"])
        (summary["gateable"], summary["gateable_coverage"],
         summary["anchor_moved"]) = check_gateable(summary["graph"],
                                                   summary["phase"])
        summary["step"] = check_steps(steps, summary["graph"])
    for kind_name, r in summary["release"].items():
        for field, phase in (("before", ".before"), ("after", ".after"),
                             ("held", ".held")):
            if r[field] != summary["live"][kind_name + phase]:
                fail("release %s: %s differs from its live record" % (
                    kind_name, field))
        if r["m"] != params["m"]:
            fail("release %s: m %d, declared %d" % (
                kind_name, r["m"], params["m"]))
        summary["residual"][kind_name] = Fraction(
            r["after"] - r["before"], r["m"])
        summary["held"][kind_name] = Fraction(r["held"] - r["after"], r["m"])
    for n in summary["phase"]:
        if "graph.%d" % n not in summary["live"]:
            fail("phase %d without its live record" % n)
    live = [r for r in records if r["record"] == "live"]
    if live:
        check_gc_log(live, gclog)
    check_comparable(summary["release"], records, summary)
    if summary["unconverged"]:
        raise NotComparable(
            "the canonical pre-anchor did not converge at size(s) %s (after "
            "%s sharing rounds): a harness reading, not a moved anchor" % (
                summary["unconverged"], ", ".join(
                    str(summary["phase"][n]["share_tries"])
                    for n in summary["unconverged"])))
    return summary


def check_comparable(release, records, summary):
    """Per release kind (the module docstring, Release readings and share
    passes): the before and after readings must have the same allocation
    area and a non-shrinking GC share-pass count; with more passes the
    residual is a lower bound, admitted only when >= HALF and not for the
    floor kind. Fills `residual_bound`, `held_bound` and `held_comparable`
    of the summary. The share-pass rule lives here, in the one validator
    that a run and its replay share."""
    live = {r["phase"]: r for r in records if r["record"] == "live"}
    for name in release:
        pair = lambda p: (live[name + p]["alloc"], live[name + p]["gc_share"])
        (ba, bs), (aa, as_), (ha, hs) = (pair(".before"), pair(".after"),
                                         pair(".held"))
        if ba != aa or as_ < bs:
            raise NotComparable(
                "release %s: the allocation area differs or the GC share "
                "count shrank between its before and after readings: %s" % (
                    name, [(ba, bs), (aa, as_)]))
        bound = as_ != bs
        if bound:
            if name == FLOOR_KIND:
                raise NotComparable(
                    "release %s: a GC share pass between the readings of "
                    "the noise floor (it must be exact)" % name)
            if summary["residual"][name] < HALF:
                raise NotComparable(
                    "release %s: a GC share pass between the readings and "
                    "the residual bound %s is under %s" % (
                        name, summary["residual"][name], HALF))
        summary["residual_bound"][name] = bound
        held_bound = hs > as_
        summary["held_bound"][name] = held_bound
        summary["held_comparable"][name] = (
            ha == aa and hs >= as_
            and (not held_bound or summary["held"][name] >= H_MIN))


# --- masking ------------------------------------------------------------
# The rule (`mask_path`, `mask_text`, ROOT_MASK, PROBE_MASK) lives in
# task32_downstream.py, whose seal TASK32 replay checks. It is imported when
# used: that module imports task33_cases, which imports this one.

def downstream():
    import task32_downstream
    return task32_downstream


def mask_path(path, root, probe_dir):
    """task32_downstream.mask_path, a misplaced prefix as RecordError."""
    try:
        return downstream().mask_path(path, root, probe_dir)
    except ValueError as error:
        fail(str(error))


def mask_text(text, root, probe_dir):
    """task32_downstream.mask_text, a misplaced prefix as RecordError."""
    try:
        return downstream().mask_text(text, root, probe_dir)
    except ValueError as error:
        fail(str(error))


def __getattr__(name):
    if name in ("ROOT_MASK", "PROBE_MASK"):
        return getattr(downstream(), name)
    raise AttributeError(name)


# --- digest -------------------------------------------------------------

def normalized_checks(text):
    """The kernel-check lines of a probe's stdout, normalized for the digest
    of a probe unit: `probe<TAB>kind<TAB>check<TAB>value`, in order, no
    timing. The value is the evidence (the printed theorems). Refuses a
    failed check."""
    lines = []
    for r in parse(text):
        if r["record"] != "check":
            continue
        if not r["ok"]:
            fail("failed check: " + r["check"])
        lines.append("\t".join((r["probe"], r["kind"], r["check"],
                                r["value"])))
    return lines


def digest(text):
    """sha256 of the normalized check lines."""
    return hashlib.sha256(
        "\n".join(normalized_checks(text)).encode()).hexdigest()
