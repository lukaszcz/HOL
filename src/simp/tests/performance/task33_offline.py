#!/usr/bin/env python3
"""TASK33 offline checks (slice S3): no process, no build, no measurement.

  archive  the TASK32 first-stage archive, read offline: its seals (the
           TASK32 replay, `task32_downstream.replay_one`), per unit and
           side the GC counts, GC time, size_heap and maxrss (medians,
           ranges, paired ratios), the cross-side masked loaded-set
           equality of every unit (case L1) and the attribution data of
           the `lim` GC CPU interval (question Q10);
  audit    the static closure of both snapshots (case L2): the transitive
           `.uo`/`.ui` dependency lists of simpLib, congLib, bossLib and
           the heap DEPS in each `sigobj`, no extension module, equal names
           on both sides, and the git source blobs of that closure equal
           except the declared set; the hidden-root scan of the B..C diff
           (R2) and the type/record classification (R3), both against
           task33_declared.json;
  harvest  copies and seals (gzip + sha256 manifest) the candidate
           snapshot's `-t` build logs and checks that each shows its suite
           passed (E1).

Every subcommand writes one JSON report (`--out FILE.json`, or a
directory that receives `<command>.json`) and, next to it, the seal of
that report (`<report>.seal`).  Exit status: 0 pass, 2 inconclusive (a
check was skipped, e.g. `archive --no-replay`: the report is not a pass
and S4 refuses it), 3 fail or refused (including a report that cannot be
written).  A check has `status` pass, fail or skipped; the report
succeeds when no check failed or was skipped.  Reports are never
overwritten.  Every report carries `code`: the seals of this file, of
the declaration (`--declared`, default task33_declared.json) and of the
TASK32 code it reuses (`check_code`).

`audit` and `harvest` are bound to the TASK32 snapshot manifest
(`--manifest`, required): each root is that side's snapshot root, the
declared pins are the manifest's, and the build commands exited 0.

Interface for the disposition (S4): see the schema notes at REPORT_NOTES.
"""
import argparse
import contextlib
import difflib
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import loading
import task32_downstream as d
import task33_records as records

SCHEMA = "task33-offline-v1"
DECLARED_SCHEMA = "task33-declared-v4"
DEFAULT_DECLARED = HERE / "task33_declared.json"
DECLARED = DEFAULT_DECLARED
# The declaration this process uses (`using_declared`, for the length of a
# command; the storage driver's `--declared` or its table's). TASK33's own
# is the default, so its records replay; TASK37 declares its revision in
# task37_declared.json (task37_declared.py). A report is bound to the
# declaration it was made under (`code_paths`).
PASS, INCONCLUSIVE, FAIL = 0, 2, 3
STATUSES = ("pass", "fail", "skipped")
REPORT_NOTES = """\
report: {schema, command, success, exit, checks, inputs, data, code}
check:  {id, case, status, reason}   status in pass/fail/skipped
archive data: units[unit].sides[base|cand|control].fields[f] =
  {n, median, min, max}; units[unit].paired[f] = {median_paired_ratio,
  reported?}; units[unit].loaded = {base_variants, cand_variants, equal};
  attribution[unit] for each unit whose GC CPU interval is above 1
audit data: closure[side] = {modules, sources}; differing = [path];
  declared; r2 hits; r3 kinds
harvest data: files[i] = {path, sha256, bytes, gz, gz_seal, rule, passed}
"""
GC_FIELDS = ("gc_full", "gc_partial", "gc_share", "gc_time", "size_heap")
ALL_FIELDS = GC_FIELDS + ("maxrss",)
REPORTED = {"gc_time": "gc_cpu", "maxrss": "maxrss"}
Q10_UNIT = "lim"
ABOVE = 1.03  # TASK32 policy margin: a reported interval wholly above it


class Refusal(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise Refusal(message)


class Checks:
    def __init__(self):
        self.rows = []

    def add(self, ident, case, status, reason=""):
        assert status in STATUSES
        self.rows.append(dict(id=ident, case=case, status=status,
                              reason=reason))

    def ok(self, ident, case, ok, reason_if_fail, reason_if_ok=""):
        self.add(ident, case, "pass" if ok else "fail",
                 reason_if_ok if ok else reason_if_fail)
        return bool(ok)

    def failed(self):
        return [r for r in self.rows if r["status"] == "fail"]


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def dumps(value):
    return json.dumps(value, indent=2, allow_nan=False,
                      sort_keys=True) + "\n"


# ------------------------------------------------------------- reports

def report_path(out, command):
    out = Path(out)
    if out.suffix == ".json":
        return out
    return out / (command + ".json")


# The archive, the code seals and the seal history are TASK32's, whichever
# table of the driver is active when this module is imported or used (the
# storage driver runs with task33 selected): this module binds to the
# `task32` table explicitly (`archive_report` runs under it).
T32 = d.TABLES["task32"]
# The tables whose archives the `archive` report accepts: the TASK32 proof
# builds of the C32 gate and of TASK37 (each is replayed under its own
# table: its counts, ledger and code).
ARCHIVE_TABLES = ("task32", "task37-t32")
# The code a report is bound to: this file, the declaration, and the
# TASK32 code it reuses (a record made by an earlier version of a TASK32
# file is accepted as task32_downstream.check_code accepts it).
OWN_CODE = ("task33_offline.py", "task33_declared.json")
CODE = OWN_CODE + tuple(T32.code)


def code_paths():
    """{name: path} of the code a report made now is bound to: `CODE`, with
    the declaration actually selected (`DECLARED`, by its own name) in the
    place of TASK33's."""
    return {(DECLARED.name if n == DEFAULT_DECLARED.name else n):
            (DECLARED if n == DEFAULT_DECLARED.name else HERE / n)
            for n in CODE}


def code_seals():
    return {n: a.seal(p) for n, p in code_paths().items()}


def check_code(recorded):
    now = code_seals()
    require(isinstance(recorded, dict) and set(recorded) == set(now),
            "the recorded code is not " + ", ".join(now))
    # TASK33's history is accepted besides TASK32's, for the files of this
    # CODE it names (`task32_downstream.py`, this file): the reports of the
    # kept TASK33 records carry the versions that made them. Only under
    # TASK33's own declaration: TASK37's reports have no history.
    own = DECLARED == DEFAULT_DECLARED
    known = {n: list(T32.history.get(n, ())) +
             list(d.TASK33_HISTORY.get(n, ())) if own else []
             for n in now}
    changed = [n for n in now if recorded[n] != now[n] and
               recorded[n] not in known[n]]
    require(not changed, "the code changed since the report was made: " +
            ", ".join(changed))


def exit_of(checks):
    if checks.failed():
        return FAIL
    if any(r["status"] == "skipped" for r in checks.rows):
        return INCONCLUSIVE
    return PASS


def write_report(out, command, checks, inputs, data):
    """Write the report and its seal; never overwrite. Returns (report,
    path, seal)."""
    code = exit_of(checks)
    report = dict(schema=SCHEMA, command=command, success=code == PASS,
                  exit=code, checks=checks.rows, inputs=inputs, data=data,
                  code=code_seals())
    path = report_path(out, command)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as stream:
        stream.write(dumps(report))
    seal = a.seal(path)
    with Path(str(path) + ".seal").open("x") as stream:
        stream.write(dumps(seal))
    return report, path, seal


def summary_line(command, report, path, seal):
    failed = [r["id"] for r in report["checks"] if r["status"] == "fail"]
    skipped = [r["id"] for r in report["checks"]
               if r["status"] == "skipped"]
    word = "PASS" if report["success"] else \
        "INCONCLUSIVE" if not failed else "FAIL"
    return "%s: %s (%d checks, %d failed%s%s) %s sha256=%s" % (
        command, word, len(report["checks"]), len(failed),
        ": " + ", ".join(failed) if failed else "",
        "; skipped: " + ", ".join(skipped) if skipped else "", path,
        seal["sha256"])


# ------------------------------------------------------------- declared

TEXT_KEYS = ("note", "log_counts_note", "mechanism", "justification",
             "reference", "rule", "created_by", "where", "slots")


def join_text(value):
    """Long prose is stored as lists of fragments (short lines): one
    string again."""
    if isinstance(value, dict):
        return {k: " ".join(v) if k in TEXT_KEYS and isinstance(v, list)
                else join_text(v) for k, v in value.items()}
    if isinstance(value, list):
        return [join_text(v) for v in value]
    return value


def use_declared(path):
    """Select the declaration the storage stages seal and judge by
    (`DECLARED`, read at call time). Returns the previous one."""
    global DECLARED
    previous = DECLARED
    DECLARED = Path(path).resolve()
    return previous


@contextlib.contextmanager
def using_declared(path):
    """`use_declared(path)` for the length of a block, the previous one
    restored whatever happens; `None` selects nothing."""
    if path is None:
        yield
        return
    previous = use_declared(path)
    try:
        yield
    finally:
        use_declared(previous)


def load_declared(path=None):
    path = Path(path or DECLARED)
    require(path.is_file(), "no declaration file: %s" % path)
    data = join_text(json.loads(path.read_text()))
    require(data.get("schema") == DECLARED_SCHEMA,
            "declaration of another schema")
    for key in ("base", "cand", "l2", "allowlist", "s2", "e2c",
                "log_counts"):
        require(key in data, "declaration lacks " + key)
    for entry in data["l2"]:
        for key in ("path", "base_blob", "cand_blob", "mechanism",
                    "justification", "allowed_kinds", "type_change",
                    "new_root"):
            require(key in entry, "declared entry lacks %s: %s" % (
                key, entry.get("path")))
    return data


def nonempty(value):
    return isinstance(value, str) and bool(value.strip())


def total_delta_problems(entries, structures):
    """The shape of `s2.total_delta`, the declared changes of the closure
    total U of the structure gate: a non-empty list of entries, each for
    one heap and some registry kinds of it (`heap`, `kinds`), no (heap,
    kind) in two entries; the entry is `entry_problems`. Which (heap, kind)
    registry records compute U is not decided here: S4 requires every one
    of them to be covered, and refuses a pair that no entry covers."""
    if not isinstance(entries, list) or not entries:
        return ["s2.total_delta is not a non-empty list of entries"]
    bad, seen = [], set()
    for i, entry in enumerate(entries):
        where = "s2.total_delta[%d]" % i
        bad += entry_problems(entry, structures, where)
        if not isinstance(entry, dict):
            continue
        heap, kinds = entry.get("heap"), entry.get("kinds")
        if not nonempty(heap) or not isinstance(kinds, list) or \
                not kinds or not all(k in records.LOAD_KINDS
                                     for k in kinds) or \
                len(set(kinds)) != len(kinds):
            bad.append("%s: heap and kinds are not a heap and distinct "
                       "registry kinds (%s)" % (
                           where, ", ".join(records.LOAD_KINDS)))
            continue
        for kind in kinds:
            if (heap, kind) in seen:
                bad.append("%s: (%s, %s) is declared twice" % (
                    where, heap, kind))
            seen.add((heap, kind))
    return bad


def entry_problems(entry, structures, where):
    """One scoped entry of `s2.total_delta`: a positive integer number of
    words (`value`) that is the observed candidate minus baseline total,
    with its mechanism (code and type structure only: no state, nothing per
    object), and the observed exclusive parts, none of which grows."""
    if not isinstance(entry, dict):
        return [where + " is not an object"]
    bad = []
    nat = lambda x: type(x) is int and x > 0
    obs = entry.get("observed")
    if entry.get("pending"):
        bad.append(where + ": pending, the live measurement is not "
                   "filled in (task37_declared.py fill)")
    elif type(entry.get("value")) is not int or entry["value"] <= 0 or \
            entry.get("unit") != "words":
        bad.append(where + ": value is not a positive integer of words")
    if not isinstance(obs, dict) or not all(
            nat(obs.get(k)) for k in ("base", "cand", "d_base", "d_cand")):
        bad.append(where + ": observed totals are not positive integers")
    elif obs["cand"] - obs["base"] != entry.get("value"):
        bad.append(where + ": value is not observed cand - base")
    others = [n for n in records.SIZED if n not in records.DECLARED]
    excl = obs.get("exclusive") if isinstance(obs, dict) else None
    if not isinstance(excl, dict) or sorted(excl) != sorted(others) or \
            not all(isinstance(v, list) and len(v) == 2 and
                    all(type(x) is int and x >= 0 for x in v) and
                    v[1] <= v[0] for v in excl.values()):
        bad.append("%s: observed exclusive parts are not a [base, cand] "
                   "pair with cand <= base for each of %s" % (
                       where, ", ".join(others)))
    if not nonempty(entry.get("mechanism")) or \
            not nonempty(entry.get("rule")) or \
            not nonempty(entry.get("reference")):
        bad.append(where + " lacks mechanism, rule or reference")
    known = {x for e in structures if isinstance(e, dict)
             for x in e.get("paths", ()) if isinstance(x, str)}
    paths = entry.get("paths")
    if not isinstance(paths, list) or not paths or \
            set(paths) != known:
        bad.append(where + ": paths are not those of the declared "
                   "structures")
    if entry.get("allowed_kinds") != ["code"] or \
            not {"state", "per-object"} <= set(
                entry.get("forbidden_kinds") or ()):
        bad.append(where + ": allowed kinds must be code only and state "
                   "and per-object forbidden")
    return bad


def shape_problems(declared):
    """The shape of the parts of the declaration that no check reads
    field by field (s2, e2c, allowlist): a malformed one is invalid."""
    bad = []
    for e in declared["allowlist"]:
        if not (isinstance(e, dict) and nonempty(e.get("path")) and
                nonempty(e.get("justification")) and
                all(isinstance(e.get(k), str) and
                    re.fullmatch(r"[0-9a-f]{40}", e[k])
                    for k in ("base_blob", "cand_blob"))):
            bad.append("allowlist entry: %s" % (
                e.get("path") if isinstance(e, dict) else e))
    s2 = declared["s2"]
    if not isinstance(s2, dict) or not isinstance(
            s2.get("structures"), list):
        bad.append("s2 is not {structures: [...], total_delta: [...]}")
        s2 = dict(structures=[])
    else:
        bad += total_delta_problems(s2.get("total_delta"),
                                    s2["structures"])
    for e in s2["structures"]:
        ok = isinstance(e, dict) and nonempty(e.get("structure")) and \
            nonempty(e.get("mechanism")) and \
            isinstance(e.get("parts"), list) and e["parts"] and \
            set(e["parts"]) <= {"struct", "sig"} and \
            isinstance(e.get("paths"), list) and e["paths"] and \
            all(nonempty(x) for x in e["paths"]) and \
            isinstance(e.get("allowed_kinds"), list) and \
            isinstance(e.get("forbidden_kinds"), list) and \
            nonempty(e.get("reference"))
        if ok:
            # the parts are the files of the paths: an opaquely ascribed
            # structure changes with its signature, so a declared
            # structure source belongs to the delta as much as its .sig
            ok = ("struct" in e["parts"]) == any(
                x.endswith(".sml") for x in e["paths"]) and \
                ("sig" in e["parts"]) == any(
                    x.endswith(".sig") for x in e["paths"])
        if not ok:
            bad.append("s2 entry: %s" % (
                e.get("structure") if isinstance(e, dict) else e))
    bad += e2c_problems(declared["e2c"])
    bad += count_problems(declared)
    return bad


def register_problems(where, registers):
    """`registers` is {list: [exact names]} over the L3 lists of the
    registry records (records.L3_LISTS): non-empty, each name once."""
    if not isinstance(registers, dict) or not registers:
        return [where + ": registers is not a non-empty map"]
    bad = []
    for f, names in registers.items():
        if f not in records.L3_LISTS or not isinstance(names, list) or \
                not names or not all(nonempty(x) for x in names) or \
                len(set(names)) != len(names):
            bad.append("%s: registers.%s is not a list of distinct names "
                       "of one of %s" % (where, f, records.L3_LISTS))
    return bad


def e2c_problems(e2c):
    """The shape of `e2c` (design 8.6): a rule, `probe_support` (exact
    names the probe's own work adds, with its justification) and
    `extension_state` entries each with `required` and `observable`
    flags. An observable entry names exact registry names; a prose-only
    one (not observable in the registry lists) names none and cannot be
    required."""
    if not isinstance(e2c, dict) or not nonempty(e2c.get("rule")) or \
            not isinstance(e2c.get("extension_state"), list) or \
            not e2c["extension_state"]:
        return ["e2c lacks rule or extension_state"]
    bad = []
    support = e2c.get("probe_support")
    if not isinstance(support, dict) or not nonempty(
            support.get("justification")):
        bad.append("e2c.probe_support lacks a justification")
    else:
        bad += register_problems("e2c.probe_support",
                                 support.get("registers"))
    for e in e2c["extension_state"]:
        name = e.get("name") if isinstance(e, dict) else e
        ok = isinstance(e, dict) and all(
            nonempty(e.get(k)) for k in ("name", "created_by", "where",
                                         "source")) and \
            isinstance(e.get("required"), bool) and \
            isinstance(e.get("observable"), bool)
        if not ok:
            bad.append("e2c entry: %s" % (name,))
            continue
        if e["observable"]:
            bad += register_problems("e2c entry " + name,
                                     e.get("registers"))
        elif e.get("registers") or e["required"]:
            bad.append("e2c entry %s: a state that is not observable "
                       "registers nothing and cannot be required" % name)
    return bad


def count_problems(declared):
    """The reviewed counts of the marker-less suites (`log_counts`: log
    name or path -> positive integer) cover exactly the required logs
    that need one, and `log_skips` names unittest logs only."""
    bad = []
    counts = declared.get("log_counts")
    if not isinstance(counts, dict) or not all(
            type(v) is int and v > 0 for v in counts.values()):
        return ["log_counts is not a map of positive integers"]
    needed = {n for n in LOGS_REQUIRED if needs_count(n)}
    if set(counts) != needed:
        bad.append("log_counts: missing %s, unknown %s" % (
            sorted(needed - set(counts)), sorted(set(counts) - needed)))
    skips = declared.get("log_skips", {})
    unit = {n for n in LOGS_REQUIRED if
            (PATH_RULES.get(n) or LOG_RULES.get(n, ("",)))[0] == "unittest"}
    if not isinstance(skips, dict) or not all(
            type(v) is int and v > 0 for v in skips.values()) or \
            not set(skips) <= unit:
        bad.append("log_skips: not positive integers of unittest logs")
    return bad


def check_declaration(declared, checks):
    """The declaration says what the gates may not accept: a declared type
    change or new root, or an allowed kind that declares a type, is not a
    reviewed difference but an invalid declaration."""
    bad = []
    for entry in declared["l2"]:
        if entry["type_change"] is not False:
            bad.append(entry["path"] + ": type_change is not false")
        if entry["new_root"] is not False:
            bad.append(entry["path"] + ": new_root is not false")
        wrong = sorted(set(entry["allowed_kinds"]) & TYPE_KINDS)
        if wrong:
            bad.append("%s: allowed kinds %s" % (entry["path"], wrong))
    paths = [e["path"] for e in declared["l2"]]
    allow = [e.get("path") for e in declared["allowlist"]
             if isinstance(e, dict)]
    if len(set(paths)) != len(paths) or len(set(allow)) != len(allow):
        bad.append("duplicate declared paths")
    if set(paths) & set(allow):
        bad.append("paths both declared and allowlisted: %s" %
                   sorted(set(paths) & set(allow)))
    for key in ("base", "cand"):
        if not (isinstance(declared[key], str) and
                re.fullmatch(r"[0-9a-f]{40}", declared[key])):
            bad.append("%s is not an exact pin" % key)
    bad += shape_problems(declared)
    checks.ok("declared.valid", "L2/R2/R3", not bad,
              "; ".join(bad), "declaration is well formed")


# ---------------------------------------------------------- provenance

def check_provenance(manifest, roots, declared, checks):
    """The TASK32 manifest binds the roots: each given root is that side's
    snapshot root, the declaration's pins are the manifest's, and every
    command that built the side exited 0. Returns the inputs entry."""
    path = Path(manifest).resolve(strict=True)
    data = a.load(path)
    require(isinstance(data, dict) and data.get("schema") ==
            d.snap.SCHEMA, "not a snapshot manifest: %s" % path)
    sides = data.get("sides")
    require(isinstance(sides, dict) and set(sides) == set(d.snap.LABELS),
            "the manifest has no base and cand sides")
    bad_roots, bad_pins, bad_build = [], [], []
    for label, root in roots.items():
        side = sides[label]
        require(isinstance(side, dict) and isinstance(side.get("root"),
                                                       str) and
                not side.get("incomplete") and side.get("label") == label,
                "incomplete or mislabelled side: " + label)
        if Path(side["root"]).resolve() != Path(root).resolve():
            bad_roots.append("%s: %s is not the manifest's %s" % (
                label, root, side["root"]))
        for key in ("pin", "tree"):
            a.exact_pin(side.get(key))
        if side["pin"] != declared[label]:
            bad_pins.append("%s: manifest %s, declaration %s" % (
                label, side["pin"], declared[label]))
        commands = side.get("commands")
        names = [c.get("name") for c in commands or ()]
        failed = [c.get("name") for c in commands or ()
                  if c.get("exit") != 0]
        if not commands or "build" not in names or failed:
            bad_build.append("%s: %s" % (
                label, "failed " + ", ".join(map(str, failed))
                if failed else "no build command"))
    checks.ok("manifest.roots", "L2/E1", not bad_roots,
              "; ".join(bad_roots), "each root is its side's snapshot "
              "root in the manifest")
    checks.ok("manifest.pins", "L2/E1", not bad_pins,
              "; ".join(bad_pins), "the declared pins are the manifest's")
    checks.ok("manifest.build", "L2/E1", not bad_build,
              "; ".join(bad_build),
              "every build command of the side exited 0")
    return dict(path=str(path), seal=a.seal(path))


# ------------------------------------------------------------------ git

def git_bytes(repo, *argv, stdin=None):
    p = subprocess.run(["git", "-C", str(repo), *argv], input=stdin,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       stdin=None if stdin is not None else
                       subprocess.DEVNULL)
    require(p.returncode == 0, "git %s: %s" % (
        " ".join(argv[:2]), p.stderr.decode(errors="replace").strip()))
    return p.stdout


def blob_ids(repo, commit, paths):
    """path -> blob id at `commit`, None when the path is not tracked
    there (one git process for all paths)."""
    paths = sorted(paths)
    if not paths:
        return {}
    request = "".join("%s:%s\n" % (commit, p) for p in paths).encode()
    out = git_bytes(repo, "cat-file", "--batch-check", stdin=request)
    found = {}
    for path, line in zip(paths, out.decode().splitlines()):
        words = line.split()
        found[path] = words[0] if len(words) == 3 and \
            words[1] == "blob" else None
    return found


def blob_text(repo, commit, path):
    return git_bytes(repo, "cat-file", "blob", "%s:%s" % (commit, path)
                     ).decode("utf-8", errors="replace")


def hash_blob(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


# ----------------------------------------------------- SML text helpers

def strip_comments(text):
    """The text with SML comments (nested) blanked out, newlines kept,
    string and character literals left alone."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "(*":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "*)":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif two == "(*":
            depth = 1
            out.append("  ")
            i += 2
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


# The writes to the global grammars and overload tables: the functions of
# src/parse/Parse.sig that modify the grammar (each also with the `temp_`
# prefix, which changes the grammar for the session only).
GRAMMAR_WRITES = (
    "add_type", "add_qtype", "add_infix_type", "thytype_abbrev",
    "type_abbrev", "disable_tyabbrev_printing", "remove_type_abbrev",
    "type_abbrev_pp", "add_absyn_postprocessor",
    "remove_absyn_postprocessor", "add_user_state_delta",
    "add_preterm_processor", "remove_preterm_processor", "add_const",
    "add_infix", "add_rule", "add_listform", "add_numeral_form",
    "add_bare_numeral_form", "add_strliteral_form",
    "remove_strliteral_form", "give_num_priority", "remove_numeral_form",
    "associate_restriction", "prefer_form_with_tok", "set_fixity",
    "set_mapped_fixity", "set_associativity", "remove_rules_for_term",
    "remove_termtok", "overload_on", "inferior_overload_on",
    "overload_on_by_nametype", "send_to_back_overload",
    "bring_to_front_overload", "clear_overloads_on", "remove_ovl_mapping",
    "gen_remove_ovl_mapping", "add_record_field", "add_record_fupdate",
    "add_user_printer", "remove_user_printer", "set_grammars")

# Text that creates or reaches state shared by the whole process (R2):
# refs, arrays of any kind, tables, weak pointers, threads and locks, hooks,
# listeners, registrations and slot or flag writes. Names are those of the
# tree's signatures (Context.Data in src/prekernel/Context.sig, ThmSetData
# in src/1/ThmSetData.sig, AncestryData, Feedback, Theory).
ROOT_PATTERNS = (
    ("ref", r"(?<![\w'.])ref\b|\b(?:Sref|Uref|Unsynchronized\.ref)\b"),
    ("assignment", r":="),
    ("Array", r"\b(?:\w*Array(?:2|Slice)?|Dynarray)\b"),
    ("hashtable", r"\b(?:Hash[Tt]able|PolyML\.HashTable)\b"),
    ("Weak", r"\bWeak\b|\bPolyML\.Weak\b"),
    ("thread-or-lock", r"\b(?:Synchronized|Mutex|Thread|ConditionVar)\b"),
    ("Listener.add_listener", r"\bListener\.add_listener\b"),
    ("register_hook", r"\bregister_(?:hook|onload)\b"),
    ("context-data",
     r"\b(?:Context\.)?Data\.(?:new|put|write|modify|update)\b"),
    ("attribute-registration",
     r"\b(?:register_attribute|new_attribute|add_attribute"
     r"|reserve_word|define_abbreviation)\b"),
    ("thmsetdata-registration",
     r"\b(?:new_exporter|export_with_ancestry|export_simple_dictionary"
     r"|export_alist|export_list)\b"),
    ("ancestry-data", r"\bAncestryData\.(?:make|fullmake)\b"),
    ("trace-registration", r"\bregister_(?:alias_|f|b)?trace\b"),
    # the simplifier's own strong-reference caches (src/simp/src/Cache.sig,
    # src/portableML/poly/Susp.sig, src/metis/mlibUseful.sig)
    ("cache", r"\b(?:Cache\.)?R?CACHE\b"),
    ("memoize", r"\bmemoize\b"),
    ("Susp.delay", r"\bSusp\.delay\b"),
    ("grammar-write", r"\b(?:temp_)?(?:%s)\b" % "|".join(GRAMMAR_WRITES)),
)
ROOT_RES = tuple((n, re.compile(p)) for n, p in ROOT_PATTERNS)


def added_lines(before, after):
    """The lines of `after` (comments blanked) that are not in `before`
    (comments blanked), by a line diff."""
    old = strip_comments(before).splitlines()
    new = strip_comments(after).splitlines()
    out = []
    for tag, _, _, j1, j2 in difflib.SequenceMatcher(
            None, old, new, autojunk=False).get_opcodes():
        if tag in ("insert", "replace"):
            out += [x for x in new[j1:j2] if x.strip()]
    return out


def scan_roots(lines):
    """[(pattern name, line)] for the hidden-root patterns."""
    return [(name, line.strip()) for line in lines
            for name, regex in ROOT_RES if regex.search(line)]


TYPE_KINDS = frozenset(("type", "datatype", "eqtype", "exception",
                        "withtype", "abstype"))
CHUNK_KINDS = TYPE_KINDS | frozenset((
    "val", "fun", "structure", "signature", "functor", "open", "local",
    "infix", "infixr", "nonfix", "include", "sharing"))


def chunks(text):
    """The declarations of a file (comments blanked) as normalized chunks
    [(kind, text)]: a chunk starts at a line whose first word is a
    declaration keyword and runs to the next such line (`and` continues
    the chunk). Nested `val`/`type` of a `let` count as chunks too, which
    only makes the classification stricter. A bare `end` at column 0 closes
    a structure or signature body: it ends the chunk and belongs to none,
    so that adding a declaration at the end of a body does not change the
    text of the declaration before it."""
    out, current = [], None
    for line in strip_comments(text).splitlines():
        words = line.split()
        if not words:
            continue
        if line.startswith("end") and words in (["end"], ["end;"]):
            current = None
            continue
        if words[0] in CHUNK_KINDS:
            current = [words[0], []]
            out.append(current)
        if current is not None:
            current[1].append(" ".join(words))
    return [(k, " ".join(v)) for k, v in out]


def classify(before, after):
    """(kinds of the declarations added or removed, those that are type
    kinds): the multiset difference of the two files' chunks."""
    old, new = {}, {}
    for kind, text in chunks(before):
        old[(kind, text)] = old.get((kind, text), 0) + 1
    for kind, text in chunks(after):
        new[(kind, text)] = new.get((kind, text), 0) + 1
    changed = []
    for key in set(old) | set(new):
        if old.get(key, 0) != new.get(key, 0):
            changed.append(key)
    kinds = sorted({k for k, _ in changed})
    types = sorted(t for k, t in changed if k in TYPE_KINDS)
    return kinds, types


# --------------------------------------------------------- .uo closure

def hol_rel(line, root):
    """The path of a dependency line relative to the root: `$(HOLDIR)/...`
    or an absolute path inside the root; anything else is an error."""
    prefix = "$(HOLDIR)/"
    if line.startswith(prefix):
        return line[len(prefix):]
    root = Path(root).resolve()
    if Path(line).is_absolute() and Path(line).is_relative_to(root):
        return str(Path(line).relative_to(root))
    raise Refusal("dependency outside the snapshot: " + line)


def tracked_rel(root, rel):
    """A source path with the sigobj links followed (inside the root)."""
    real = Path(os.path.realpath(Path(root) / rel))
    root = Path(root).resolve()
    require(real.is_relative_to(root), "%s leaves the snapshot" % rel)
    return str(real.relative_to(root))


def read_deps(path, root):
    """(names, locals, sources): the module names a `.uo`/`.ui` lists from
    sigobj, the `directory/name` of those it lists from another directory
    (its own entry among them), and the source paths (relative to the
    root) it names."""
    names, local, sources = [], [], []
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        rel = hol_rel(line, root)
        if rel.endswith((".sml", ".sig")):
            sources.append(tracked_rel(root, rel))
        elif Path(rel).parent == Path("sigobj"):
            names.append(Path(rel).name)
        else:
            local.append(rel)
    return names, local, sources


def module_files(root, name):
    out = []
    for ext in (".uo", ".ui"):
        link = Path(root) / "sigobj" / (name + ext)
        if os.path.lexists(link):
            require(link.exists(), "dangling sigobj link " + str(link))
            real = Path(os.path.realpath(link))
            require(real.is_relative_to(Path(root).resolve()),
                    "%s leaves the snapshot: %s" % (link, real))
            out.append(link)
    return out


def local_deps(root, rel, seen, nominal=None, listed=()):
    """(sigobj names, sources) reached through a dependency listed by
    directory (`dir/name`). If sigobj links the object built in that
    directory it is the sigobj module `name`; if the directory has a
    private object of that name its own lists are followed in place, by
    directory. If the directory has no such object the line only names
    where the module was expected (the implicit Overlay dependency of every
    module, whose one real object is src/thm/.hol/objs/Overlay.uo, or a
    functor that Holdep lists both from sigobj and by directory, such as
    Table): it stands for the sigobj module of that name, and is recorded
    in `nominal` as (rel, whether the same deps file lists sigobj/name,
    `listed` being the sigobj names of that file); see nominal_problems."""
    if rel in seen:
        return [], []
    seen.add(rel)
    name = Path(rel).name
    objs = Path(root) / Path(rel).parent / ".hol" / "objs"
    files = [objs / (name + e) for e in (".uo", ".ui")
             if (objs / (name + e)).is_file()]
    if not files:
        if nominal is not None:
            nominal.append((rel, name in listed))
        return [name], []
    for f in files:
        link = Path(root) / "sigobj" / f.name
        if os.path.lexists(link) and Path(os.path.realpath(link)) == \
                f.resolve():
            return [name], []
    names, sources = [], []
    for f in files:
        n, local, s = read_deps(f, root)
        names += n
        sources += s
        for x in local:
            more = local_deps(root, x, seen, nominal, set(n))
            names += more[0]
            sources += more[1]
    return names, sources


def walk(root, starts):
    """The closure of `starts` under the `.uo` and `.ui` lists of `root`:
    (modules {name: {deps, sources}}, unresolved names)."""
    modules, unresolved, stack = {}, set(), list(starts)
    while stack:
        name = stack.pop()
        if name in modules or name in unresolved:
            continue
        files = module_files(root, name)
        if not files:
            unresolved.add(name)
            continue
        deps, sources, seen, nominal = set(), set(), set(), []
        for f in files:
            n, local, s = read_deps(f, root)
            deps.update(n)
            sources.update(s)
            for x in local:
                more = local_deps(root, x, seen, nominal, set(n))
                deps.update(more[0])
                sources.update(more[1])
        deps.discard(name)
        modules[name] = dict(
            deps=sorted(deps), sources=sorted(sources),
            nominal=sorted({r for r, _ in nominal}),
            nominal_unlisted=sorted({r for r, ok in nominal if not ok and
                                     Path(r).name != "Overlay"}))
        stack += sorted(deps)
    return modules, sorted(unresolved)


MAKE_VAR = re.compile(r"\s*([A-Za-z_]+)\s*([+:]?)=(.*)")
# Per heap: the directory of its Holmakefile, the variables whose words are
# the modules it is built from, and the names the buildheap command adds
# literally (`$(protect $(SIGOBJ)/X)` words count as X): `recipe` takes
# them from the buildheap recipe line of the Holmakefile (recipe_names),
# `extra` lists them.
HEAP_SPECS = {
    "hol.state": dict(dir="src/boss", vars=("boss_deps",), recipe=True),
    "numheap": dict(dir="src/num/termination",
                    vars=("ARITH_DEPS", "BARE_DEPS"), extra=()),
    "realheap": dict(dir="src/real/analysis", vars=("REAL_DEPS",),
                     extra=()),
    # bin/hol.state0: `buildheap $(UOARGS)` of src/proofman/Holmakefile
    # (the words `$(protect $(SIGOBJ)/X)` are the sigobj object X).
    "hol.state0": dict(dir="src/proofman", vars=("UOARGS",), extra=()),
}
# Reviewed: names that are compiled into bin/hol or the Poly/ML basis and
# have no sigobj object, so that a closure walk may leave them unresolved.
# None is needed for the pinned snapshots (every name above resolves);
# a name that is not here and does not resolve fails L2.resolved.
BASIS_ONLY = ()
ROOT_MODULES = ("simpLib", "congLib", "bossLib")
PROTECTED = re.compile(r"\$\(protect \$\(SIGOBJ\)/([\w']+)\)")


# Variables of a buildheap recipe line that are not module lists.
RECIPE_IGNORED = ("$(DEBUG_FLAG)",)
RECIPE_OPTIONS = ("-o", "-b")


def recipe_names(text, variables, heap):
    """The module names that the buildheap recipe line of a Holmakefile
    adds to the `variables` it expands: the one recipe line (it starts
    with a tab) that runs `buildheap`, read as `buildheap`, options
    (`-o X`, `-b X`, DEBUG_FLAG), then names, `$(var)` of a module-list
    variable, and `$(protect $(SIGOBJ)/X)` words. A line of another
    structure is an error, so that a new form of the command cannot add a
    root unseen."""
    lines = [l for l in text.replace("\\\n", " ").splitlines()
             if l.startswith("\t") and re.search(r"\bbuildheap\b", l)]
    require(len(lines) == 1, "%s: %d buildheap recipe lines, not 1" % (
        heap, len(lines)))
    words = PROTECTED.sub(r"\1", lines[0].split("#")[0]).split()
    require("buildheap" in words, "%s: no `buildheap` word in the recipe "
            "line" % heap)
    names, used, skip = [], set(), False
    for w in words[words.index("buildheap") + 1:]:
        if skip:
            skip = False
        elif w in RECIPE_OPTIONS:
            skip = True
        elif w in RECIPE_IGNORED:
            pass
        elif w.startswith("$(") and w.endswith(")") and \
                w[2:-1] in variables:
            used.add(w[2:-1])
        elif re.fullmatch(r"[\w']+", w):
            names.append(w)
        else:
            raise Refusal("%s: unexpected word %r in the buildheap recipe "
                          "line" % (heap, w))
    require(not skip, "%s: the buildheap options end in %r" % (heap, w))
    require(used == set(variables), "%s: the buildheap line does not "
            "expand %s" % (heap, sorted(set(variables) - used)))
    return names


def heap_deps(root, specs=HEAP_SPECS):
    """{heap: sorted module names} from the Holmakefiles of the tree: the
    words of the named variables (words with `$` are expressions, not
    names), plus the literal names. A missing variable is an error."""
    out = {}
    for heap, spec in specs.items():
        text = (Path(root) / spec["dir"] / "Holmakefile").read_text()
        values = {}
        for line in text.replace("\\\n", " ").splitlines():
            found = MAKE_VAR.match(line)
            if found and found.group(1) in spec["vars"]:
                if found.group(2) != "+":
                    values[found.group(1)] = set()
                words = PROTECTED.sub(r"\1", found.group(3).split("#")[0])
                values.setdefault(found.group(1), set()).update(
                    Path(w).name for w in words.split() if "$" not in w)
        missing = [v for v in spec["vars"] if not values.get(v)]
        require(not missing, "%s: no value for %s" % (heap, missing))
        extra = recipe_names(text, spec["vars"], heap) \
            if spec.get("recipe") else spec.get("extra", ())
        names = set().union(*values.values()) | set(extra)
        out[heap] = sorted(n[:-3] if n.endswith(".uo") else n
                           for n in names)
    return out


# Closure sources that a build generates, and the tracked files they are
# made from. All the listed files are tracked and compared (the files of
# both kernel flavours, of both the poly and the generic configuration, of
# both word sizes): each is one input of the generated file.
GENERATED = {
    "src/thm/Thm.sml": ("src/thm/std-thm.ML", "src/thm/otknl-thm.ML"),
    "src/thm/Thm-sig.sml": ("src/thm/std-thmsig.ML",
                            "src/thm/otknl-thmsig.ML"),
    "sigobj/Systeml.sml": ("tools-poly/Holmake/unix-systeml.sml",
                           "tools/Holmake/unix-systeml.sml"),
    "sigobj/Systeml.sig": ("tools/Holmake/Systeml.sig",),
    "src/portableML/poly/SHA1_ML.sml": (
        "src/portableML/poly/w64-SHA1.ML",
        "src/portableML/poly/SHA1-byexec.ML"),
}
# Generated files that are plain copies of one of their inputs.
COPIES = ("sigobj/Systeml.sig", "src/portableML/poly/SHA1_ML.sml")


def source_candidates(rel):
    """The tracked files a closure source line can stand for, any one of
    which tracks it: the line itself, what a lexer or grammar product is
    made from, the script of a theory. A GENERATED line is tracked by all
    of its inputs: see source_inputs."""
    base = Path(rel)
    stem = base.name.rsplit(".", 1)[0]
    out = [rel]
    if rel.endswith("-sig.sml"):
        out.append(rel[:-8])
    if rel.endswith(".sml"):
        out.append(rel[:-4])
    if stem.endswith("Theory"):
        out.append(str(base.with_name(stem[:-6] + "Script.sml")))
    return out


def source_inputs(rel):
    """(mode, files) of a source line: `all` of the files of a GENERATED
    line, else `any` of its candidates."""
    if rel in GENERATED:
        return "all", list(GENERATED[rel])
    return "any", source_candidates(rel)


def source_files(rel):
    return source_inputs(rel)[1]


def closure_sources(modules):
    return sorted({c for m in modules.values() for s in m["sources"]
                   for c in source_files(s)})


def untracked_sources(modules, ids):
    """[(module, source)] of the closure's source lines that are tracked
    in no way: not themselves, not by the file they are made from."""
    out = []
    for name, m in sorted(modules.items()):
        for src in m["sources"]:
            mode, files = source_inputs(src)
            found = [bool(ids.get(f)) for f in files]
            if not (all(found) if mode == "all" else any(found)):
                out.append((name, src))
    return out


def side_closure(root, specs=HEAP_SPECS):
    heaps = heap_deps(root, specs)
    starts = set(ROOT_MODULES)
    for names in heaps.values():
        starts.update(names)
    modules, unresolved = walk(root, sorted(starts))
    return dict(heaps=heaps, roots=sorted(starts), modules=modules,
                unresolved=[n for n in unresolved if n not in BASIS_ONLY],
                basis_only=[n for n in unresolved if n in BASIS_ONLY])


# ------------------------------------------------ generated products

def mask_root(data, root):
    """The bytes with the snapshot's root (as written or resolved) named
    $HOLDIR: what a product that records its root compares as."""
    for text in sorted({str(root), str(Path(root).resolve())},
                       key=len, reverse=True):
        data = data.replace(text.encode(), b"$HOLDIR")
    return data


def product_path(root, rel):
    """Where a generated source line lives: at its path when the build
    leaves it there, else in the `.hol/objs` of its directory."""
    flat = Path(root) / rel
    if flat.is_file():
        return flat
    return Path(root) / Path(rel).parent / ".hol" / "objs" / \
        Path(rel).name


def generated_products(modules, ids):
    """The files a build generated for the closure, as paths relative to a
    root: every source line tracked by no file of its own but made from
    tracked ones (a line tracked in no way is L2.sources-tracked's), and
    the `.dat` of every theory."""
    unmapped = {src for i in ids.values()
                for _, src in untracked_sources(modules, i)}
    rels = set()
    for m in modules.values():
        for src in m["sources"]:
            if src in unmapped:
                continue
            if not any(i.get(src) for i in ids.values()):
                rels.add(src)
            if src.endswith("Theory.sml") and \
                    Path(src).name != "Theory.sml":
                rels.add(src[:-4] + ".dat")
    return sorted(rels)


def compare_products(roots, rels):
    """[(rel, reason)] of the products that are missing on a side or whose
    bytes differ (the root masked) between the sides."""
    bad, masked = [], []
    for rel in rels:
        found = {}
        for side, root in roots.items():
            f = product_path(root, rel)
            found[side] = f.read_bytes() if f.is_file() else None
        if None in found.values():
            bad.append((rel, "missing on " + ", ".join(
                s for s, v in found.items() if v is None)))
            continue
        one, two = (mask_root(found[s], roots[s]) for s in roots)
        if one != two:
            bad.append((rel, "differs"))
        elif any(mask_root(found[s], roots[s]) != found[s] for s in roots):
            masked.append(rel)
    return bad, masked


def check_copies(repo, pins, roots, rels, checks):
    """A generated copy is a copy of one of its tracked inputs."""
    bad = []
    for rel in COPIES:
        if rel not in rels:
            continue
        for side, root in roots.items():
            f = product_path(root, rel)
            inputs = set()
            for path in GENERATED[rel]:
                try:
                    inputs.add(git_bytes(repo, "cat-file", "blob", "%s:%s"
                                         % (pins[side], path)))
                except Refusal:
                    pass
            if not f.is_file() or f.read_bytes() not in inputs:
                bad.append("%s:%s" % (side, rel))
    checks.ok("L2.generated-copies", "L2", not bad,
              "not a copy of a tracked input: " + ", ".join(bad),
              "generated copies equal a tracked input")


# ---------------------------------------------------------- the audit

# Holmakefile text that decides what a heap or a build contains: the
# assignments of INCLUDES, HOLHEAP, OPTIONS, UOARGS and the *DEPS lists
# (also their uses) and the buildheap command. An allowlisted Holmakefile
# may change anything else (targets, cleanups, tests).
BUILD_HAZARD = re.compile(
    r"^\s*(?:INCLUDES|HOLHEAP|OPTIONS|UOARGS|\w*DEPS)\s*[+:?]?=|"
    r"\$\((?:INCLUDES|HOLHEAP|OPTIONS|UOARGS|\w*DEPS)\)|"
    r"\bbuildheap\b", re.I)


def hazard_lines(text):
    """The logical lines (continuations joined, comments removed) of a
    Holmakefile that BUILD_HAZARD matches, as a multiset."""
    out = {}
    for line in text.replace("\\\n", " ").splitlines():
        line = line.split("#")[0].rstrip()
        if BUILD_HAZARD.search(line):
            key = " ".join(line.split())
            out[key] = out.get(key, 0) + 1
    return out


def hazard_changes(before, after):
    """The hazard lines that B..C adds or removes."""
    old, new = hazard_lines(before), hazard_lines(after)
    return sorted(k for k in set(old) | set(new)
                  if old.get(k, 0) != new.get(k, 0))

def modified_paths(repo, base, cand):
    """{path: status} of the tracked files B..C changed, other than the
    added ones, outside the tests directories (TASK32's COMPILED_REF rule,
    d.snap.TEST_ONLY)."""
    out = git_bytes(repo, "diff", "--name-status", "--no-renames", "-z",
                    base, cand, "--", ".", *d.snap.TEST_ONLY)
    parts = out.decode("utf-8", errors="replace").split("\0")
    found = {}
    for status, path in zip(parts[0::2], parts[1::2]):
        if status != "A":
            found[path] = status
    return found


def audit(repo, base_root, cand_root, declared, checks,
          specs=HEAP_SPECS):
    pins = dict(base=declared["base"], cand=declared["cand"])
    roots = dict(base=Path(base_root), cand=Path(cand_root))
    data = dict(pins=pins)
    side = {}
    for name, root in roots.items():
        side[name] = side_closure(root, specs)
        checks.ok("L2.resolved." + name, "L2", not side[name]["unresolved"],
                  "no .uo/.ui for: %s" % ", ".join(
                      side[name]["unresolved"]),
                  "every closure module has a .uo or .ui")
    data["closure"] = {n: dict(
        roots=s["roots"], heaps=s["heaps"], unresolved=s["unresolved"],
        basis_only=s["basis_only"], modules=sorted(s["modules"]),
        nominal={m: v["nominal"] for m, v in sorted(s["modules"].items())
                 if v["nominal"]}) for n, s in side.items()}
    for name, s in side.items():
        found = sorted(m for m in s["modules"] if loading.extension_name(m))
        checks.ok("L2.no-extension." + name, "L2", not found,
                  "extension module(s) in the closure: " + ", ".join(found),
                  "no extension module in the closure")
    nominal = {n: {m: v["nominal"] for m, v in s["modules"].items()}
               for n, s in side.items()}
    differ = sorted(m for m in set(nominal["base"]) | set(nominal["cand"])
                    if nominal["base"].get(m, []) !=
                    nominal["cand"].get(m, []))
    unlisted = sorted("%s:%s: %s" % (n, m, ", ".join(v["nominal_unlisted"]))
                      for n, s in side.items()
                      for m, v in s["modules"].items()
                      if v["nominal_unlisted"])
    checks.ok("L2.nominal", "L2", not (differ or unlisted),
              "nominal dependencies differ between the sides in: %s; "
              "unlisted ones (not Overlay, not also sigobj/<name> in the "
              "same deps file): %s" % (differ[:5], unlisted[:5]),
              "the nominal dependencies of every module are equal on both "
              "sides, each Overlay or also listed from sigobj")
    mods = {n: sorted(s["modules"]) for n, s in side.items()}
    only = {n: sorted(set(mods[n]) - set(mods[o]))
            for n, o in (("base", "cand"), ("cand", "base"))}
    checks.ok("L2.names-equal", "L2", mods["base"] == mods["cand"],
              "closure names differ: only in base %s; only in cand %s" % (
                  only["base"], only["cand"]),
              "closure names are equal (%d modules)" % len(mods["base"]))
    data["names_only"] = only
    # source blobs of the closure
    paths = sorted(set(closure_sources(side["base"]["modules"])) |
                   set(closure_sources(side["cand"]["modules"])))
    ids = {n: blob_ids(repo, pins[n], paths) for n in pins}
    tracked = [p for p in paths if ids["base"][p] or ids["cand"][p]]
    differing = [p for p in tracked if ids["base"][p] != ids["cand"][p]]
    data["sources"] = dict(candidates=len(paths), tracked=len(tracked))
    data["differing"] = differing
    # the snapshots hold what git says
    mismatch, absent = [], []
    for n, root in roots.items():
        for p in tracked:
            if not ids[n][p]:
                continue
            f = root / p
            if not f.is_file():
                absent.append("%s:%s" % (n, p))
            elif hash_blob(f.read_bytes()) != ids[n][p]:
                mismatch.append("%s:%s" % (n, p))
    checks.ok("L2.snapshot-is-git", "L2", not (mismatch or absent),
              "snapshot file(s) differ from their pin: %s; tracked "
              "closure file(s) missing on disk: %s" % (
                  ", ".join(mismatch[:5]), ", ".join(absent[:5])),
              "closure files equal their pinned git blobs")
    # every source line of every module is tracked or made from tracked
    # files
    lacking = sorted({"%s: %s" % (m, src) for n, s in side.items()
                      for m, src in untracked_sources(s["modules"],
                                                      ids[n])})
    data["no_tracked_source"] = lacking
    checks.ok("L2.sources-tracked", "L2", not lacking,
              "source line(s) tracked in no way: " + "; ".join(lacking[:8]),
              "every source line of every closure module is tracked or "
              "made from tracked files")
    # the generated products of the closure agree between the snapshots
    rels = sorted(set(generated_products(side["base"]["modules"],
                                         ids)) |
                  set(generated_products(side["cand"]["modules"], ids)))
    bad, masked = compare_products(roots, rels)
    data["generated"] = dict(products=len(rels), root_masked=masked,
                             differing=[list(x) for x in bad])
    checks.ok("L2.generated-products", "L2", not bad,
              "generated product(s) differ: " + "; ".join(
                  "%s (%s)" % x for x in bad[:6]),
              "%d generated products are byte-identical (%d after "
              "masking the root)" % (len(rels), len(masked)))
    check_copies(repo, pins, roots, rels, checks)
    # declared set
    want = sorted(e["path"] for e in declared["l2"])
    checks.ok("L2.diff-is-declared", "L2", differing == want,
              "differing closure files %s are not the declared set %s "
              "(undeclared: %s; declared but equal or outside: %s)" % (
                  differing, want, sorted(set(differing) - set(want)),
                  sorted(set(want) - set(differing))),
              "differing closure files = declared set (%d)" % len(want))
    stale = []
    for e in declared["l2"]:
        if ids["base"].get(e["path"]) != e["base_blob"] or \
                ids["cand"].get(e["path"]) != e["cand_blob"]:
            stale.append(e["path"])
    checks.ok("L2.declared-blobs", "L2", not stale,
              "declared blob ids differ from git: " + ", ".join(stale),
              "declared blobs are the pinned git blobs")
    # every modified tracked file B..C is declared or a reviewed build or
    # documentation file
    modified = modified_paths(repo, pins["base"], pins["cand"])
    allow = {e["path"]: e for e in declared["allowlist"]}
    data["modified"] = dict(files=sorted(modified),
                            allowlisted=sorted(set(modified) & set(allow)))
    unexplained = sorted(set(modified) - set(want) - set(allow))
    unused = sorted(set(allow) - set(modified))
    ablobs = {n: blob_ids(repo, pins[n], list(allow)) for n in pins}
    wrong = sorted(p for p, e in allow.items()
                   if ablobs["base"][p] != e["base_blob"] or
                   ablobs["cand"][p] != e["cand_blob"])
    checks.ok("L2.modified-explained", "L2",
              not (unexplained or unused or wrong or
                   set(want) - set(modified)),
              "modified tracked file(s) neither declared nor allowlisted: "
              "%s; allowlisted but not modified: %s; allowlist blobs "
              "stale: %s; declared but not modified: %s" % (
                  unexplained, unused, wrong,
                  sorted(set(want) - set(modified))),
              "every modified tracked file B..C (%d) is declared or "
              "allowlisted (%d)" % (len(modified), len(allow)))
    # an allowlisted Holmakefile does not change what a heap contains
    hazards = []
    for p in sorted(allow):
        if Path(p).name != "Holmakefile":
            continue
        before = blob_text(repo, pins["base"], p) if ablobs["base"][p] \
            else ""
        after = blob_text(repo, pins["cand"], p) if ablobs["cand"][p] \
            else ""
        hazards += ["%s: %s" % (p, x) for x in hazard_changes(before,
                                                              after)]
    data["allowlist_hazards"] = hazards
    checks.ok("L2.allowlist-build-safe", "L2", not hazards,
              "an allowlisted Holmakefile changes INCLUDES, HOLHEAP, "
              "OPTIONS, *DEPS, UOARGS or a buildheap line: " +
              "; ".join(hazards[:4]),
              "allowlisted Holmakefile diffs touch no heap, include or "
              "option line")
    # R2 and R3 on every differing file
    r2, r3 = {}, {}
    for p in differing:
        before = blob_text(repo, pins["base"], p) if ids["base"][p] else ""
        after = blob_text(repo, pins["cand"], p) if ids["cand"][p] else ""
        r2[p] = scan_roots(added_lines(before, after))
        kinds, types = classify(before, after)
        r3[p] = dict(kinds=kinds, type_changes=types)
    data["r2"] = {p: [list(h) for h in hits] for p, hits in r2.items()}
    data["r3"] = r3
    hits = ["%s: %s `%s`" % (p, n, line) for p, hs in r2.items()
            for n, line in hs]
    checks.ok("R2.no-new-root", "R2", not hits,
              "added hidden-root text: " + "; ".join(hits[:5]),
              "no added ref/assignment/array/hash table/Weak/thread/"
              "listener/hook/registration/slot write in the differing "
              "files")
    types = ["%s: %s" % (p, t) for p, r in r3.items()
             for t in r["type_changes"]]
    checks.ok("R3.no-type-change", "R3", not types,
              "type/datatype/exception declaration changed: " +
              "; ".join(types[:5]),
              "no type, datatype, exception or record declaration changed")
    allowed = {e["path"]: set(e["allowed_kinds"]) for e in declared["l2"]}
    extra = ["%s: %s" % (p, sorted(set(r["kinds"]) - allowed.get(p, set())))
             for p, r in r3.items()
             if set(r["kinds"]) - allowed.get(p, set())]
    checks.ok("R3.kinds-declared", "R3", not extra,
              "changed declaration kinds not declared: " + "; ".join(extra),
              "changed declarations are only of the declared kinds")
    return data


# ------------------------------------------------------------- harvest

# Failure text, matched on the log without ANSI escapes and backspaces
# (testutils prints `ESC[2CFAILED!` after a failed test and ends a failing
# process with `Failure count = N`; PolyML prints uncaught exceptions as
# `Exception- ... raised`).
LOG_FAIL = tuple(re.compile(p, re.M) for p in (
    r"Traceback \(most recent call last\)",
    r"FAILED!", r"^Failure count = [1-9]",
    r"^\s*FAILED\b", r"\bFAILED \(", r"\.\.\.\s*FAIL(?:ED)?\s*$",
    r": FAIL\b", r"^OBS (?:assertion\.)?result=(?!pass\b)\S*",
    r"^OBS repair=(?!pass\b)\S*",
    r"^Exception- ", r"^Static Errors", r"[Uu]ncaught exception",
    r"^Holmake: .*[Ff]ail"))
ANSI = re.compile(r"\x1b(?:\[[0-9;?]*[ -/]*[@-~]|.)")
OK_LINE = re.compile(r"\.\.\.\s*(?:\(\S+s\)\s*)?OK\s*$", re.M)
RAN = re.compile(r"^Ran (\d+) tests? in", re.M)
# The last line of a unittest run: `OK`, or `OK (skipped=N)` when tests
# were skipped (the only extra a passing run prints that we accept: an
# `expected failures` or `unexpected successes` suffix is not accepted).
UNITTEST_OK = re.compile(r"^OK(?: \(skipped=(\d+)\))?\s*$", re.M)
# The count that pins each kind of suite without a completion marker, and
# the declaration key that holds the reviewed value (task33_declared.json:
# log_counts, and log_skips for skipped unittest tests).
COUNT_KEY = dict(tprint="ok_lines", obs="ok_lines", unittest="ran_blocks",
                 manifest="manifest_lines")
MANIFEST_LINE = re.compile(r"manifest\.json\s*$", re.M)
OBS_PASS = re.compile(r"^OBS (?:assertion\.)?result=pass\s*$", re.M)
AUDIT_PASS = re.compile(r"^\S+/\S+/(?:before|after): PASS$", re.M)


def clean_log(text):
    """The log as a reader sees it: no ANSI escapes, no backspaces."""
    return ANSI.sub("", text).replace("\x08", "")


def marker(regex):
    return dict(marker=regex)


# name -> (kind, options); the name is the log file's name without `.log`.
# kinds: tprint (OK lines), obs (OK lines and `OBS result=pass`),
# unittest (every `Ran N tests` followed by OK), manifest (a script that
# ends by naming its manifest), audit (api-audit receipts), theory (a
# built theory), heap (a saved heap), empty (a link step, no suite).
LOG_RULES = {
    "api-audit": ("audit", {}),
    "cond-rewr-ext": ("tprint", marker(r"Cond_rewrExt focused checks: "
                                       r"([1-9]\d*)")),
    "congruence-ext": ("tprint", marker(r"Congruence extension focused "
                                        r"checks: ([1-9]\d*)")),
    "simp-ext": ("tprint", marker(r"TraverseExt lifetime checks: "
                                  r"([1-9]\d*)")),
    "traverse-ext": ("tprint", marker(r"TraverseExt focused checks: "
                                      r"([1-9]\d*)")),
    "standard-recipes": ("tprint", marker(r"STANDARD_RECIPE_CHECKS="
                                          r"([1-9]\d*)")),
    "tracked-defaults": ("tprint", marker(r"TRACKED_DEFAULTS_COMPLETE "
                                          r"checks=([1-9]\d*)")),
    "native-extension": ("tprint", {}),
    "check-full": ("tprint", marker(r"Native coverage: ([1-9]\d*) "
                                    r"original")),
    "split-registration": ("tprint", {}),
    "replay-order": ("tprint", {}),
    "simp-marker-tests": ("tprint", {}),
    "simp-selftest": ("tprint", {}),
    "boss-selftest": ("tprint", {}),
    "traversal-contracts": ("tprint", {}),
    "fresh-load-regressions": ("obs", {}),
    "split-lifecycle": ("obs", {}),
    "split-persistence": ("obs", {}),
    "exclusion-contracts": ("obs", {}),
    "legacy-contracts": ("unittest", marker(r"OriginalScope: ([1-9]\d*) "
                                            r"checks")),
    "literal-exclusions": ("unittest", {}),
    "ordinary-tactics": ("unittest", {}),
    # These three logs are not in LOGS_REQUIRED and have no `log_counts`
    # entry (count_problems rejects unknown entries, and the sealed
    # task33_declared.json must not change), so they are judged by the
    # marker: a positive `Ran N tests` line plus the unittest OK footer.
    # (With a declaration, judge_log demands a reviewed count for count kinds
    # that have no marker, so these rules need one.)
    "fragments-python-tests": ("unittest", marker(
        r"Ran ([1-9]\d*) tests? in")),
    "compiled-core-python-tests": ("unittest", marker(
        r"Ran ([1-9]\d*) tests? in")),
    "interfaces-design-check": ("unittest", marker(
        r"Ran ([1-9]\d*) tests? in")),
    "compiled-core": ("manifest", {}),
    "fragment-contracts": ("manifest", {}),
    "boolSimpsContextTheory": ("theory", dict(theory="boolSimpsContext")),
    "simpMarkerTheory": ("theory", dict(theory="simpMarker")),
    "fresh-load-selftest.exe": ("empty", {}),
}
# Rules of logs whose name alone does not tell them apart (the five
# tracked-recipes suites of the library directories print their own
# completion line) or that have the name of other logs: by path.
PATH_RULES = {
    "src/integer/.hol/logs/tracked-recipes": (
        "tprint", marker(r"INTEGER_RECIPE_CHECKS=([1-9]\d*)")),
    "src/real/.hol/logs/tracked-recipes": (
        "tprint", marker(r"REAL_RECIPE_CHECKS=([1-9]\d*)")),
    "src/list/src/.hol/logs/tracked-recipes": (
        "tprint", marker(r"LIST_TRACKED_RECIPE_CHECKS=([1-9]\d*)")),
    "src/num/arith/src/.hol/logs/tracked-recipes": (
        "tprint", marker(r"NUMERAL_RECIPE_CHECKS=([1-9]\d*)")),
    "src/pred_set/src/.hol/logs/tracked-recipes": (
        "tprint", marker(r"PRED_SET_TRACKED_RECIPE_CHECKS=([1-9]\d*)")),
    "src/1/.hol/logs/selftest.log": ("tprint", {}),
}
# Logs that must exist: the suites of the extension and the ordinary
# modules that the candidate's `-t` build runs (by name, or by path where
# a name is not unique).
LOGS_REQUIRED = (
    "api-audit", "cond-rewr-ext", "congruence-ext", "simp-ext",
    "traverse-ext", "split-lifecycle", "split-persistence",
    "split-registration", "native-extension", "fresh-load-regressions",
    "standard-recipes", "replay-order", "exclusion-contracts",
    "legacy-contracts", "simp-marker-tests", "tracked-defaults",
    "boss-selftest", "check-full", "traversal-contracts",
    "literal-exclusions", "ordinary-tactics", "compiled-core",
    "fragment-contracts", "simp-selftest") + tuple(sorted(PATH_RULES))
# (directory, glob) of the logs taken from the candidate snapshot: what
# Holmake recorded of each target's output (stdout and stderr; the
# `<name>.log` copies in the source directories lack the stderr of the
# Python suites, so they are not taken). The native-extension suite also
# prints its coverage line in its own directory.
LOG_SOURCES = (
    ("src/simp/src/.hol/logs", "*"),
    ("src/boss/.hol/logs", "tracked-defaults"),
    ("src/boss/.hol/logs", "boss-selftest.log"),
    ("src/simp/tests/native-extension/.hol/logs", "*"),
    ("src/1/.hol/logs", "selftest.log")) + tuple(
        (str(Path(k).parent), "tracked-recipes") for k in PATH_RULES
        if k.endswith("tracked-recipes"))


def rule_for(path):
    """(name, rule): the rule of the log at `path`, by its path first."""
    name = Path(path).name
    stem = name[:-4] if name.endswith(".log") else name
    for key, rule in PATH_RULES.items():
        if str(path).endswith(key):
            return stem, rule
    return stem, LOG_RULES.get(stem) or LOG_RULES.get(name)


def log_names(path):
    """The names a log answers for in LOGS_REQUIRED: its name and path."""
    return {rule_for(path)[0]} | {k for k in PATH_RULES
                                  if str(path).endswith(k)}


def finished(text):
    """The last test line of the log (a line with `...`) ends in OK: a log
    cut off in the middle of a test is not finished."""
    tests = [l for l in text.splitlines() if re.search(r"\.\.\.(\s|$)", l)]
    return bool(tests) and bool(OK_LINE.search(tests[-1]))


def count_key(path):
    """The name under which the reviewed counts of a log are declared: the
    path key of a PATH_RULES log, else its name."""
    for key in PATH_RULES:
        if str(path).endswith(key):
            return key
    return rule_for(path)[0]


def needs_count(name):
    """Whether the required log `name` is of a suite with no completion
    marker, whose size is then pinned as reviewed data."""
    rule = PATH_RULES.get(name) or LOG_RULES.get(name)
    return bool(rule) and rule[0] in COUNT_KEY and "marker" not in rule[1]


def judge_log(path, text, declared=None):
    """(passed, reasons, counts) of one log, by the rule of its path or
    name, read without ANSI escapes and backspaces. `declared` is the
    declaration (task33_declared.json): given it, a marker-less suite
    must have exactly the reviewed count (`log_counts`) and no skipped
    unittest tests beyond `log_skips`."""
    stem, rule = rule_for(path)
    if rule is None:
        return False, ["no pass criterion defined for " + stem], {}
    kind, options = rule
    text = clean_log(text)
    reasons, counts = [], {}
    for regex in LOG_FAIL:
        found = regex.search(text)
        if found:
            reasons.append("failure text: " + found.group(0).strip()[:60])
    if kind == "empty":
        if text.strip():
            reasons.append("expected an empty link log")
        return not reasons, reasons, counts
    if not text.strip():
        return False, reasons + ["empty log"], counts
    oks = len(OK_LINE.findall(text))
    counts["ok_lines"] = oks
    if kind in ("tprint", "obs"):
        if not oks:
            reasons.append("no OK line")
        elif not finished(text):
            reasons.append("the last test has no OK (truncated log)")
    if kind == "obs":
        counts["result_pass"] = len(OBS_PASS.findall(text))
        if not counts["result_pass"]:
            reasons.append("no `OBS result=pass`")
    if kind == "unittest":
        ran = RAN.findall(text)
        oks = UNITTEST_OK.findall(text)
        counts.update(ran_blocks=len(ran), ok_blocks=len(oks),
                      tests=sum(int(x) for x in ran),
                      skipped=sum(int(x or 0) for x in oks))
        if not ran or len(oks) != len(ran):
            reasons.append("%d `Ran` blocks, %d OK" % (len(ran), len(oks)))
        allowed = (declared or {}).get("log_skips", {}).get(
            count_key(path), 0)
        if counts["skipped"] != allowed:
            reasons.append("%d skipped test(s), %d declared" % (
                counts["skipped"], allowed))
    if kind == "audit":
        passes = len(AUDIT_PASS.findall(text))
        counts["pass_lines"] = passes
        if passes != 8:
            reasons.append("%d api-audit PASS lines, not 8" % passes)
        if not re.search(r"^Receipt: ", text, re.M):
            reasons.append("no receipt line")
    if kind == "manifest":
        counts["manifest_lines"] = len(MANIFEST_LINE.findall(
            text.rstrip() + "\n"))
        if not counts["manifest_lines"]:
            reasons.append("no manifest path")
    if kind == "theory":
        t = options["theory"]
        if 'Exporting theory "%s" ... done.' % t not in text or \
                'Theory "%s" took' % t not in text:
            reasons.append("theory %s was not built" % t)
    if "marker" in options:
        found = re.search(options["marker"], text)
        if not found:
            reasons.append("no completion line /%s/" % options["marker"])
        else:
            counts["marker"] = found.group(0)
    if declared is not None and kind in COUNT_KEY and \
            "marker" not in options:
        key, want = COUNT_KEY[kind], \
            declared.get("log_counts", {}).get(count_key(path))
        if want is None:
            reasons.append("no reviewed %s declared" % key)
        elif counts.get(key) != want:
            reasons.append("%s is %s, reviewed %s" % (
                key, counts.get(key), want))
    return not reasons, reasons, counts


def flat_name(rel):
    return rel.replace("/", "__") + ".gz"


def log_files(root):
    seen, out = set(), []
    for directory, pattern in LOG_SOURCES:
        folder = Path(root) / directory
        if not folder.is_dir():
            continue
        for f in sorted(folder.glob(pattern)):
            rel = str(f.relative_to(root))
            if f.is_file() and not f.is_symlink() and rel not in seen:
                seen.add(rel)
                out.append(rel)
    return out


def harvest(root, out_dir, checks, declared):
    out_dir = Path(out_dir)
    require(not out_dir.exists() or not any(out_dir.iterdir()),
            "the harvest directory is not empty: %s" % out_dir)
    (out_dir / "logs").mkdir(parents=True, exist_ok=True)
    files, sums = [], []
    rels = log_files(root)
    require(rels, "no log under %s" % root)
    for rel in rels:
        raw = (Path(root) / rel).read_bytes()
        text = raw.decode("utf-8", errors="replace")
        passed, reasons, counts = judge_log(rel, text, declared)
        gz = out_dir / "logs" / flat_name(rel)
        gz.write_bytes(gzip.compress(raw, mtime=0))
        seal = a.seal(gz)
        sums.append("%s  logs/%s\n" % (seal["sha256"], gz.name))
        files.append(dict(path=rel, rule=rule_for(rel)[0], sha256=sha256(raw),
                          bytes=len(raw), gz="logs/" + gz.name,
                          gz_seal=seal, passed=passed, reasons=reasons,
                          counts=counts))
        checks.ok("E1.log." + rel, "E1", passed,
                  "; ".join(reasons), "suite passed")
    (out_dir / "SHA256SUMS").write_text("".join(sums))
    have = set().union(*(log_names(f["path"]) for f in files))
    missing = [n for n in LOGS_REQUIRED if n not in have]
    checks.ok("E1.required-logs", "E1", not missing,
              "missing log(s): " + ", ".join(missing),
              "every required suite log is present")
    return dict(root=str(root), files=files, required=list(LOGS_REQUIRED))


# ------------------------------------------------------------- archive

def median(values):
    return statistics.median(values) if values else None


def summarize(values):
    return dict(n=len(values), median=median(values),
                min=min(values) if values else None,
                max=max(values) if values else None)


def field_of(receipt, field):
    if field == "maxrss":
        return float(receipt["usage"]["maxrss"])
    return receipt["stats"][field]


def group_of(receipt):
    """base / cand: the candidate phase, which pairs the sides; control:
    the B/B phase (both labels on the base)."""
    if receipt["phase"] == "control":
        return "control"
    return "base" if receipt["side"] == "base" else "cand"


def pair_means(receipts, unit, field):
    """pair -> {baseline, candidate} sample means of the candidate phase
    (the mean of the fresh processes of a label, as d.sample does)."""
    rows = [r for r in receipts if r["workload"] == unit and
            r["phase"] == "candidate"]
    pairs = sorted({r["pair"] for r in rows})
    out = []
    for i in pairs:
        row = {}
        for sel in ("baseline", "candidate"):
            vs = [field_of(r, field) for r in rows
                  if r["pair"] == i and r["selection"] == sel]
            row[sel] = math.fsum(vs) / len(vs) if vs else None
        row["pair"] = i
        out.append(row)
    return out


def ratio_of(row):
    """candidate/baseline of a pair, None when it has no usable ratio."""
    if row["baseline"] and row["candidate"] is not None:
        return row["candidate"] / row["baseline"]
    return None


def ratios(pairs):
    return [r for r in map(ratio_of, pairs) if r is not None]


def masked_sets(report, receipts, unit):
    """Per side the distinct L1 views of the unit's processes, by the one
    rule of the driver (`task32_downstream.masked_view`: the heap's
    `loaded_before` names, the modules loaded, the files the process added
    to fileDirMap with the root and the probe directory masked), keyed by
    the sha256 of the view."""
    out = {"base": {}, "cand": {}}
    for r in receipts:
        if r["workload"] != unit:
            continue
        side = r["side"]
        view = d.masked_view(r, report["roots"][side],
                             report["reporter"][side]["dir"])
        key = sha256(json.dumps(view, sort_keys=True).encode())
        out[side].setdefault(key, dict(count=0, view=view))["count"] += 1
    return out


def view_difference(base, cand):
    """Why two views differ, for the report."""
    parts = []
    for k in ("loaded_before", "loaded", "files"):
        only = lambda x, y: [i for i in x[k] if i not in y[k]][:3]
        parts.append("%s: only in cand %s, only in base %s" % (
            k, only(cand, base), only(base, cand)))
    return "; ".join(parts)


def check_loaded_sets(report, receipts, checks):
    """L1 on the archive, the rule of `task32_downstream.check_cross_side`:
    per unit every process of a side has one and the same view (a baseline
    that differs from itself is a harness fault, a candidate that does is a
    finding) and the two sides' views are equal."""
    data = {}
    for unit in report["workloads"]:
        sets = masked_sets(report, receipts, unit)
        base, cand = sets["base"], sets["cand"]
        one = lambda s: next(iter(s.values()))["view"] if s else None
        consistent = len(base) == 1 and len(cand) == 1
        equal = consistent and set(base) == set(cand)
        view = one(base) or dict(loaded_before=[], loaded=[], files=[])
        data[unit] = dict(
            base_variants=sorted(base), cand_variants=sorted(cand),
            equal=equal, modules=len(set(view["loaded_before"]) |
                                     set(view["loaded"])),
            files=len(view["files"]),
            base_counts=[v["count"] for v in base.values()],
            cand_counts=[v["count"] for v in cand.values()])
        why = ""
        if len(base) != 1:
            why = "%s: the baseline's processes have %d different views " \
                "(a harness fault)" % (unit, len(base))
        elif len(cand) != 1:
            why = "%s: the candidate's processes have %d different views" \
                % (unit, len(cand))
        elif not equal:
            why = "masked loaded sets differ in %s: %s" % (
                unit, view_difference(one(base), one(cand)))
        checks.ok("L1.masked-sets-equal." + unit, "L1", equal, why,
                  "base and candidate have the same masked view "
                  "(%d variant(s) each)" % len(base))
    return data


def check_load_rules(report, receipts, checks):
    """The TASK32 rules again, on the archive: every path inside its root
    and no extension module (check_loaded), candidate stems within the
    baseline's (check_new_stems)."""
    bad = []
    for r in receipts:
        side = r["side"]
        try:
            d.check_loaded(r["stats"], Path(report["roots"][side]),
                           report["reporter"][side]["dir"], side == "cand")
        except (d.Refusal, d.Blocked) as error:
            bad.append("%s: %s" % (
                d.label_of(r["workload"], r["phase"], r["pair"],
                           r["selection"], r["rep"]), error))
    checks.ok("L1.paths-and-extensions", "L1", not bad,
              "; ".join(bad[:3]),
              "every loaded path is inside its root; no extension module")
    try:
        d.check_new_stems(receipts)
        stems = True, ""
    except (d.Refusal, d.Blocked) as error:
        stems = False, str(error)
    checks.ok("L1.new-stems", "L1", stems[0], stems[1],
              "candidate stems are within the baseline's")


def unit_data(report, receipts, unit, checks):
    mine = [r for r in receipts if r["workload"] == unit]
    sides = {}
    for g in ("base", "cand", "control"):
        rows = [r for r in mine if group_of(r) == g]
        sides[g] = dict(n=len(rows), fields={
            f: summarize([field_of(r, f) for r in rows])
            for f in ALL_FIELDS})
    paired = {}
    result = report["outcome"]["results"][unit]["candidate"]["metrics"]
    control = report["outcome"]["results"][unit]["control"]["metrics"]
    for f in ALL_FIELDS:
        ps = pair_means(receipts, unit, f)
        rs = ratios(ps)
        row = dict(pairs=len(ps), usable=len(rs),
                   median_paired_ratio=median(rs))
        if f in REPORTED:
            rep = result[REPORTED[f]]
            row["reported"] = dict(
                median_paired_ratio=rep["median_paired_ratio"],
                bootstrap_95=rep["paired_ratio_bootstrap_95_percent"],
                decision=rep["decision"])
            row["control_reported"] = dict(
                median_paired_ratio=control[REPORTED[f]][
                    "median_paired_ratio"],
                bootstrap_95=control[REPORTED[f]][
                    "paired_ratio_bootstrap_95_percent"])
            ok = rs and math.isclose(median(rs), rep["median_paired_ratio"],
                                     rel_tol=1e-9)
            checks.ok("S3.ties-to-report.%s.%s" % (unit, f), "S3", ok,
                      "median of the paired ratios %s differs from the "
                      "report's %s" % (median(rs),
                                       rep["median_paired_ratio"]),
                      "recomputed median equals the report's")
        paired[f] = row
    return dict(sides=sides, paired=paired)


def attribution(receipts, unit, row):
    """Q10: where a reported GC CPU excess comes from: GC counts per
    process and size_heap, base against candidate (and against the B/B
    control for the noise)."""
    def values(group, field):
        return [field_of(r, field) for r in receipts
                if r["workload"] == unit and group_of(r) == group]

    def per_gc(group):
        return [r["stats"]["gc_time"] / (r["stats"]["gc_full"] +
                                         r["stats"]["gc_partial"])
                for r in receipts if r["workload"] == unit and
                group_of(r) == group and
                r["stats"]["gc_full"] + r["stats"]["gc_partial"]]

    def total(group):
        return [r["stats"]["gc_full"] + r["stats"]["gc_partial"]
                for r in receipts if r["workload"] == unit and
                group_of(r) == group]

    out = dict(unit=unit, reported={
        f: row["paired"][f]["reported"] for f in ALL_FIELDS
        if "reported" in row["paired"][f]}, groups={},
        ratios_of_medians={})
    quantities = {f: (lambda g, f=f: values(g, f)) for f in ALL_FIELDS}
    quantities["gc_collections"] = total
    quantities["gc_time_per_collection"] = per_gc
    for g in ("base", "cand", "control"):
        out["groups"][g] = {q: dict(summarize(fn(g)), values=sorted(fn(g)))
                            for q, fn in quantities.items()}
    for q, fn in quantities.items():
        b, c, k = (median(fn(g)) for g in ("base", "cand", "control"))
        out["ratios_of_medians"][q] = dict(
            cand_over_base=c / b if b else None,
            control_over_base=k / b if b else None)
    # pair level: does the GC time ratio follow the count or size ratio?
    # Every series is taken over the same pairs: those with a usable
    # ratio in all of them.
    pc = {f: {r["pair"]: r for r in pair_means(receipts, unit, f)} for f in
          ("gc_time", "gc_full", "gc_partial", "size_heap", "maxrss")}
    series = {f: {i: ratio_of(r) for i, r in pc[f].items()}
              for f in ("gc_time", "size_heap", "maxrss")}
    series["gc_collections"] = {}
    for i, x in pc["gc_full"].items():
        y = pc["gc_partial"].get(i)
        series["gc_collections"][i] = None if y is None else ratio_of(dict(
            baseline=x["baseline"] + y["baseline"]
            if None not in (x["baseline"], y["baseline"]) else None,
            candidate=x["candidate"] + y["candidate"]
            if None not in (x["candidate"], y["candidate"]) else None))
    kept = sorted(set.intersection(*(
        {i for i, r in v.items() if r is not None}
        for v in series.values())))
    out["pairs_kept"] = kept
    out["pairs_total"] = len(pc["gc_time"])
    out["pair_ratios"] = {q: [v[i] for i in kept]
                          for q, v in series.items()}
    corr = {}
    if len(kept) > 2:
        for q in ("gc_collections", "size_heap", "maxrss"):
            try:
                corr[q] = statistics.correlation(
                    [math.log(x) for x in out["pair_ratios"]["gc_time"]],
                    [math.log(x) for x in out["pair_ratios"][q]])
            except statistics.StatisticsError:
                corr[q] = None
    out["log_ratio_correlation_with_gc_time"] = corr
    return out


def verify_archive(folder, report, checks, replay, repo, ledger=None):
    """The seals as the TASK32 replay checks them: the report schema and
    success, then every process by `d.check_receipt` (seal, label,
    agreement with the report, command, layout and every per-process
    validation), the report's seal against the ledger, and (`replay`) the
    whole TASK32 replay `replay_one`, which repeats all of it and every
    decision. `repo` is the repository that holds this tool (the replay's
    counts-commit rule), not the one of the pins."""
    ok = report.get("schema") == d.SCHEMA and report.get("success") is True
    checks.ok("archive.report", "L1/S3", ok,
              "not a successful %s run" % d.SCHEMA, "report is %s, success"
              % d.SCHEMA)
    if not ok:
        raise Refusal("not a TASK32 downstream report")
    bad, receipts = [], []
    for entry in report["runs"]:
        try:
            receipts.append(d.check_receipt(
                folder, report, entry, report["references"]))
        except (d.Refusal, d.Blocked, ValueError, OSError, KeyError,
                AssertionError) as error:
            bad.append("%s: %s" % (entry.get("receipt"), error))
    checks.ok("archive.seals", "L1/S3", not bad,
              "%d bad receipt(s): %s" % (len(bad), "; ".join(bad[:3])),
              "%d receipts pass d.check_receipt" % len(receipts))
    if bad:
        raise Refusal("the archive's seals do not hold")
    seal = a.seal(folder / "downstream.json")
    if report.get("mode") in d.DECISIVE:
        try:
            d.check_ledger(ledger or d.ledger_path(report["repo"]), report,
                           seal, d.stage_status(report["outcome"][
                               "results"]))
            checks.add("archive.ledger", "L1/S3", "pass",
                       "the ledger closes this report's seal")
        except (d.Refusal, d.Blocked, ValueError, KeyError,
                OSError) as error:
            checks.add("archive.ledger", "L1/S3", "fail", str(error))
    else:
        checks.add("archive.ledger", "L1/S3", "pass",
                   "an information run: no decision attempt")
    if not replay:
        checks.add("archive.replay", "L1/S3", "skipped",
                   "--no-replay: the TASK32 replay was not run")
    else:
        try:
            info, _ = d.replay_one(folder, ledger=ledger, repo=repo)
            checks.add("archive.replay", "L1/S3", "pass",
                       "replayed %d processes, exit %s" % (
                           info["replayed"], info.get("exit")))
        except (d.Refusal, d.Blocked, ValueError, KeyError, OSError,
                AssertionError) as error:
            checks.add("archive.replay", "L1/S3", "fail", str(error))
    return receipts


def reported_intervals(report):
    """[(unit, metric, low, decision)] of every metric of the candidate
    outcome that has a bootstrap interval."""
    out = []
    for unit, result in report["outcome"]["results"].items():
        for name, m in result["candidate"]["metrics"].items():
            interval = m.get("paired_ratio_bootstrap_95_percent")
            if interval:
                out.append((unit, name, interval[0], m.get("decision")))
    return out


def archive_report(folder, repo, replay, checks, ledger=None):
    """The archive report, under the TASK32 table of the run archived (the
    C32 `task32` or TASK37's `task37-t32`: its seals, replay and ledger
    are that table's, whichever table is active)."""
    run = a.load(Path(folder).resolve(strict=True) / "downstream.json")
    table = run.get("table", T32.name)
    require(table in ARCHIVE_TABLES, "the archive is of table %s, not one "
            "of %s" % (table, ", ".join(ARCHIVE_TABLES)))
    with d.using_table(table):
        return archive_in_table(folder, repo, replay, checks, ledger)


def archive_in_table(folder, repo, replay, checks, ledger=None):
    folder = Path(folder).resolve(strict=True)
    report = a.load(folder / "downstream.json")
    receipts = verify_archive(folder, report, checks, replay, repo, ledger)
    check_load_rules(report, receipts, checks)
    data = dict(workloads=list(report["workloads"]),
                loaded=check_loaded_sets(report, receipts, checks),
                units={}, attribution={}, above=[])
    for unit in report["workloads"]:
        data["units"][unit] = unit_data(report, receipts, unit, checks)
    for unit, metric, low, decision in reported_intervals(report):
        if low > 1:
            data["above"].append(dict(
                unit=unit, field=metric, low=low, decision=decision,
                wholly_above_margin=low > ABOVE))
    wanted = sorted({Q10_UNIT} | {x["unit"] for x in data["above"]
                                  if x["wholly_above_margin"]})
    for unit in wanted:
        if unit in data["units"]:
            data["attribution"][unit] = attribution(
                receipts, unit, data["units"][unit])
    checks.ok("Q10.attribution-data", "Q10",
              Q10_UNIT in data["attribution"] and all(
                  v["groups"]["base"]["gc_full"]["n"] and
                  v["groups"]["cand"]["gc_full"]["n"]
                  for v in data["attribution"].values()),
              "no GC attribution data for %s" % Q10_UNIT,
              "GC counts, GC time, size_heap and maxrss, base against "
              "candidate, for %s" % ", ".join(wanted))
    inputs = dict(folder=str(folder), downstream=a.seal(
        folder / "downstream.json"), receipts=len(receipts),
        base=report["base"], cand=report["cand"],
        manifest=report["manifest"], replay_repo=str(repo))
    return inputs, data


# ----------------------------------------------------------------- CLI

def default_repo():
    p = subprocess.run(["git", "-C", str(HERE), "rev-parse",
                        "--show-toplevel"], stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, stdin=subprocess.DEVNULL)
    require(p.returncode == 0, "not inside a git repository")
    return Path(p.stdout.decode().strip())


class Parser(argparse.ArgumentParser):
    """A usage error is a refusal: exit 3, not argparse's 2 (which this
    tool's protocol reads as inconclusive)."""

    def error(self, message):
        self.print_usage(sys.stderr)
        self.exit(FAIL, "%s: error: %s\n" % (self.prog, message))


def build_parser():
    parser = Parser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="command", required=True,
                                parser_class=Parser)
    for name in ("archive", "audit", "harvest"):
        p = sub.add_parser(name)
        p.add_argument("--out", required=True,
                       help="report FILE.json, or a directory (for "
                       "harvest: the directory of the sealed logs)")
    sub.choices["archive"].add_argument("--archive", type=Path,
                                        required=True)
    sub.choices["archive"].add_argument(
        "--declared", type=Path, default=DECLARED, help="the declaration "
        "the report is bound to (default task33_declared.json; TASK37's "
        "is task37_declared.json)")
    sub.choices["archive"].add_argument("--no-replay", action="store_true",
                                        help="skip the TASK32 replay: the "
                                        "report is inconclusive (exit 2)")
    sub.choices["archive"].add_argument(
        "--ledger", type=Path, help="the TASK32 attempts ledger (default: "
        "the one of the run's repository)")
    for name in ("audit", "harvest"):
        p = sub.choices[name]
        p.add_argument("--manifest", type=Path, required=True,
                       help="the TASK32 snapshot manifest the roots are "
                       "bound to")
        p.add_argument("--declared", type=Path, default=DECLARED)
        p.add_argument("--cand-root", type=Path, required=True)
    sub.choices["audit"].add_argument("--base-root", type=Path,
                                      required=True)
    sub.choices["audit"].add_argument(
        "--repo", type=Path, help="git repository holding the pinned "
        "commits (the pins only; default: the one holding this file)")
    return parser


def run(args):
    """The command, with its declaration selected for its length."""
    with using_declared(getattr(args, "declared", None)):
        return run_command(args)


def run_command(args):
    checks, inputs, data = Checks(), {}, {}
    try:
        if args.command == "archive":
            # the replay's repository is the one that holds this tool
            inputs, data = archive_report(
                args.archive, default_repo(), not args.no_replay, checks,
                args.ledger)
        else:
            declared = load_declared(args.declared)
            check_declaration(declared, checks)
            roots = dict(cand=args.cand_root)
            if args.command == "audit":
                roots["base"] = args.base_root
            inputs = dict(
                declared=a.seal(args.declared),
                manifest=check_provenance(args.manifest, roots, declared,
                                          checks),
                cand_root=str(args.cand_root))
            if args.command == "audit":
                repo = args.repo or default_repo()
                inputs.update(base_root=str(args.base_root),
                              repo=str(repo))
                data = audit(repo, args.base_root, args.cand_root,
                             declared, checks)
            else:
                data = harvest(args.cand_root, args.out, checks, declared)
    except Exception as error:
        # a malformed manifest, declaration or tree of any kind is a
        # refusal (exit 3), never a traceback
        checks.add("refused", args.command, "fail", "%s: %s" % (
            type(error).__name__, error) if not isinstance(
                error, (Refusal, a.Blocked)) else str(error))
    out = args.out if args.command != "harvest" else \
        Path(args.out) / (args.command + ".json")
    return write_report(out, args.command, checks, inputs, data)


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        report, path, seal = run(args)
    except (Refusal, a.Blocked, ValueError, OSError) as error:
        print("%s: cannot write the report: %s" % (args.command, error),
              file=sys.stderr)
        return FAIL
    print(summary_line(args.command, report, path, seal))
    return report["exit"]


if __name__ == "__main__":
    sys.exit(main())
