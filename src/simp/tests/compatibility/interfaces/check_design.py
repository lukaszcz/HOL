#!/usr/bin/env python3
"""Fail-closed TASK_08 design/type-boundary gate; no production migration."""
import argparse
import csv
import hashlib
import io
import json
import os
from functools import lru_cache
from pathlib import Path
import re
import shutil
import sys
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(HERE.parent))
from check_task27_docs import (NAME, signature_symbols,  # noqa: E402
                               strip_sml_comments)
# The Holmake check builds and runs the design gate; one hour bounds it, and
# its children read /dev/null, not the caller's standard input.
TIMEOUT = 3600
MIGRATION = HERE.parent / "migration"
TABLE = MIGRATION / "final-apis.tsv"
SHARED = MIGRATION / "shared-exports.tsv"
BASE = "cccaa27d70"
FIELDS = ["group", "old_api", "replacement", "domain", "construction",
          "witness", "owners"]
# Develop module -> (extension module, extension signature in the repo).
# Every extension signature of a develop module must be listed; see
# validate_extension_coverage.
MODULES = {
    "Traverse": ("TraverseExt", "src/simp/src/TraverseExt.sig"),
    "Cond_rewr": ("Cond_rewrExt", "src/simp/src/Cond_rewrExt.sig"),
    "Opening": ("OpeningExt", "src/simp/src/OpeningExt.sig"),
    "Travrules": ("TravrulesExt", "src/simp/src/TravrulesExt.sig"),
    "simpLib": ("simpExtLib", "src/simp/src/simpExtLib.sig"),
    "congLib": ("congExtLib", "src/simp/src/congExtLib.sig"),
    "boolSimps": ("boolSimpsExt", "src/simp/src/boolSimpsExt.sig"),
    "combinSimps": ("combinSimpsExt", "src/simp/src/combinSimpsExt.sig"),
    "pureSimps": ("pureSimpsExt", "src/simp/src/pureSimpsExt.sig"),
    "intReduce": ("intReduceExt", "src/integer/intReduceExt.sig"),
    "integer_wordLib": ("integer_wordLibExt",
                        "src/integer/integer_wordLibExt.sig"),
    "listSimps": ("listSimpsExt", "src/list/src/listSimpsExt.sig"),
    "numSimps": ("numSimpsExt", "src/num/arith/src/numSimpsExt.sig"),
    "pred_setSimps": ("pred_setSimpsExt",
                      "src/pred_set/src/pred_setSimpsExt.sig"),
    "realSimps": ("realSimpsExt", "src/real/realSimpsExt.sig"),
}
BOUNDARIES = {
    "T1": "extension reducer factory; explicit ordinary lift; no inventory",
    "R1": "tracked rule installation; paired preparation once",
    "C1": "extension fragment/congruence factory before installation",
    "C2": "extension congset from explicit fragments; no opaque congset lift",
    "B1": "extension EMPTY/PURE/BOOL before relevant maker/rule/dproc",
    "P1": "already tracked object; shallow extraction shares actual controls",
    "S1": "typed extension base before strategy installation",
    "F1": ("opt-in extension fragment/simpset values of a develop library; "
           "no default simpset update"),
    "M1": ("pure marker construction/classification; "
           "typed engine at processing"),
    "E1": "already tracked input; reset versus preserving replay explicit",
    "V1": "tracked fragment slots then install events; prepare bundle once",
    "A1": ("tracked invocation before supplied-rule binding; "
           "BOUND never reinstalls"),
    "H1": ("tracked ambient net before private derivation; "
           "opaque internals excluded"),
    "D1": "typed provider/producer before source use; explicit typed updates",
    "I1": "retain singleton owner; split persistence explicitly initialized",
}
WITNESS = {"T1": "T", "R1": "C", "C1": "R", "C2": "G",
           "B1": "S", "P1": "S", "S1": "S", "M1": "S",
           "E1": "S", "F1": "Ext", "V1": "S", "A1": "S", "H1": "S",
           "D1": "Default", "I1": "shared"}
NEGATIVES = ["reducer-to-legacy", "reducer-from-legacy", "set-to-legacy",
             "set-from-legacy", "fragment-to-legacy", "fragment-from-legacy",
             "congset-to-legacy", "provider-from-legacy"]


def read_old_rows():
    with (MIGRATION / "apis.tsv").open() as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


# Owner stages of a row in apis.tsv: two-digit TASK numbers, comma-separated
# and strictly ascending (08,11,13); the final table appends ;27.
OWNERS = re.compile(r"\d\d(?:,\d\d)*")


def valid_owners(owners):
    stages = owners.split(",")
    return (OWNERS.fullmatch(owners) is not None and
            stages == sorted(set(stages)))


def expected_rows(old=None):
    if old is None:
        old = read_old_rows()
    rows = []
    for row in old:
        if not valid_owners(row["owners"]):
            raise ValueError("malformed owner field: " + row["old_api"] +
                             ": " + repr(row["owners"]))
        group, api = row["group"], row["old_api"]
        module, name = api.split(".", 1)
        replacement = MODULES.get(module, (module,))[0] + "." + name
        domain = "extension; ordinary API unchanged"
        witness = WITNESS[group]
        if module == "simpLib":
            witness = "S"
        elif module == "Opening":
            witness = "O"
        if group == "I1" or module in {"simpMarkerLib", "splitLib"}:
            domain, witness = "shared singleton; no type migration", "shared"
        elif group == "D1":
            domain = ("external typed extension variant; "
                      "retain ordinary variant")
            if module == "seedCollections":
                domain = ("ordinary producer retained; "
                          "explicit extension recipe if selected")
        elif group in {"B1", "C2", "F1"}:
            domain = ("parallel ordinary and extension APIs; "
                      "no ordinary migration")
        if name == "legacy_traversedata_for_ss":
            replacement = "REMOVED; use simpExtLib.traversedata_for_ss"
        rows.append(dict(zip(FIELDS, [group, api, replacement, domain,
            BOUNDARIES[group], witness, row["owners"] + ";27"])))
    return rows


INPUTS = HERE.parent / "inputs" / "develop"
PAIRED_KINDS = {"existing", "val", "type", "datatype", "constructor"}


# Names `include Abbrev` brings in are the shared basic types, identical in
# a develop module and its extension; they never need a row.
INCLUDES = {"Abbrev": set(), "Task08ReducerTypes": set()}  # (ns, name) pairs


@lru_cache(maxsize=None)
def declared(text):
    """Names a signature text declares: not comments or `signature X = sig`.

    Abbrev only adds the shared basic types, never a module's own names;
    Task08ReducerTypes is concatenated with its includer where it is used."""
    return frozenset(signature_symbols(
        text, {k: {n for _, n in v} for k, v in INCLUDES.items()}))


UNSUPPORTED = re.compile(
    r"\b(structure|functor|sharing|and|withtype|where|abstype)\b")


def normalise(spec):
    """Whitespace-insensitive spec text: runs of blanks collapse, blanks
    around : , ; ( ) { } * = -> go, and a trailing ; goes."""
    spec = re.sub(r"\s+", " ", spec).strip()
    spec = re.sub(r"\s*([:,;(){}*=]|->)\s*", r"\1", spec)
    return re.sub(r";$", "", spec).strip()


@lru_cache(maxsize=None)
def parse_specs(text):
    """((namespace, name), normalised spec text) pairs of a signature.

    "type" is the namespace of type, eqtype and datatype names, "value" of
    val, exception and datatype constructors (a name may be in both, so a
    flat name set is not enough).  Includes resolve through INCLUDES, whose
    values are sets of (namespace, name) pairs; an unknown include fails, as
    does syntax this flat reader does not handle: structure, functor and
    sharing specs, `and` (a spec-level conjunction), `withtype`, `where` and
    `abstype`; the scan covers the whole signature text."""
    text = strip_sml_comments(text)
    unsupported = UNSUPPORTED.search(text)
    if unsupported:
        raise ValueError("unsupported signature syntax: " +
                         unsupported.group(1))
    params = r"(?:\([^)]*\)\s*|'+[A-Za-z_0-9]+\s+)?"
    declaration = re.compile(
        rf"\b(val|type|eqtype|datatype|exception|include)\s+{params}"
        rf"(?:op\s+)?({NAME})")
    matches = list(declaration.finditer(text))
    result = []
    for i, match in enumerate(matches):
        kind, name = match.groups()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        if kind == "include":
            tail = re.sub(r"\bend\s*$", "", text[match.start() + 7:end])
            for included in re.findall(r"[^\s;]+", tail):
                if included not in INCLUDES:
                    raise ValueError("unresolved signature include: " +
                                     included)
                result.extend((key, "include " + included)
                              for key in INCLUDES[included])
            continue
        body = text[match.end():end]
        spec = re.sub(r"\s+", " ", text[match.start():end]).strip()
        spec = normalise(re.sub(r"\s*;?\s*\bend$", "", spec))
        if kind in {"val", "exception"}:
            result.append((("value", name), spec))
            continue
        result.append((("type", name), spec))
        if kind == "datatype" and not re.match(r"\s*=\s*datatype\b", body):
            for ctor in re.findall(rf"(?:=|\|)\s*({NAME})", body):
                result.append((("value", ctor), spec))
    return tuple(result)


@lru_cache(maxsize=None)
def namespaced(text):
    """(namespace, name) pairs a signature declares; see parse_specs."""
    return frozenset(key for key, _ in parse_specs(text))


def exports(text, name):
    return name in declared(text)


def validate_existing(old_rows=None):
    """Every kind=existing old name must be exported by develop's .sig."""
    if old_rows is None:
        old_rows = read_old_rows()
    for row in old_rows:
        if row["kind"] != "existing":
            continue
        module, name = row["old_api"].split(".", 1)
        path = INPUTS / (module + ".sig")
        if not path.is_file():
            raise ValueError("no develop signature for existing row: " +
                             row["old_api"])
        if not exports(path.read_text(), name):
            raise ValueError("existing row not exported by develop: " +
                             row["old_api"])


def read_shared():
    """api -> justification of shared-exports.tsv (columns old_api and
    justification); a repeated entry or an empty or missing justification
    fails."""
    result = {}
    with SHARED.open() as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            api = row["old_api"]
            why = (row.get("justification") or "").strip()
            if api in result:
                raise ValueError("repeated shared-exports entry: " + api)
            if not why:
                raise ValueError("empty shared-exports justification: " +
                                 api)
            result[api] = why
    return result


# Extension signatures are recognised by name alone: MExt.sig or pExtLib.sig.
EXT_SIG = re.compile(r"\w+Ext(?:Lib)?\.sig")
# The scan prunes every dot-directory (.git, .hol, .agent-files, ...) and
# every directory named sigobj or tests, so copies there are never counted.
PRUNED_DIRS = {"sigobj", "tests"}
# Extension signatures that have no develop counterpart, so MODULES does not
# list them: path -> reason.  Each entry needs a reason and must exist.
EXCLUDED_EXT_SIGS = {}


def scan_extension_sigs(root=ROOT):
    """Repo-relative paths of the extension signatures under root, found by
    walking the file system (not git); dot-directories, sigobj and tests
    directories and symbolic links are skipped."""
    found = []
    for directory, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs
                   if not d.startswith(".") and d not in PRUNED_DIRS]
        for file in files:
            full = os.path.join(directory, file)
            # sigobj holds symlinks to the real signatures: not files.
            if EXT_SIG.fullmatch(file) and not os.path.islink(full):
                found.append(os.path.relpath(full, root))
    return sorted(found)


def validate_extension_coverage(root=ROOT, modules=None, excluded=None,
                                develop=INPUTS):
    """Every extension signature in the tree is in MODULES or excluded.

    Fails closed: each MODULES extension must be found by the scan and
    exist, each MODULES develop module needs its pinned signature, and each
    exclusion needs a reason and a signature the scan finds."""
    if modules is None:
        modules = MODULES
    if excluded is None:
        excluded = EXCLUDED_EXT_SIGS
    found = set(scan_extension_sigs(root))
    covered = {path for _, path in modules.values()}
    for module, (_, path) in modules.items():
        if not (Path(root) / path).is_file():
            raise ValueError("MODULES extension signature missing: " + path)
        if path not in found:
            raise ValueError("MODULES extension signature not found by "
                             "the scan: " + path)
        if not (Path(develop) / (module + ".sig")).is_file():
            raise ValueError("no pinned develop signature for " + module)
    for path, reason in excluded.items():
        if not reason.strip():
            raise ValueError("exclusion without a reason: " + path)
        if path in covered:
            raise ValueError("exclusion is in MODULES: " + path)
        if path not in found:
            raise ValueError("stale exclusion, signature absent: " + path)
    for path in sorted(found):
        if path not in covered and path not in excluded:
            raise ValueError("extension signature not covered by MODULES: " +
                             path)


def validate_completeness(old_rows=None, shared=None,
                          develop=INPUTS, root=ROOT):
    """Every name develop's M exports that extension M' also declares has
    either a row or a shared-exports justification, never both."""
    if old_rows is None:
        old_rows = read_old_rows()
    if shared is None:
        shared = read_shared()
    rows = {row["old_api"] for row in old_rows}
    common = set()
    for module, (_, path) in sorted(MODULES.items()):
        old_text = (develop / (module + ".sig")).read_text()
        new_text = (root / path).read_text()
        # A name may be a type in one signature and a value in the other;
        # compare per namespace, then name the shared exports.
        both = namespaced(old_text) & namespaced(new_text)
        for name in sorted({n for _, n in both}):
            api = module + "." + name
            common.add(api)
            if api in shared and api in rows:
                raise ValueError("stale shared-exports entry has a row: " +
                                 api)
            if api not in shared and api not in rows:
                raise ValueError("shared export has neither row nor "
                                 "shared-exports entry: " + api)
    for api in shared:
        if api not in common:
            raise ValueError("stale shared-exports entry, not a shared "
                             "export: " + api)


SHARED_CHECK = HERE / "sharedExportsCheck.sml"
SYMBOL = re.compile(r"[A-Za-z_][\w']*")


def type_params(spec):
    """The type-variable prefix of a type spec ('', "'a", "('a,'b)"), as
    SML writes it before the type name."""
    rest = re.sub(r"^(?:type|eqtype|datatype)\s*", "", spec)
    if rest.startswith("("):
        return rest[:rest.index(")") + 1]
    found = re.match(r"'+\w+(?=\s)", rest)
    return found.group(0) if found else ""


def is_function_spec(spec):
    """Whether `val x : T` has a top-level `->` in T (outside parentheses
    and brackets); pointer equality cannot tell equal immediates apart."""
    depth = 0
    text = spec.split(":", 1)[1] if ":" in spec else ""
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "-" and text[i + 1:i + 2] == ">" and depth == 0:
            return True
    return False


def shared_entries(shared=None, develop=INPUTS, root=ROOT):
    """(namespace, module, extension module, name, type params) of every
    allowlist entry, in a fixed order.  Cheap pre-filters only; the compiled
    check is the authority.  Every entry names a shared export; a value
    entry's develop and extension specs are equal and are plain `val`
    specs (an exception or constructor is not an object to compare); a value
    entry has a function type (a top-level `->`; pointer equality cannot tell
    immediates apart, so this rule is not left to the compiler); a type
    entry has one arity in both signatures; names are plain identifiers."""
    if shared is None:
        shared = read_shared()
    entries = []
    for module, (ext, path) in sorted(MODULES.items()):
        old = dict(parse_specs((Path(develop) / (module + ".sig"))
                               .read_text()))
        new = dict(parse_specs((Path(root) / path).read_text()))
        for key in sorted(old.keys() & new.keys()):
            api = module + "." + key[1]
            if api not in shared:
                continue
            ns, name = key
            if not SYMBOL.fullmatch(name):
                raise ValueError("entry is not a plain identifier: " + api)
            if ns == "value":
                if old[key] != new[key]:
                    raise ValueError("value entry has distinct specs, "
                                     "needs a row: " + api)
                if not old[key].startswith("val "):
                    raise ValueError("value entry is not a val spec: " + api)
                if not is_function_spec(old[key]):
                    raise ValueError("value entry is not a function, "
                                     "needs a row: " + api)
                params = ""
            else:
                params = type_params(old[key])
                if params != type_params(new[key]):
                    raise ValueError("type entry has distinct arities: " +
                                     api)
            entries.append((ns, module, ext, name, params))
    named = {m + "." + n for _, m, _, n, _ in entries}
    for api in shared:
        if api not in named:
            raise ValueError("allowlist entry names no shared export: " +
                             api)
    return entries


def validate_entries(shared=None, develop=INPUTS, root=ROOT):
    shared_entries(shared, develop, root)


CHECK_HEAD = """\
(* GENERATED by check_design.py --write-shared-check from
   ../migration/shared-exports.tsv; do not edit.  Each allowlisted shared
   export is the identical develop object: a value by pointer equality
   (its two types must unify), a type by a coercion in both directions
   (it compiles only if the types are equal).  A failure stops the build. *)
val failures = ref 0
val checks = ref 0
fun passed what = (checks := !checks + 1;
                   print ("shared export ok: " ^ what ^ "\\n"))
fun same_value what a b =
  if PolyML.pointerEq (a, b) then passed what
  else (failures := !failures + 1;
        print ("SHARED_EXPORT_FAILED: " ^ what ^
               " is not the develop object\\n"))
"""
CHECK_TAIL = """\
val _ = if !failures = 0 then
          print ("SHARED_EXPORTS_CHECK_OK entries=" ^
                 Int.toString (!checks) ^ "\\n")
        else raise Fail "shared export check failed"
"""


def entry_check(entry):
    ns, module, ext, name, params = entry
    api, ext_api = module + "." + name, ext + "." + name
    if ns == "value":
        return f'val _ = same_value "{api}" {api} {ext_api}\n'
    prefix = params + " " if params else ""
    return (f"val _ = fn (v : {prefix}{api}) => (v : {prefix}{ext_api})\n"
            f"val _ = fn (v : {prefix}{ext_api}) => (v : {prefix}{api})\n"
            f'val _ = passed "type {api}"\n')


def shared_check_text(shared=None, entries=None):
    if entries is None:
        entries = shared_entries(shared)
    return CHECK_HEAD + "".join(map(entry_check, entries)) + CHECK_TAIL


# Negative controls, from the same generator: a type the extension keeps
# distinct must not compile, a value of one type that is evaluated again in
# the extension must compare unequal.
NEGATIVES_SHARED = {
    "sharedExportsNegType": ("type", "simpLib", "simpExtLib", "ssfrag", ""),
    "sharedExportsNegValue": ("value", "boolSimps", "boolSimpsExt",
                              "SimpL", ""),
}


def negative_shared_texts():
    return {name: shared_check_text(entries=[entry])
            for name, entry in NEGATIVES_SHARED.items()}


def validate_shared_check_file():
    if SHARED_CHECK.read_text() != shared_check_text():
        raise ValueError("sharedExportsCheck.sml is stale; run "
                         "check_design.py --write-shared-check")


def table_text(rows):
    stream = io.StringIO()
    writer = csv.DictWriter(stream, FIELDS, delimiter="\t",
                            lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue()


def validate_table(text):
    rows = list(csv.DictReader(io.StringIO(text), delimiter="\t"))
    old = read_old_rows()
    expected = expected_rows(old)
    validate_existing(old)
    validate_extension_coverage()
    validate_completeness(old)
    validate_entries()
    validate_shared_check_file()
    if rows != expected:
        raise ValueError("missing/stale final API decision; "
                         "do not drop a consumer")
    api = (HERE / "Task08API.sml").read_text()
    blocks = dict(re.findall(
        r"  structure (\w+) :\s*\n  sig\n(.*?)\n  end", api, re.S))
    blocks["T"] = (HERE / "Task08TraverseExt.sml").read_text() + (
        HERE / "Task08ReducerTypes.sml").read_text()
    for row in rows:
        witness = row["witness"]
        name = row["replacement"].rsplit(".", 1)[-1]
        if witness == "Default":
            # External producer names are not exports of the core prototype.
            # Their typed construction boundary is checked, not their future
            # TASK_25 implementation. Never count these as compiled clients.
            if not all(exports(blocks["Default"], n) for n in
                       ["recipe", "provider", "build", "get_of", "Update"]):
                raise ValueError("missing typed external provider boundary")
        elif witness == "Ext":
            # The extension's own signature in the repo, not a prototype.
            module = row["old_api"].split(".")[0]
            source = (ROOT / MODULES[module][1]).read_text()
            if (row["replacement"].split(".")[0] != MODULES[module][0] or
                    not exports(source, name)):
                raise ValueError("missing extension export: " + name)
        elif witness == "shared":
            module = row["old_api"].split(".")[0]
            directory = "src/1" if module == "ThmAttribute" else "src/simp/src"
            source = (ROOT / directory / (module + ".sig")).read_text()
            if not exports(source, name):
                raise ValueError("missing singleton export: " + name)
        elif not exports(blocks[witness], name):
            raise ValueError("missing scoped prototype export: " + name)
    return len(rows)


def validate_graph(graph):
    nodes = graph["nodes"]
    order, active, done = [], set(), set()
    def visit(name):
        if name not in nodes:
            raise ValueError("unknown module " + name)
        if name in active:
            raise ValueError("module cycle at " + name)
        if name in done:
            return
        active.add(name)
        for dependency in nodes[name]["imports"]:
            visit(dependency)
        active.remove(name)
        done.add(name)
        order.append(name)
    for name in nodes:
        layers = {"ordinary", "shared", "extension", "service"}
        if nodes[name]["layer"] not in layers:
            raise ValueError("unknown layer")
        visit(name)
    def closure(name, seen):
        if name not in seen:
            seen.add(name)
            for dep in nodes[name]["imports"]:
                closure(dep, seen)
        return seen
    for name, node in nodes.items():
        if node["layer"] in {"ordinary", "shared"}:
            bad = [n for n in closure(name, set())
                   if nodes[n]["layer"] in {"extension", "service"}]
            if bad:
                raise ValueError(
                    "ordinary/shared import reaches extension: " + name)
    if graph["cutovers"] != list(range(9, 17)):
        raise ValueError("missing structural cutover")
    ids = set()
    for edge in graph["transitional_edges"]:
        if (edge["id"] in ids or edge["from"] not in nodes or
                edge["to"] not in nodes):
            raise ValueError("invalid transitional edge")
        ids.add(edge["id"])
        if not 9 <= edge["introduced"] < edge["remove"] <= 16:
            raise ValueError("unbounded transitional removal owner")
    if ids != {"X1", "X2", "M1", "M2", "M3", "M5a", "M5b"}:
        raise ValueError("missing transitional edge/removal decision")
    introduced = graph["introduced_nodes"]
    expected_introductions = {
        "TraverseExt": 9, "simpExtLib": 10,
        "pureSimpsExt": 10, "boolSimpsExt": 10, "congExtLib": 11,
        "Cond_rewrExt": 12,
        "OpeningExt": 13, "TravrulesExt": 13,
        "combinSimpsExt": 24, "trackedSimpDefaults": 24}
    if introduced != expected_introductions:
        raise ValueError("missing module-availability decision")
    # X1/X2 are the real pre-extraction routes. Future module references
    # have not been introduced into the source yet, not permissive stubs.
    for stage in range(9, 17):
        available = {n for n in nodes if introduced.get(n, 0) <= stage}
        edges = {n: [d for d in nodes[n]["imports"] if d in available]
                 for n in available}
        for e in graph["transitional_edges"]:
            if e["introduced"] <= stage < e["remove"]:
                edges[e["from"]].append(e["to"])
        def walk(n, stack, visited):
            if n in stack:
                raise ValueError("transitional cycle in " + str(stage))
            if n in visited:
                return
            for dep in edges[n]:
                walk(dep, stack | {n}, visited)
            visited.add(n)
        visited = set()
        for n in edges:
            walk(n, set(), visited)
        if stage in {10, 11} and "Cond_rewr" not in edges["simpExtLib"]:
            raise ValueError("missing initial paired compiler route")
        if stage in {10, 11, 12} and "Travrules" not in edges["simpExtLib"]:
            raise ValueError("missing initial threaded compiler route")
    return order


def validate_output(code, output):
    if code != 0 or output.count("TASK08_COMPLETE checks=29") != 1:
        raise ValueError("incomplete/failed executed elaboration")
    for name in NEGATIVES:
        if output.count("static rejection: " + name + " ...") != 1:
            raise ValueError("missing static type rejection: " + name)
    for name in ["Task08API", "Task08TraverseExt", "Task08ReducerTypes",
                 "Task08Clients", "Task08Cutovers", "Task08Controls",
                 "Task08Reducers"]:
        if "TASK08_LOADED " + str(HERE / name) not in output:
            raise ValueError("missing private module path: " + name)


def validate_shared_output(output, entries=None):
    """The compiled identity check ran and passed every entry."""
    if entries is None:
        entries = shared_entries()
    checks = len(entries)
    if "SHARED_EXPORTS_CHECK_OK entries=%d\n" % checks not in output:
        raise ValueError("shared export check did not pass")
    if "SHARED_EXPORT_FAILED" in output:
        raise ValueError("shared export check reported a failure")
    for ns, module, _, name, _ in entries:
        line = "shared export ok: %s%s.%s\n" % (
            "type " if ns == "type" else "", module, name)
        if line not in output:
            raise ValueError("shared export not checked: " + line.strip())


# What each negative control must print when it fails.  In this build a
# .uo is only a dependency stub: the source is compiled and run by the
# executable, so the type control is a static error naming the two types
# and the value control the runtime message naming the entry.
NEGATIVE_SHARED_EXPECT = {
    "sharedExportsNegType": [
        "Type mismatch in type constraint",
        "Can't unify simpLib.ssfrag", "Fail \"Static Errors\""],
    "sharedExportsNegValue": [
        "SHARED_EXPORT_FAILED: boolSimps.SimpL is not the develop object",
        "Fail \"shared export check failed\""],
}


def run_quietly(command, cwd=ROOT):
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                          stdin=subprocess.DEVNULL, timeout=TIMEOUT)


def shared_negative_controls():
    """Build and run each generated negative control in a scratch
    directory; each must build, and its executable must fail in the
    expected way (see NEGATIVE_SHARED_EXPECT).  Receipts."""
    receipts = []
    with tempfile.TemporaryDirectory(prefix="task35-shared-neg-") as temp:
        for name, text in sorted(negative_shared_texts().items()):
            directory = Path(temp) / name
            directory.mkdir()
            (directory / (name + ".sml")).write_text(text)
            (directory / "Holmakefile").write_text(
                f"INCLUDES = {ROOT / 'src/simp/src'}\n"
                f"{name}.exe: {name}.uo\n\t$(HOLMOSMLC) -o $@ $<\n")
            build = run_quietly([
                str(ROOT / "bin/Holmake"),
                "--holstate=" + str(ROOT / "bin/hol.state0"),
                "--no-project", "--no-cache", "--no_prereqs", "-j1",
                "-C", str(directory), name + ".exe"])
            if build.returncode != 0:
                raise ValueError("shared negative control did not build: " +
                                 name + build.stdout + build.stderr)
            result = run_quietly([str(directory / (name + ".exe"))],
                                 directory)
            output = result.stdout + result.stderr
            if result.returncode == 0 or "SHARED_EXPORTS_CHECK_OK" in output:
                raise ValueError("shared negative control passed: " + name)
            for expected in NEGATIVE_SHARED_EXPECT[name]:
                if expected not in output:
                    raise ValueError("shared negative control %s failed "
                                     "unexpectedly, no %r:\n%s" %
                                     (name, expected, output))
            matched = list(NEGATIVE_SHARED_EXPECT[name])
            # "output" is the private full text: main() writes it only to
            # the --output directory and strips it before anything is
            # printed (it holds `Uncaught exception`, which the log judge
            # rightly treats as a failure when it appears in a log).
            receipts.append({
                "control": name, "exit": result.returncode,
                "matched": matched,
                "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
                "output": output})
    return receipts


def execute(negative_controls):
    command = [str(ROOT / "bin/Holmake"),
               "--holstate=" + str(ROOT / "bin/hol.state0"),
               "--no-project", "--no-cache", "-C", str(HERE), "-j1", "check"]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            stdin=subprocess.DEVNULL, timeout=TIMEOUT)
    output = result.stdout + result.stderr
    validate_output(result.returncode, output)
    validate_shared_output(output)
    receipts = [{"argv": command, "exit": result.returncode}]
    if negative_controls:
        import os
        with tempfile.TemporaryDirectory(prefix="task08-negative-") as temp:
            for file in (HERE / "negative").glob("*.ML"):
                shutil.copyfile(file, Path(temp) / file.name)
            accepted = Path(temp) / "reducer-to-legacy.ML"
            accepted.write_text("functor Task08Accept (I : Task08API) =\n"
                                "struct fun f r = I.S.dproc_ss r end\n")
            for kind in ["accepted-body", "missing-file"]:
                if kind == "missing-file":
                    accepted.unlink()
                control = subprocess.run(
                    [str(HERE / "selftest.exe")], cwd=HERE,
                    env={**os.environ, "TASK08_NEGATIVE_DIR": temp},
                    capture_output=True, text=True,
                    stdin=subprocess.DEVNULL, timeout=TIMEOUT)
                text = control.stdout + control.stderr
                if control.returncode == 0 or "TASK08_COMPLETE" in text:
                    raise ValueError(
                        "negative control falsely passed: " + kind)
                receipts.append({"control": kind, "exit": control.returncode})
        receipts += shared_negative_controls()
    return receipts, output


def source_paths():
    """The sources of the verdict: this directory, the final table, and the
    inputs the verdict reads: the shared-exports and apis tables, the
    generated shared-export check, the pinned develop signatures, every
    extension signature and source the checks read, the singleton signatures
    of the `shared` witness, and the signature parser."""
    shared = {row["old_api"].split(".")[0] for row in expected_rows()
              if row["witness"] == "shared"}
    witnesses = [ROOT / ("src/1" if module == "ThmAttribute"
                         else "src/simp/src") / (module + ".sig")
                 for module in sorted(shared)]
    extensions = [ROOT / path for _, path in MODULES.values()]
    extensions += [p.with_suffix(".sml") for p in extensions]
    return sorted(set([p for p in HERE.rglob("*")
                   if p.is_file() and ".hol" not in p.parts and
                   p.suffix in {".sml", ".ML", ".md", ".py", ".json"}]
                  + [HERE / "Holmakefile", TABLE, SHARED,
                     MIGRATION / "apis.tsv",
                     HERE.parent / "check_task27_docs.py"]
                  + list(INPUTS.glob("*.sig")) + [SHARED_CHECK]
                  + witnesses + extensions))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-table", action="store_true")
    parser.add_argument("--write-shared-check", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--negative-controls", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.write_table:
        TABLE.write_text(table_text(expected_rows()))
    if args.write_shared_check:
        SHARED_CHECK.write_text(shared_check_text())
    rows = validate_table(TABLE.read_text())
    order = validate_graph(json.loads((HERE / "graph.json").read_text()))
    result = {"api_decisions": rows, "topological_order": order,
              "cutovers_checked": list(range(9, 17))}
    if args.run:
        result["commands"], output = execute(args.negative_controls)
        for command in result["commands"]:
            text = command.pop("output", None)
            if text is not None and args.output:
                args.output.mkdir(parents=True, exist_ok=True)
                (args.output / (command["control"] + ".log")).write_text(
                    text)
        for line in output.splitlines():
            if line.startswith(("shared export ok:",
                                "SHARED_EXPORTS_CHECK_OK")):
                print(line, file=sys.stderr)
        for command in result["commands"]:
            if str(command.get("control", "")).startswith("sharedExports"):
                print("shared negative control %s failed as expected "
                      "(exit %d)" % (command["control"], command["exit"]),
                      file=sys.stderr)
        if args.output:
            args.output.mkdir(parents=True, exist_ok=True)
            (args.output / "interfaces.log").write_text(output)
        result["log_sha256"] = hashlib.sha256(output.encode()).hexdigest()
    paths = source_paths()
    result["source_sha256"] = {str(p.relative_to(ROOT)):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    if args.output:
        (args.output / "design-check.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
