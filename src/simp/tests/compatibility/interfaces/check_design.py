#!/usr/bin/env python3
"""Fail-closed TASK_08 design/type-boundary gate; no production migration."""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
MIGRATION = HERE.parent / "migration"
TABLE = MIGRATION / "final-apis.tsv"
FIELDS = ["group", "old_api", "replacement", "domain", "construction",
          "witness", "owners"]
MODULES = {"Traverse": "TraverseExt", "Cond_rewr": "Cond_rewrExt",
           "Opening": "OpeningExt", "Travrules": "TravrulesExt",
           "simpLib": "simpExtLib", "congLib": "congExtLib"}
BOUNDARIES = {
    "T1": "extension reducer factory; explicit ordinary lift; no inventory",
    "R1": "tracked rule installation; paired preparation once",
    "C1": "extension fragment/congruence factory before installation",
    "C2": "extension congset from explicit fragments; no opaque congset lift",
    "B1": "extension EMPTY/PURE/BOOL before relevant maker/rule/dproc",
    "P1": "already tracked object; shallow extraction shares actual controls",
    "S1": "typed extension base before strategy installation",
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
           "E1": "S", "V1": "S", "A1": "S", "H1": "S",
           "D1": "Default", "I1": "shared"}
NEGATIVES = ["reducer-to-legacy", "reducer-from-legacy", "set-to-legacy",
             "set-from-legacy", "fragment-to-legacy", "fragment-from-legacy",
             "congset-to-legacy", "provider-from-legacy"]


def expected_rows():
    with (MIGRATION / "apis.tsv").open() as stream:
        old = list(csv.DictReader(stream, delimiter="\t"))
    rows = []
    for row in old:
        group, api = row["group"], row["old_api"]
        module, name = api.split(".", 1)
        replacement = MODULES.get(module, module) + "." + name
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
        elif group == "B1" or group == "C2":
            domain = ("parallel ordinary and extension APIs; "
                      "no ordinary migration")
        if name == "legacy_traversedata_for_ss":
            replacement = "REMOVED; use simpExtLib.traversedata_for_ss"
        if api == "congLib.CONGRUENCE_EQ_SIMP_RULE":
            replacement = "congExtLib.CONGRUENCE_SIMP_RULE"
        rows.append(dict(zip(FIELDS, [group, api, replacement, domain,
            BOUNDARIES[group], witness, row["owners"] + ";27"])))
    return rows


def table_text(rows):
    stream = io.StringIO()
    writer = csv.DictWriter(stream, FIELDS, delimiter="\t",
                            lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue()


def validate_table(text):
    rows = list(csv.DictReader(io.StringIO(text), delimiter="\t"))
    expected = expected_rows()
    if rows != expected:
        raise ValueError("missing/stale final API decision; "
                         "do not drop a consumer")
    api = (HERE / "Task08API.sml").read_text()
    blocks = dict(re.findall(
        r"  structure (\w+) :\s*\n  sig\n(.*?)\n  end", api, re.S))
    blocks["T"] = (HERE / "Task08TraverseExt.sml").read_text() + (
        HERE / "Task08ReducerTypes.sml").read_text()
    def exports(text, name):
        return re.search(r"\b(?:val|type|datatype)\s+" + re.escape(name) +
                         r"\b|(?:=|\|)\s*" + re.escape(name) + r"\b", text)
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
        "SimpTracking": 12, "Cond_rewrExt": 12,
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


def execute(negative_controls):
    command = [str(ROOT / "bin/Holmake"),
               "--holstate=" + str(ROOT / "bin/hol.state0"),
               "--no-project", "--no-cache", "-C", str(HERE), "-j1", "check"]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    validate_output(result.returncode, output)
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
                    capture_output=True, text=True)
                text = control.stdout + control.stderr
                if control.returncode == 0 or "TASK08_COMPLETE" in text:
                    raise ValueError(
                        "negative control falsely passed: " + kind)
                receipts.append({"control": kind, "exit": control.returncode})
    return receipts, output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-table", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--negative-controls", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.write_table:
        TABLE.write_text(table_text(expected_rows()))
    rows = validate_table(TABLE.read_text())
    order = validate_graph(json.loads((HERE / "graph.json").read_text()))
    result = {"api_decisions": rows, "topological_order": order,
              "cutovers_checked": list(range(9, 17))}
    if args.run:
        result["commands"], output = execute(args.negative_controls)
        if args.output:
            args.output.mkdir(parents=True, exist_ok=True)
            (args.output / "interfaces.log").write_text(output)
        result["log_sha256"] = hashlib.sha256(output.encode()).hexdigest()
    paths = sorted([p for p in HERE.rglob("*")
                    if p.is_file() and ".hol" not in p.parts and
                    p.suffix in {".sml", ".ML", ".md", ".py", ".json"}]
                   + [HERE / "Holmakefile", TABLE])
    result["source_sha256"] = {str(p.relative_to(ROOT)):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    if args.output:
        (args.output / "design-check.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
