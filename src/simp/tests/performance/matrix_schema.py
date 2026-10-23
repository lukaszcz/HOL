#!/usr/bin/env python3
"""Fail-closed P09 machinery ledger, not performance acceptance evidence.

Public API: load_matrix(), validate_matrix(data), get_case(case, size) ->
fixture basename. All validate the frozen requirement/case/size contract and
live fixture inventories. report() distinguishes runnable cases/external
commands from real prerequisite blocks. Neither validation nor reporting
executes commands or certifies results. No cached ledger can mask deletions.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import shlex
import sys

HERE = Path(__file__).resolve().parent
BASELINE = "cccaa27d7099cbadc886983020cbe745db7793f3"
SIZE_SETS = {
    "rules": [0, 1, 10, 100, 1000, 10000],
    "depth": [0, 1, 10, 100],
    "assumptions": [0, 1, 10, 100, 1000, 10000],
    "numeral": [1, 10, 100, 1000, 10000],
    "singleton": [0],
}
PROTOCOL = {
    "selector": "PERF_CASE", "size": "PERF_SIZE", "labels": ["$PERF_CASE"],
    "consumed_per_iteration": 1, "storage": False,
    "outliers": "none removed", "minimum_acceptance_pairs": 10,
    "result_statuses": ["pass", "fail", "inconclusive", "blocked"],
}
STAGES = ("construct", "reuse", "complete")
TACTIC_FAMILIES = (
    "supplied", "installed", "asm", "full", "reverse", "no_strip_full",
    "no_strip_reverse", "global", "req0", "reqd", "req0_reqd", "reqd_req0",
    "dependency_full", "dependency_reverse",
)
MATRIX_CASES = """
frag_create frag_named frag_named_rules frag_record frag_update frag_duplicate
frag_merge frag_named_merge frag_ac frag_ac_merge frag_typebase
frag_type_lookup
compile_batch compile_single compile_empty compile_excluded compile_conditional
compile_bounded compile_ac compile_maker compile_user compile_collector
compile_construct_conv compile_reuse compile_complete compile_supplied
exclude_empty exclude_missing exclude_matching exclude_batch exclude_qualified
exclude_partial exclude_literal_namespace exclude_literal_exact exclude_dproc
exclude_mixed exclude_marker exclude_marker_reuse exclude_tactic_construct
exclude_tactic_reuse exclude_tactic_complete exclude_replay history_remove
history_force history_excluded history_bounded history_limit history_collectors
history_makers history_theory_change storage_graph
""".split()
ATOMIC_CASES = """
traversal_construct traversal_context_construct traversal_complete
traversal_reuse_hit traversal_reuse_miss traversal_weakening downstream_boss
""".split()
DEPTH_CASES = """
traversal_deep traversal_congruence traversal_side_conditions
traversal_failed_candidates traversal_saved
""".split()
EXPECTED_CASES = {
    name: {"fixture": "MatrixPerformance.sml", "sizes": "rules"}
    for name in MATRIX_CASES
}
for grid, names in (
        ("singleton", ATOMIC_CASES), ("depth", DEPTH_CASES),
        ("numeral", ["downstream_arithmetic", "downstream_reduce"]),
        ("assumptions", ["tactic_" + family + "_" + stage
                         for family in TACTIC_FAMILIES for stage in STAGES])):
    EXPECTED_CASES.update({
        name: {"fixture": "ClientPerformance.sml", "sizes": grid}
        for name in names
    })

# Frozen independently of matrix.json: deleting a ledger row must fail, even
# if its cases are shared with another row. Changes require schema review.
_CASE_REQUIREMENTS = """
fragments.empty_and_sizes frag_create
fragments.named_anonymous frag_named frag_named_rules frag_record
fragments.creation frag_create frag_named
fragments.update frag_update
fragments.duplicates frag_duplicate
fragments.merge frag_merge frag_named_merge
fragments.ac frag_ac frag_ac_merge
fragments.typebase frag_typebase frag_type_lookup
compilation.small_large_batches compile_batch
compilation.repeated_single_additions compile_single
compilation.empty_additions compile_empty
compilation.excluded_additions compile_excluded
compilation.conditional compile_conditional
compilation.bounds compile_bounded
compilation.ac compile_ac
compilation.custom_makers compile_maker
compilation.user_conversions compile_user
compilation.stages compile_construct_conv compile_reuse compile_complete \
compile_supplied
exclusions.missing exclude_missing
exclusions.matching exclude_matching exclude_partial
exclusions.batched exclude_batch exclude_empty
exclusions.qualified exclude_qualified
exclusions.literal_namespace_names exclude_literal_namespace \
exclude_literal_exact
exclusions.dprocs exclude_dproc exclude_mixed
exclusions.marker_routes exclude_marker exclude_marker_reuse \
exclude_tactic_construct exclude_tactic_reuse exclude_tactic_complete
exclusions.replay exclude_replay
history.fragment_removal history_remove
history.forced_addition history_force history_excluded
history.exclusions_theory_changes history_theory_change
history.bounded_rules history_bounded
history.limits history_limit
history.custom_collectors history_collectors compile_collector history_makers
traversal.construction traversal_construct traversal_context_construct \
traversal_complete
traversal.reuse traversal_reuse_hit
traversal.lookup_hit_miss traversal_reuse_hit traversal_reuse_miss
traversal.deep_terms traversal_deep
traversal.congruences traversal_congruence
traversal.weakening traversal_weakening
traversal.repeated_side_conditions traversal_side_conditions
traversal.failed_candidates traversal_failed_candidates
traversal.saved_conversions traversal_saved
storage.gc_time storage_graph
storage.gc_counts storage_graph
storage.retained_graph_and_slope storage_graph
downstream.arithmetic downstream_arithmetic
downstream.reduce downstream_reduce
downstream.boss_basic downstream_boss
"""
REQUIRED_COVERAGE = {
    row[0]: tuple(row[1:]) for line in _CASE_REQUIREMENTS.splitlines()
    if (row := line.split())
}
for requirement, families in {
        "tactics.supplied_installed": ("supplied", "installed"),
        "tactics.assumption_counts": ("asm",),
        "tactics.global_fixpoints": ("global",),
        "tactics.full_reverse_passes": (
            "full", "reverse", "no_strip_full", "no_strip_reverse",
            "dependency_full", "dependency_reverse"),
        "tactics.requirements": ("req0", "reqd", "req0_reqd", "reqd_req0"),
}.items():
    REQUIRED_COVERAGE[requirement] = tuple(
        "tactic_" + family + "_" + stage
        for family in families for stage in STAGES)
REQUIRED_COVERAGE["tactics.saved_reuse_and_validation"] = tuple(
    "tactic_" + family + "_reuse"
    for family in ("supplied", "installed", "full", "reverse", "global",
                   "reqd"))
REQUIRED_BLOCKERS = {
    "storage.allocation": "allocation_prerequisite",
    "storage.release_discarded_simpsets": "lifetime_prerequisite",
    "storage.temporary_peaks_rss": "rss_prerequisite",
    "downstream.integer": "integer_prerequisite",
    "downstream.real": "real_prerequisite",
    "downstream.routine_build": "independent_routine_prerequisite",
    "downstream.full_regression": "independent_full_prerequisite",
}
REQUIRED_EXTERNALS = {
    "loading.startup_time": "loading_timing",
    "loading.fresh_simpLib": "loading_audit",
    "loading.fresh_congLib": "loading_audit",
    "loading.dependency_list": "loading_audit",
    "loading.initialization_callbacks": "loading_audit",
    "loading.extension_absence": "loading_audit",
    "downstream.migrated_extension_consumer": "extension_consumer",
    "protocol.independent_build_mode": "independent_build_mode",
    "protocol.extensions_enabled": "extension_suite",
}
REQUIRED_REQUIREMENTS = frozenset(
    REQUIRED_COVERAGE.keys() | REQUIRED_BLOCKERS.keys() |
    REQUIRED_EXTERNALS.keys())

# These mandatory executable routes keep enabled extension/loading checks
# from quietly becoming echo commands, dry runs, or receipt-only blockers.
EXTERNAL_COMMANDS = {
    "loading_timing": [
        "python3 src/simp/tests/performance/loading.py --baseline " + BASELINE +
        " --candidate CANDIDATE --module simpLib --pairs 10 --api-audit API_AUDIT_RECEIPT "
        "--authorize-measurements --output FRESH_SIMP_LOADING",
        "python3 src/simp/tests/performance/loading.py --baseline " + BASELINE +
        " --candidate CANDIDATE --module congLib --pairs 10 --api-audit API_AUDIT_RECEIPT "
        "--authorize-measurements --output FRESH_CONG_LOADING"],
    "loading_audit": [
        "sh src/simp/tests/compatibility/evidence/task26/root-wrapper.sh "
        "bin/Holmake -C src/simp/tests/api-audit check"],
    "extension_consumer": [
        "python3 src/simp/tests/compatibility/run_task25_consumer.py "
        "--consumer-patch "
        "src/simp/tests/compatibility/evidence/task25/consumer.patch "
        "--simplifier-revision CANDIDATE --output FRESH_CONSUMER_OUTPUT"],
    "independent_build_mode": [
        "python3 src/simp/tests/performance/acceptance.py verify-builds "
        "BUILD_MANIFEST --candidate CANDIDATE"],
    "extension_suite": [
        "bin/Holmake --holstate=$PWD/bin/hol.state0 -C src/simp/src "
        "-j1 HOLSELFTESTLEVEL=1 all",
        "bin/Holmake --holstate=$PWD/bin/hol.state0 "
        "-C src/simp/tests/native-extension -j1 check-full",
        "bin/build -t --seq=tools/sequences/upto-parallel",
        "bin/build -t -F"],
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def exact_keys(value, keys, where):
    require(type(value) is dict, where + ": expected object")
    missing, extra = set(keys) - value.keys(), value.keys() - set(keys)
    require(not missing and not extra,
            f"{where}: missing={sorted(missing)} extra={sorted(extra)}")


def unique_list(value, where):
    require(type(value) is list and value, where + ": expected nonempty list")
    require(all(type(x) is str and x.strip() for x in value),
            where + ": expected nonempty strings")
    require(len(value) == len(set(value)), where + ": duplicate entries")


def _object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def _no_constant(value):
    raise ValueError("nonfinite JSON constant: " + value)


def _uncomment_sml(text):
    """Remove nested SML comments without accepting inventories in comments."""
    out, depth, quoted, i = [], 0, False, 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == "(*":
                depth += 1
                i += 2
            elif pair == "*)":
                depth -= 1
                i += 2
                out.append(" ")
            else:
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\":
                i += 1
                require(i < len(text), "truncated SML string")
                out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif pair == "(*":
            depth = 1
            i += 2
            out.append(" ")
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    require(not depth and not quoted, "unterminated SML comment/string")
    return "".join(out)


def _strings(text, where):
    require(re.fullmatch(r'\s*"[a-zA-Z0-9_]+"'
                         r'(?:\s*,\s*"[a-zA-Z0-9_]+")*\s*', text),
            where + ": unsupported string inventory syntax")
    result = re.findall(r'"([a-zA-Z0-9_]+)"', text)
    unique_list(result, where)
    return result


def _one(pattern, text, where):
    matches = re.findall(pattern, text, re.DOTALL)
    require(len(matches) == 1, where + ": missing/ambiguous source inventory")
    return matches[0]


def validate_sources(cases, fixture_dir=HERE):
    """Check actual SML case inventories/dispatch; never infer from JSON."""
    fixture_dir = Path(fixture_dir)

    def source(name):
        path = fixture_dir / name
        require(path.is_file(), "missing fixture/source: " + str(path))
        return _uncomment_sml(path.read_text())

    entry = source("MatrixPerformance.sml")
    for pattern in (r"\bopen\b[^\n]*\bMatrixSupport\b",
                    r"\bworkload\s+label\s+size\b",
                    r"\bLib\.mem\s+label\s+cases\b",
                    r"\bLib\.mem\s+size\s+sizes\b"):
        require(re.search(pattern, entry) is not None,
                "MatrixPerformance missing support/selection dispatch")
    support = source("MatrixSupport.sml")
    inventory = _strings(_one(r"\bval\s+cases\s*=\s*\[(.*?)\]",
                              support, "MatrixSupport.cases"),
                         "MatrixSupport.cases")
    expected_matrix = {name for name, row in cases.items()
                       if row["fixture"] == "MatrixPerformance.sml"}
    require(set(inventory) == expected_matrix,
            "MatrixSupport.cases does not match ledger")
    dispatch = re.findall(
        r'"((?:frag|compile|exclude|history|storage)_[a-z0-9_]+)"\s*=>',
        support)
    dispatch += re.findall(r'\blabel\s*=\s*"(storage_[a-z0-9_]+)"\s+then',
                           support)
    require(Counter(dispatch) == Counter(inventory),
            "MatrixSupport dispatch does not match case inventory")
    sizes = _one(r"\bval\s+sizes\s*=\s*\[(.*?)\]", support,
                 "MatrixSupport.sizes")
    require(re.fullmatch(r"\s*\d+(?:\s*,\s*\d+)*\s*", sizes) is not None,
            "unsupported MatrixSupport.sizes syntax")
    require([int(x) for x in sizes.split(",")] == SIZE_SETS["rules"],
            "MatrixSupport.sizes does not match frozen rules grid")

    client = source("ClientPerformance.sml")
    atomic = re.findall(r'"((?:traversal|downstream)_[a-z0-9_]+)"\s*=>',
                        client)
    choices = _one(r"\bval\s+choices\s*=(.*?)\bval\s+\(oper,stage\)",
                   client, "client tactic choices")
    lists = re.findall(r"\[([^\[\]]*)\]", choices)
    require(len(lists) == 2, "unsupported client tactic product syntax")
    stages, families = (_strings(text, "client tactic product")
                        for text in lists)
    require(tuple(stages) == STAGES,
            "client construction/reuse/complete stages")
    require(set(x.lower() for x in families) == set(TACTIC_FAMILIES),
            "client tactic family inventory mismatch")
    generated = ["tactic_" + family.lower() + "_" + stage
                 for family in families for stage in stages]
    actual = atomic + generated
    require(len(actual) == len(set(actual)), "duplicate client source case")
    expected_client = {name for name, row in cases.items()
                       if row["fixture"] == "ClientPerformance.sml"}
    require(set(actual) == expected_client,
            "ClientPerformance source cases do not match ledger")


def _gate_records(records, ids, status, where):
    exact_keys(records, ids, where)
    for key, record in records.items():
        location = where + "." + key
        exact_keys(record, ("status", "gate_owner", "reason", "commands"),
                   location)
        require(record["status"] == status, location + ": wrong status")
        require(type(record["reason"]) is str and
                len(record["reason"].strip()) >= 40,
                location + ": missing substantive prerequisite/scope reason")
        owner = record["gate_owner"]
        require(type(owner) is str and re.fullmatch(
            r"TASK(?:0[1-9]|[12][0-9]|3[0-8])"
            r"(?:, TASK(?:0[1-9]|[12][0-9]|3[0-8]))*", owner),
            location + ": missing/invalid task gate owner")
        unique_list(record["commands"], location + ".commands")
        for command in record["commands"]:
            require(not any(c in command for c in "\r\n\x00"),
                    location + ": multiline/invalid command")
            try:
                words = shlex.split(command)
            except ValueError as error:
                raise ValueError(location + ": malformed command") from error
            require(words and words[0] in {
                "python3", "poly", "sh", "bin/Holmake", "bin/build",
                "BASELINE/bin/Holmake", "CANDIDATE/bin/Holmake",
                "BASELINE/bin/build", "CANDIDATE/bin/build", "/usr/bin/time"},
                location + ": not a prerequisite command")


def validate_matrix(data, *, fixture_dir=HERE):
    """Validate a decoded ledger; ValueError means unusable, never complete."""
    exact_keys(data, ("schema", "scope", "baseline", "protocol", "size_sets",
                      "cases", "requirements", "blockers", "externals"),
               "matrix")
    require(type(data["schema"]) is int and data["schema"] == 1,
            "unsupported matrix schema")
    require(data["scope"] ==
            "TASK28 machinery readiness; not P09 performance acceptance",
            "wrong matrix scope")
    require(data["baseline"] == BASELINE, "wrong baseline")
    # JSON's bool/int equality must not admit true as consumption/pair count.
    require(json.dumps(data["protocol"], sort_keys=True) ==
            json.dumps(PROTOCOL, sort_keys=True), "wrong frozen protocol")
    exact_keys(data["size_sets"], SIZE_SETS, "size_sets")
    for key, grid in data["size_sets"].items():
        require(type(grid) is list and all(type(n) is int for n in grid) and
                grid == SIZE_SETS[key], "invalid frozen size grid: " + key)
    cases = data["cases"]
    exact_keys(cases, EXPECTED_CASES, "cases")
    for name, case in cases.items():
        exact_keys(case, ("fixture", "sizes"), "case " + name)
        require(case == EXPECTED_CASES[name],
                "wrong fixture/size binding: " + name)
    requirements = data["requirements"]
    exact_keys(requirements, REQUIRED_REQUIREMENTS, "requirements")
    referenced = set()
    for key, coverage in REQUIRED_COVERAGE.items():
        row = requirements[key]
        exact_keys(row, ("cases",), "requirement " + key)
        unique_list(row["cases"], "requirement " + key)
        require(set(row["cases"]) == set(coverage),
                "incomplete/unknown case or stage coverage: " + key)
        referenced.update(row["cases"])
    require(referenced == set(cases), "unreferenced cases")
    for mode, expected in (("blocker", REQUIRED_BLOCKERS),
                           ("external", REQUIRED_EXTERNALS)):
        for key, target in expected.items():
            exact_keys(requirements[key], (mode,), "requirement " + key)
            require(requirements[key][mode] == target,
                    "wrong " + mode + " reference: " + key)
    _gate_records(data["blockers"], set(REQUIRED_BLOCKERS.values()),
                  "blocked", "blockers")
    _gate_records(data["externals"], set(REQUIRED_EXTERNALS.values()),
                  "runnable_external", "externals")
    for key, commands in EXTERNAL_COMMANDS.items():
        require(data["externals"][key]["commands"] == commands,
                "missing/disabled external commands: " + key)
    validate_sources(cases, fixture_dir)
    return data


def load_matrix(path=None, *, fixture_dir=None):
    """Read strict JSON and validate it against the live fixture sources."""
    path = Path(path) if path is not None else HERE / "matrix.json"
    if fixture_dir is None:
        fixture_dir = path.parent
    try:
        data = json.loads(path.read_text(), object_pairs_hook=_object,
                          parse_constant=_no_constant)
        return validate_matrix(data, fixture_dir=fixture_dir)
    except OSError as error:
        raise ValueError("cannot read matrix/source: " + str(error)) from error


def get_case(case, size, *, matrix=None, fixture_dir=HERE):
    """Return fixture basename after validating case AND its ledger size.

    Python int only: no bool, float, numeric string or coercion. Callers parse
    CLI integers first. Explicit matrix inputs are also fully revalidated.
    """
    data = (load_matrix() if matrix is None else
            validate_matrix(matrix, fixture_dir=fixture_dir))
    require(type(case) is str and case in data["cases"],
            "unknown matrix case: " + repr(case))
    row = data["cases"][case]
    require(type(size) is int and size in data["size_sets"][row["sizes"]],
            "invalid size for " + case + ": " + repr(size))
    return row["fixture"]


def report(matrix=None, *, fixture_dir=HERE):
    """JSON-ready completeness report. Runnable != executed, passed or ready
    for release. Prerequisite blocks remain visible even with valid schema.
    """
    data = (load_matrix() if matrix is None else
            validate_matrix(matrix, fixture_dir=fixture_dir))
    gates = {}
    for key, row in sorted(data["requirements"].items()):
        if "cases" in row:
            workloads = []
            for name in row["cases"]:
                case = data["cases"][name]
                workloads.append({
                    "case": name, "fixture": case["fixture"],
                    "sizes": data["size_sets"][case["sizes"]],
                    "command_template":
                        "python3 src/simp/tests/performance/acceptance.py run "
                        "--mode isolated --candidate CANDIDATE --case " +
                        name +
                        " --size SIZE --pairs 10 --samples 5 "
                        "--batch-seconds 0.2 --authorize-measurements "
                        "--output FRESH_OUTPUT",
                })
            gates[key] = {"status": "runnable_case", "workloads": workloads}
        else:
            mode = "external" if "external" in row else "blocker"
            record = data["externals" if mode == "external" else "blockers"][
                row[mode]]
            gates[key] = {
                **record, "reference": row[mode],
                "status": ("runnable_external" if mode == "external" else
                           "prerequisite_blocked"),
            }
    return {
        "schema_valid": True, "performance_acceptance": False,
        "scope": data["scope"], "case_count": len(data["cases"]),
        "requirement_count": len(gates),
        "counts": dict(Counter(row["status"] for row in gates.values())),
        "gates": gates,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, default=HERE / "matrix.json")
    parser.add_argument("--json", action="store_true", help="machine report")
    args = parser.parse_args(argv)
    try:
        result = report(load_matrix(args.matrix),
                        fixture_dir=args.matrix.parent)
    except (ValueError, TypeError) as error:
        print("INVALID MATRIX: " + str(error), file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"Valid ledger: {result['requirement_count']} requirements, "
              f"{result['case_count']} cases. Not performance acceptance.")
        for name, gate in result["gates"].items():
            print(name + ": " + gate["status"])
            if gate["status"] == "runnable_case":
                for row in gate["workloads"]:
                    print("  " + row["case"] + " [" + row["fixture"] +
                          "] sizes=" + ",".join(map(str, row["sizes"])))
                    print("  " + row["command_template"])
            else:
                print("  " + gate["gate_owner"] + ": " + gate["reason"])
                for command in gate["commands"]:
                    print("  " + command)
        print("Counts: " + json.dumps(result["counts"], sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
