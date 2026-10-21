#!/usr/bin/env python3
"""Reproduce TASK_07's lexical API cross-reference and signature coverage.

This is deliberately not an SML resolver. Qualified and open/bare references,
comments, declarations and homonyms are retained so an inventory cannot silently
miss a caller. CONSUMERS.md classifies the actual consumers and construction
obligations; the category column distinguishes frozen inputs and homonyms.
No builds, imports, worktree creation or writes to the external checkout occur.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = "cccaa27d7099cbadc886983020cbe745db7793f3"
SOURCE = "50cfa5d709a306298991b113c7ac63e426f8aabd"

# group, module, kind, whitespace-separated exports. See MIGRATION.md for
# construction, replacement type, invariants and final responsibility.
GROUPS = [
    ("T1", "Traverse", "type", "reducer_config_data simp_prover_ctxt ssolver "
     "subgoaler traverse_config xtraverse_data child_first_policy"),
    ("T1", "Traverse", "constructor", "CONTEXT_REDUCER CONFIG_REDUCER"),
    ("T1", "Traverse", "datatype", "traversal_policy"),
    ("T1", "Traverse", "constructor", "ParentFirst ChildFirst"),
    ("T1", "Traverse", "val", "reducer_data reducer_config_data default_config "
     "XTRAVERSE charge_only keep_abstraction NORMALIZE_ARGUMENTS "
     "TRAVERSE_WITH_CONTEXT CHILD_FIRST_WITH_OBSERVER ROOT_REWRITE "
     "ROOT_REWRITE_WITH_CONTEXT"),
    ("R1", "Cond_rewr", "val", "is_var_perm COND_REWR_CONVS "
     "COND_REWR_CONV_WITH_CONTEXT COND_REWR_CONV_WITH_CONFIG"),
    ("C1", "Opening", "val", "THREADED_CONGPROC"),
    ("C1", "Travrules", "val", "mk_threaded_travrules"),
    ("I1", "ThmAttribute", "val", "attribute_fns_of attribute_fns"),
    ("M1", "simpLib", "val", "Split ExclX"),
    ("C1", "simpLib", "val", "threaded_cong_ss"),
    ("S1", "simpLib", "val", "looper_ss solver_ss safe_solver_ss "
     "add_looper del_looper set_looper add_split del_split split_ss "
     "add_unsafe_solver add_safe_solver set_unsafe_solvers set_safe_solvers "
     "remove_solver set_subgoaler set_cond_depth set_term_ord mk_tactic_solver "
     "clear_rules"),
    ("V1", "simpLib", "type", "rewrite_source rewrite_bundle"),
    ("V1", "simpLib", "val", "rewrite_sources rewrite_source_handles "
     "prepare_rewrite_arguments source_rewrite same_rewrite_source "
     "rewrite_source_compare rewrite_views prepare_rewrite_bundle "
     "combine_rewrite_bundles rewrite_bundle_rules install_rewrite_bundle "
     "suspend_rewrite_sources rewrite_context_changes"),
    ("E1", "simpLib", "val", "remove_ssfrags_preserving_controls "
     "filter_rewrites filter_rewrites_preserving_controls"),
    ("P1", "simpLib", "val", "legacy_traversedata_for_ss "
     "traverseconfig_for_ss xtraversedata_for_ss"),
    ("A1", "simpLib", "type", "simp_mode xsimptac_config"),
    ("A1", "simpLib", "val", "GEN_SIMP_TAC GEN_SIMP_TAC_CHILD_FIRST "
     "GEN_GLOBAL_SIMP_TAC GEN_GLOBAL_SIMP_TAC_CHILD_FIRST "
     "GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND"),
    ("H1", "simpLib", "val", "SIMP_CONV_CHILD_FIRST prepare_child_first "
     "prepare_child_first_observed"),
    ("I1", "SplitData", "datatype", "raw_delta"),
    ("I1", "SplitData", "constructor", "Add Remove"),
    ("I1", "SplitData", "val", "initialize exclude named_rules theory_data "
     "current_data"),
    ("M1", "simpMarkerLib", "datatype", "directive"),
    ("M1", "simpMarkerLib", "constructor", "Legacy DSplit DExclX"),
    ("M1", "simpMarkerLib", "val", "Split_tm Split destSplit ExclX destExclX "
     "dest_directive is_directive strip_wrappers process_taclist_then_recur"),
    ("I1", "splitLib", "type", "split_rule"),
    ("I1", "splitLib", "val", "SPLIT_CONV SPLIT_ASM_TAC SPLIT_TAC "
     "mk_asm_split split_forms SPLIT_RULE_TAC type_split_of type_asm_split_of "
     "type_split_rules goal_split_rule_groups goal_split_rules "
     "enable_split_attribute exclude_split split_thms named_split_thms "
     "is_asm_split split_thm_name"),
    # Baseline exports whose mixed implementation/domain or construction
    # obligations must not disappear from the migration table.
    ("B1", "simpLib", "existing", "dproc_ss weakener_data SSFRAG "
     "traversedata_for_ss empty_ss empty_ssfrag rewrites rewrites_with_names "
     "named_rewrites named_rewrites_with_names merge_ss named_merge_ss "
     "name_ss mk_simpset register_frag lookup_named_frag all_named_frags "
     "SF ssfrags_of ssf_upd_rewrs type_ssfrag tyi_to_ssdata ac_ss conv_ss "
     "relsimp_ss add_weakener add_relsimp"),
    ("C2", "congLib", "existing", "CSFRAG CONGRUENCE_SIMP_QCONV "
     "CONGRUENCE_SIMP_CONV CONGRUENCE_EQ_SIMP_CONV CONGRUENCE_EQ_SIMP_RULE"),
]
# Producer-output and mixed-helper closure: ordinary-looking uses of these
# results also cross the type boundary. These are external APIs/helpers, not
# additional signature deltas on the simplifier branch.
PRODUCERS = {
    "clasimpLib": "clasimp_ss derive_clasimp_ss derive_simpset "
    "working_original working_full_simpset working_decision_base "
    "working_plain_decision_base install_supplied_rules install_supplied_views "
    "add_supplied_views supplied_converse_working bound_simplification_simpset "
    "extend_invocation normalised_subject_fragment bottom_up_fragment "
    "clasimp_bu_head_ss clasimp_bu_reduce lhs_view_table working_simpset "
    "asm_full_simp",
    "aesopData": "aesop_ss cached_simpset",
    "aesopRule": "simp_rule_with",
    "iffTestSupport": "rewrite_changes has_iff_rewrite rewrites_to "
    "iff_fragment_count",
    "orderLib": "ORDER_ss ORDER_ss_budgeted",
    "linarithLib": "LINARITH_ss LINARITH_ss_budgeted linarith_solver "
    "linarith_solver_budgeted",
    "seedCollections": "algebra_ss field_ss",
    "benchLib": "clean_simpset translation_frag simp_controls",
}
OWNERS = {
    "T1": "09,10,11,22", "R1": "12,14", "C1": "10,13,14",
    "C2": "08,11,13", "I1": "23,27", "M1": "18,20,23",
    "S1": "10,20,24", "V1": "14,19,21", "E1": "17,19,21",
    "P1": "08,10,11,14,16", "A1": "10,18,20", "H1": "10,22",
    "B1": "10,14,15,16,24", "D1": "25",
}
REPLACEMENTS = {
    "Traverse": "TraverseExt", "Cond_rewr": "Cond_rewrExt",
    "Opening": "OpeningExt", "Travrules": "TravrulesExt",
    "simpLib": "simpExtLib", "congLib": "congExtLib",
    "ThmAttribute": "ThmAttribute", "SplitData": "SplitData",
    "splitLib": "splitLib", "simpMarkerLib": "simpMarkerLib",
    **{m: m for m in PRODUCERS},
}
SIGS = {m: ("src/1/" if m == "ThmAttribute" else "src/simp/src/")
        + m + ".sig" for _, m, _, _ in GROUPS}


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def digest(data):
    return hashlib.sha256(data).hexdigest()


def uncomment(text):
    # Nested ML comments, including strings inside comments, are irrelevant
    # to declaration names. Do not mistake declaration examples for exports.
    depth, out, i = 0, [], 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "(*":
            depth += 1
            i += 2
        elif pair == "*)" and depth:
            depth -= 1
            i += 2
        else:
            out.append(" " if depth else text[i])
            i += 1
    return "".join(out)


def declarations(text):
    text = uncomment(text)
    result = set()
    for kind, name in re.findall(
            r"\b(val|type|datatype)\s+([A-Za-z][A-Za-z0-9_']*)", text):
        result.add((kind, name))
    # Constructor scan is restricted to the three signatures with datatypes.
    for block in re.findall(r"\bdatatype\s+.*?(?=\n\s*(?:val|type|datatype)"
                            r"\b|\nend\b|\Z)", text, re.S):
        for name in re.findall(r"(?:=|\|)\s*([A-Z][A-Za-z0-9_']*)", block):
            result.add(("constructor", name))
    return result


def catalog():
    rows = []
    for group, module, kind, names in GROUPS:
        for name in names.split():
            rows.append((group, module, kind, name))
    for module, names in PRODUCERS.items():
        rows.extend(("D1", module, "external-output", n) for n in names.split())
    return sorted(rows)


def validate_signatures(rows):
    differences = {}
    for module, path in sorted(SIGS.items()):
        current = (ROOT / path).read_bytes()
        old = subprocess.run(["git", "-C", str(ROOT), "show",
                              f"{BASE}:{path}"], capture_output=True)
        before = declarations(old.stdout.decode()) if old.returncode == 0 else set()
        after = declarations(current.decode())
        expected = {(k, n) for _, m, k, n in rows
                    if m == module and k != "existing"}
        actual = after - before
        if actual != expected or before - after:
            raise ValueError(f"{path}: uncatalogued signature delta "
                             f"missing={actual - expected}, "
                             f"extra={expected - actual}, "
                             f"removed={before - after}")
        differences[module] = {
            "path": path, "sha256": digest(current),
            "baseline_exists": old.returncode == 0,
            "added": [list(x) for x in sorted(actual)],
        }
    # Whole-tree guard: any other changed/new production signature must be
    # explicitly classified, not silently excluded from API coverage.
    changed = git(ROOT, "diff", "--name-only", BASE, "--", "*.sig")
    unclassified = set(changed.decode().splitlines()) - set(SIGS.values())
    unclassified = {p for p in unclassified
                    if not p.startswith("src/simp/tests/compatibility/inputs/")}
    if unclassified:
        raise ValueError(f"Unclassified changed signatures: {unclassified}")
    return differences


def category(scope, path, module):
    if scope == "external":
        if path.startswith("src/auto/"):
            return "external-consumer", "25"
        if path.startswith("src/basicProof/"):
            return "external-construction-provider", "24,25"
        if path.startswith("src/simp/"):
            return "external-provider-or-tests", "25"
        if path.startswith("help/"):
            return "external-documentation", "25,27"
        return "lexical-homonym-or-ordinary", "25,27"
    if path.startswith("help/") or path == "src/simp/src/notes.md":
        return "documentation", "27"
    if path == "src/1/selftest.sml" and module == "ThmAttribute":
        return "attribute-identity-test-keep", "23,27"
    if "/compatibility/inputs/" in path or "/compatibility/public/" in path:
        return "frozen-reference-do-not-migrate", "26,27"
    if path.startswith("src/simp/tests/compatibility/"):
        return "contract-harness-or-ledger", "26,27"
    if path.startswith("src/simp/tests/"):
        return "focused-test", "23,24,26"
    if path == "src/simp/src/selftest.sml":
        return "native-test", "24,26"
    if path.startswith("src/simp/src/") or path.startswith("src/1/ThmAttribute"):
        return "provider-or-internal-consumer", ""  # API-family owner
    if path.startswith("src/basicProof/"):
        return "ordinary-construction-provider", "24,27"
    return "lexical-homonym-or-ordinary", "24,27"


def scan(root, scope, rows):
    symbols = sorted({n for _, _, _, n in rows})
    pattern = re.compile(r"(?<![A-Za-z0-9_'])((?:" +
                         "|".join(map(re.escape, symbols)) +
                         r"))(?![A-Za-z0-9_'])")
    by_name = {}
    for group, module, _, name in rows:
        by_name.setdefault(name, set()).add((group, module))
    references, matched, all_inputs = [], {}, []
    for path in sorted(git(root, "ls-files", "-z").decode().split("\0")):
        if not path or path.startswith("src/simp/tests/compatibility/migration/"):
            continue
        if path.endswith("TASK_07_HANDOFF.md") or "/evidence/" in path:
            continue
        p = Path(path)
        if p.suffix not in {".sml", ".sig", ".ML", ".smd", ".md", ".py"} \
                and p.name != "Holmakefile":
            continue
        full = root / path
        if not full.is_file():
            continue
        data = full.read_bytes()
        all_inputs.append((path, digest(data)))
        text = data.decode("utf-8", errors="replace")
        for number, line in enumerate(text.splitlines(), 1):
            for name in sorted(set(pattern.findall(line))):
                for group, module in sorted(by_name[name]):
                    if group == "D1" and scope != "external":
                        continue
                    cat, owner = category(scope, path, module)
                    # Very common constructors are only meaningful in their
                    # owning area or with explicit qualification.
                    if name in {"Add", "Remove", "Legacy", "directive"}:
                        if not path.startswith("src/simp/") and \
                                module + "." + name not in line:
                            continue
                    references.append([scope, path, str(number), group,
                                       module + "." + name, cat,
                                       owner or OWNERS[group]])
                    matched[path] = digest(data)
    return references, matched, digest(json.dumps(all_inputs).encode()), len(all_inputs)


def external_provenance(root):
    status = git(root, "status", "--porcelain=v2", "--branch",
                 "--untracked-files=all")
    result = {
        "path": str(root.resolve()), "head": git(root, "rev-parse", "HEAD").decode().strip(),
        "branch": git(root, "branch", "--show-current").decode().strip(),
        "status": status.decode(), "status_sha256": digest(status),
        "unstaged_diff_bytes": len(git(root, "diff", "--binary")),
        "staged_diff_bytes": len(git(root, "diff", "--cached", "--binary")),
    }
    nested = root / ".agent-files"
    if (nested / ".git").exists():
        ns = git(nested, "status", "--porcelain=v1", "--untracked-files=all")
        result["ignored_agent_files"] = {
            "head": git(nested, "rev-parse", "HEAD").decode().strip(),
            "status_sha256": digest(ns),
            "untracked_count": sum(l.startswith(b"?? ") for l in ns.splitlines()),
            "tracked_changes": [l.decode() for l in ns.splitlines()
                                if not l.startswith(b"?? ")],
        }
    return result


def validate_marker_consumers(external, document=None):
    """Require actual migration entries for external classifier consumers.

    Lexical references alone did not close this boundary in the first receipt.
    Each table row must state replacement, construction, assertions and owner;
    every direct classifier use must have a source-bound row, including the
    generic-only uses that deliberately retain their constructor identities.
    """
    if document is None:
        document = (HERE / "EXTERNAL_MARKERS.md").read_text()
    entries, covered = {}, set()
    for line in document.splitlines():
        if not line.startswith("| MC"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) != 7 or any(not c for c in cells):
            raise ValueError("Incomplete marker migration entry")
        key, anchor, old, replacement, construction, assertions, owner = cells
        match = re.fullmatch(r"`(src/auto/[^:]+\.sml):(\d+)–(\d+)`", anchor)
        if not match or key in entries or owner != "TASK_25":
            raise ValueError(f"Invalid marker migration entry: {key}")
        path, start, end = match.groups()
        start, end = int(start), int(end)
        lines = (external / path).read_text().splitlines()
        if not 1 <= start <= end <= len(lines):
            raise ValueError(f"Invalid marker source range: {anchor}")
        entries[key] = cells
        covered.update((path, n) for n in range(start, end + 1))
    if not entries:
        raise ValueError("Missing marker migration table")
    pattern = re.compile(r"markerLib\.(?:dest_directive|is_directive|"
                         r"strip_wrappers)\b|\bclassify_simp_args\b")
    uses = set()
    paths = git(external, "ls-files", "src/auto/*.sml").decode().splitlines()
    for path in paths:
        lines = (external / path).read_text().splitlines()
        for number, line in enumerate(lines, 1):
            if pattern.search(line):
                uses.add((path, number))
    missing = uses - covered
    if missing:
        raise ValueError(f"Unmapped marker classifier consumers: {sorted(missing)}")
    return {"entries": len(entries), "classifier_source_lines": len(uses)}


def run(external, write):
    rows = catalog()
    signatures = validate_signatures(rows)
    before = external_provenance(external)
    marker_consumers = validate_marker_consumers(external)
    refs, sources = [], {}
    scans = {}
    for scope, root in [("repository", ROOT), ("external", external)]:
        rr, hashes, aggregate, count = scan(root, scope, rows)
        refs.extend(rr)
        sources[scope] = hashes
        scans[scope] = {"scanned_files": count, "input_digest": aggregate,
                        "matched_files": len(hashes), "reference_rows": len(rr)}
    if external_provenance(external) != before:
        raise ValueError("External provenance changed during read-only inventory")
    api_header = "group\told_api\tkind\treplacement_api\towners\n"
    api_text = api_header + "".join(
        f"{g}\t{m}.{n}\t{k}\t{REPLACEMENTS[m]}.{n}\t{OWNERS[g]}\n"
        for g, m, k, n in rows)
    ref_header = "scope\tpath\tline\tgroup\tapi\tcategory\towners\n"
    ref_text = ref_header + "".join("\t".join(r) + "\n" for r in refs)
    manifest = {
        "schema": 1, "source_revision": SOURCE, "baseline_revision": BASE,
        "signature_deltas": signatures, "external": before,
        "scans": scans, "matched_source_sha256": sources,
        "api_rows": len(rows), "api_tsv_sha256": digest(api_text.encode()),
        "references_tsv_sha256": digest(ref_text.encode()),
        "scope": "lexical superset; actual consumers in CONSUMERS.md; no build claim",
    }
    files = {"apis.tsv": api_text, "references.tsv": ref_text,
             "manifest.json": json.dumps(manifest, indent=2, sort_keys=True) + "\n"}
    for name, text in files.items():
        path = HERE / name
        if write:
            path.write_text(text)
        elif not path.exists() or path.read_text() != text:
            raise ValueError(f"Stale inventory: {path}")
    print(json.dumps({"api_rows": len(rows), "scans": scans,
                      "external_head": before["head"],
                      "external_unchanged": True,
                      "marker_consumers": marker_consumers}, sort_keys=True))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external", type=Path,
                        default=ROOT.parent / "isabelle-tactics")
    parser.add_argument("--write", action="store_true",
                        help="explicitly regenerate reviewed inventory snapshot")
    args = parser.parse_args()
    try:
        run(args.external, args.write)
    except (ValueError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
