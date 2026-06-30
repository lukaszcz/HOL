#!/usr/bin/env python3
"""Record Z3 proof outputs and raw proof-rule histograms for HolSmt."""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from typing import Iterable


SCHEMA = "holsmt-z3-proof-corpus-v1"
MATRIX_SCHEMA = "holsmt-z3-proof-corpus-matrix-v1"
RULE_CONTEXT_LIMIT = 3
ROOT = pathlib.Path(__file__).resolve().parents[3]
DEFAULT_SUPPORTED_VERSION_MANIFEST = (
    pathlib.Path(__file__).resolve().parent
    / "proof-corpus"
    / "supported_versions"
    / "manifest.json"
)
SUPPORTED_Z3_VERSIONS = ("2.19.1", "4.12.4", "4.13.0")

REPLAY_SUPPORTED_RULES = {
    "and-elim",
    "asserted",
    "commutativity",
    "def-axiom",
    "elim-unused",
    "hypothesis",
    "iff-false",
    "iff-true",
    "intro-def",
    "lemma",
    "monotonicity",
    "mp",
    "mp-eq",
    "mp_eq",
    "mp~",
    "nnf-neg",
    "nnf-pos",
    "not-or-elim",
    "quant-inst",
    "quant-intro",
    "refl",
    "rewrite",
    "sk",
    "skolem",
    "symm",
    "th-lemma-arith",
    "th-lemma-array",
    "th-lemma-basic",
    "th-lemma-bv",
    "th-lemma-datatype",
    "th-lemma-datatypes",
    "th-lemma-dt",
    "th-lemma-floating-point",
    "th-lemma-fp",
    "th-lemma-fpa",
    "th-lemma-nia",
    "th-lemma-nla",
    "th-lemma-nonlinear",
    "th-lemma-nonlinear-arith",
    "th-lemma-nra",
    "th-lemma-re",
    "th-lemma-regex",
    "th-lemma-regexp",
    "th-lemma-seq",
    "th-lemma-sequence",
    "th-lemma-sequences",
    "th-lemma-str",
    "th-lemma-string",
    "th-lemma-strings",
    "trans",
    "trans-star",
    "trans*",
    "true-axiom",
    "unit-resolution",
}

PARSE_ONLY_RULES = {
    # Z3 can wrap local proof terms in proof-bind annotations.  HolSmt's
    # parser treats the wrapper as transparent, so there is deliberately no
    # replay step for this rule.
    "proof-bind",
}

KNOWN_RULES = REPLAY_SUPPORTED_RULES | PARSE_ONLY_RULES

RULE_PREMISE_KIND = {
    "and-elim": "one",
    "asserted": "zero",
    "commutativity": "zero",
    "def-axiom": "zero",
    "elim-unused": "zero",
    "hypothesis": "zero",
    "iff-false": "one",
    "iff-true": "one",
    "intro-def": "zero",
    "lemma": "one",
    "monotonicity": "list",
    "mp": "two",
    "mp-eq": "two",
    "mp_eq": "two",
    "mp~": "two",
    "nnf-neg": "list",
    "nnf-pos": "list",
    "not-or-elim": "one",
    "proof-bind": "one",
    "quant-inst": "zero",
    "quant-intro": "one",
    "refl": "zero",
    "rewrite": "zero",
    "sk": "zero",
    "skolem": "zero",
    "symm": "one",
    "th-lemma-arith": "list",
    "th-lemma-array": "list",
    "th-lemma-basic": "list",
    "th-lemma-bv": "list",
    "th-lemma-datatype": "list",
    "th-lemma-datatypes": "list",
    "th-lemma-dt": "list",
    "th-lemma-floating-point": "list",
    "th-lemma-fp": "list",
    "th-lemma-fpa": "list",
    "th-lemma-nia": "list",
    "th-lemma-nla": "list",
    "th-lemma-nonlinear": "list",
    "th-lemma-nonlinear-arith": "list",
    "th-lemma-nra": "list",
    "th-lemma-re": "list",
    "th-lemma-regex": "list",
    "th-lemma-regexp": "list",
    "th-lemma-seq": "list",
    "th-lemma-sequence": "list",
    "th-lemma-sequences": "list",
    "th-lemma-str": "list",
    "th-lemma-string": "list",
    "th-lemma-strings": "list",
    "trans": "two",
    "trans-star": "list",
    "trans*": "list",
    "true-axiom": "zero",
    "unit-resolution": "list",
}
SOLVER_RESULTS = {"sat", "unsat", "unknown"}


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    start: int
    end: int


@dataclass(frozen=True)
class Atom:
    text: str
    start: int
    end: int


@dataclass(frozen=True)
class ListNode:
    items: list["Node"]
    start: int
    end: int


Node = Atom | ListNode


class SexpParseError(Exception):
    def __init__(self, message: str, offset: int):
        super().__init__(message)
        self.message = message
        self.offset = offset


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as infile:
        for chunk in iter(lambda: infile.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def json_dump(path: pathlib.Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as outfile:
        json.dump(value, outfile, indent=2, sort_keys=True)
        outfile.write("\n")


def write_text(path: pathlib.Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def tokenize(text: str) -> list[Token]:
    tokens: list[Token] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c == "(":
            tokens.append(Token("lparen", c, i, i + 1))
            i += 1
        elif c == ")":
            tokens.append(Token("rparen", c, i, i + 1))
            i += 1
        elif c == '"':
            start = i
            i += 1
            while i < n:
                if text[i] == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        i += 2
                    else:
                        i += 1
                        break
                else:
                    i += 1
            else:
                raise SexpParseError("unterminated SMT-LIB string", start)
            tokens.append(Token("atom", text[start:i], start, i))
        elif c == "|":
            start = i
            i += 1
            value = []
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    value.append(text[i + 1])
                    i += 2
                elif text[i] == "|":
                    i += 1
                    break
                else:
                    value.append(text[i])
                    i += 1
            else:
                raise SexpParseError("unterminated quoted symbol", start)
            tokens.append(Token("atom", "".join(value), start, i))
        else:
            start = i
            while i < n and not text[i].isspace() and text[i] not in "();":
                i += 1
            tokens.append(Token("atom", text[start:i], start, i))
    return tokens


def parse_sexps(text: str) -> list[Node]:
    tokens = tokenize(text)
    index = 0

    def parse_one() -> Node:
        nonlocal index
        if index >= len(tokens):
            raise SexpParseError("expected S-expression", len(text))
        token = tokens[index]
        index += 1
        if token.kind == "atom":
            return Atom(token.text, token.start, token.end)
        if token.kind == "rparen":
            raise SexpParseError("unexpected ')'", token.start)
        items: list[Node] = []
        while index < len(tokens) and tokens[index].kind != "rparen":
            items.append(parse_one())
        if index >= len(tokens):
            raise SexpParseError("missing ')'", token.start)
        end = tokens[index].end
        index += 1
        return ListNode(items, token.start, end)

    nodes = []
    while index < len(tokens):
        nodes.append(parse_one())
    return nodes


def line_col(text: str, offset: int) -> dict[str, int]:
    prefix = text[:offset]
    line = prefix.count("\n") + 1
    last_newline = prefix.rfind("\n")
    column = offset + 1 if last_newline < 0 else offset - last_newline
    return {"line": line, "column": column}


def context_for(text: str, start: int, end: int, radius: int = 96) -> str:
    left = max(0, start - radius)
    right = min(len(text), end + radius)
    context = text[left:right].replace("\n", "\\n")
    if left > 0:
        context = "..." + context
    if right < len(text):
        context += "..."
    return context


def atom_text(node: Node) -> str | None:
    return node.text if isinstance(node, Atom) else None


def normalize_rule_head(head: Node) -> str | None:
    if isinstance(head, Atom):
        return head.text
    if not isinstance(head, ListNode) or len(head.items) < 2:
        return None
    first = atom_text(head.items[0])
    base = atom_text(head.items[1])
    if first != "_" or base is None:
        return None
    if base == "th-lemma":
        theory = atom_text(head.items[2]) if len(head.items) >= 3 else None
        return f"th-lemma-{theory}" if theory else "th-lemma"
    if base == "rewrite":
        return "rewrite"
    return base


def malformed_item(text: str, message: str, start: int, end: int) -> dict[str, object]:
    loc = line_col(text, start)
    return {
        "message": message,
        "line": loc["line"],
        "column": loc["column"],
        "context": context_for(text, start, end),
    }


def extract_rule_report(proof_text: str) -> dict[str, object]:
    histogram: collections.Counter[str] = collections.Counter()
    rule_contexts: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    unknown_contexts: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    malformed: list[dict[str, object]] = []

    try:
        nodes = parse_sexps(proof_text)
    except SexpParseError as exc:
        malformed.append(
            malformed_item(
                proof_text,
                exc.message,
                exc.offset,
                min(len(proof_text), exc.offset + 1),
            )
        )
        return {
            "rule_histogram": {},
            "rule_contexts": {},
            "unknown_rules": [],
            "malformed_fragments": malformed,
        }

    def context_item(node: ListNode) -> dict[str, object]:
        loc = line_col(proof_text, node.start)
        return {
            "line": loc["line"],
            "column": loc["column"],
            "context": context_for(proof_text, node.start, node.end),
        }

    def record_rule_context(rule: str, node: ListNode) -> None:
        if len(rule_contexts[rule]) >= RULE_CONTEXT_LIMIT:
            return
        rule_contexts[rule].append(context_item(node))

    def record_unknown(rule: str, node: ListNode) -> None:
        if len(unknown_contexts[rule]) >= RULE_CONTEXT_LIMIT:
            return
        unknown_contexts[rule].append(context_item(node))

    def visit(node: Node, proof_expected: bool) -> None:
        if isinstance(node, Atom):
            return
        if not node.items:
            if proof_expected:
                malformed.append(
                    malformed_item(proof_text, "empty proof fragment", node.start, node.end)
                )
            return

        head_name = normalize_rule_head(node.items[0])

        if head_name == "proof":
            for child in node.items[1:]:
                visit(child, True)
            return

        if not proof_expected:
            for child in node.items:
                visit(child, False)
            return

        if head_name == "let":
            if len(node.items) < 3:
                malformed.append(
                    malformed_item(proof_text, "malformed proof let", node.start, node.end)
                )
                return
            bindings = node.items[1]
            if isinstance(bindings, ListNode):
                for binding in bindings.items:
                    if isinstance(binding, ListNode) and len(binding.items) == 2:
                        bound_name = atom_text(binding.items[0])
                        if bound_name is not None and bound_name.startswith("@x"):
                            visit(binding.items[1], True)
                    else:
                        malformed.append(
                            malformed_item(
                                proof_text,
                                "malformed proof let binding",
                                binding.start,
                                binding.end,
                            )
                        )
            else:
                malformed.append(
                    malformed_item(
                        proof_text,
                        "proof let bindings are not a list",
                        bindings.start,
                        bindings.end,
                    )
                )
            for body in node.items[2:]:
                visit(body, True)
            return

        if head_name == "!":
            if len(node.items) >= 2:
                visit(node.items[1], True)
            else:
                malformed.append(
                    malformed_item(proof_text, "malformed annotated proof", node.start, node.end)
                )
            return

        if head_name is None:
            malformed.append(
                malformed_item(proof_text, "proof rule head is not a symbol", node.start, node.end)
            )
            return

        histogram[head_name] += 1
        record_rule_context(head_name, node)
        if head_name not in KNOWN_RULES:
            record_unknown(head_name, node)

        premise_kind = RULE_PREMISE_KIND.get(head_name, "unknown")
        args = node.items[1:]
        if premise_kind == "zero":
            return
        if premise_kind == "one":
            if len(args) < 1:
                malformed.append(
                    malformed_item(
                        proof_text,
                        f"proof rule '{head_name}' is missing its premise",
                        node.start,
                        node.end,
                    )
                )
            else:
                visit(args[0], True)
        elif premise_kind == "two":
            if len(args) < 2:
                malformed.append(
                    malformed_item(
                        proof_text,
                        f"proof rule '{head_name}' is missing a premise",
                        node.start,
                        node.end,
                    )
                )
            for child in args[:2]:
                visit(child, True)
        elif premise_kind == "list":
            if len(args) < 1:
                malformed.append(
                    malformed_item(
                        proof_text,
                        f"proof rule '{head_name}' is missing a conclusion",
                        node.start,
                        node.end,
                    )
                )
            for child in args[:-1]:
                visit(child, True)
        else:
            for child in args[:-1]:
                visit(child, True)

    for node in nodes:
        visit(node, False)

    if not histogram and len(nodes) == 1:
        visit(nodes[0], True)

    unknown_rules = [
        {
            "rule": rule,
            "count": histogram[rule],
            "contexts": contexts,
        }
        for rule, contexts in sorted(unknown_contexts.items())
    ]

    return {
        "rule_histogram": dict(sorted(histogram.items())),
        "rule_contexts": dict(sorted(rule_contexts.items())),
        "unknown_rules": unknown_rules,
        "malformed_fragments": malformed,
    }


def detect_solver_result(stdout: str) -> tuple[str, str]:
    lines = stdout.splitlines(keepends=True)
    offset = 0
    for line in lines:
        stripped = line.strip()
        if stripped in SOLVER_RESULTS:
            proof_text = stdout[offset + len(line) :]
            return stripped, proof_text
        offset += len(line)
    return "no-result", ""


def z3_version(z3_executable: str) -> str:
    try:
        completed = subprocess.run(
            [z3_executable, "-version"],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except OSError as exc:
        return f"unavailable: {exc}"
    output = (completed.stdout or completed.stderr).strip()
    match = re.search(r"Z3 version\s+(\S+)", output)
    return match.group(1) if match else output


def proof_options_for(version: str) -> list[str]:
    if version.startswith("4."):
        return ["proof=true", "pp.simplify_implies=false"]
    return ["PROOF_MODE=2"]


def command_line_for(z3_executable: str, version: str, extra_options: list[str], path: pathlib.Path) -> list[str]:
    return [z3_executable, *proof_options_for(version), *extra_options, "-smt2", str(path)]


def prepare_input(original: pathlib.Path, append_get_proof: bool) -> tuple[pathlib.Path, tempfile.TemporaryDirectory[str] | None, str | None]:
    if not append_get_proof:
        return original, None, None
    data = original.read_text(encoding="utf-8")
    tempdir = tempfile.TemporaryDirectory(prefix="holsmt-proof-corpus-")
    prepared = pathlib.Path(tempdir.name) / original.name
    suffix = ""
    if "(check-sat" not in data:
        suffix += "\n(check-sat)\n"
    if "(get-proof" not in data:
        suffix += "\n(get-proof)\n"
    if "(exit" not in data:
        suffix += "(exit)\n"
    prepared.write_text(data.rstrip() + "\n" + suffix, encoding="utf-8")
    return prepared, tempdir, sha256_bytes(prepared.read_bytes())


def record_one(
    input_path: pathlib.Path,
    out_dir: pathlib.Path,
    z3_executable: str,
    version: str,
    extra_options: list[str],
    append_get_proof: bool,
    timeout: int,
) -> dict[str, object]:
    input_path = input_path.resolve()
    input_hash = sha256_file(input_path)
    run_path, tempdir, effective_hash = prepare_input(input_path, append_get_proof)
    command = command_line_for(z3_executable, version, extra_options, run_path)
    stdout = ""
    stderr = ""
    timed_out = False
    exit_code: int | None = None
    try:
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        stdout = completed.stdout
        stderr = completed.stderr
        exit_code = completed.returncode
    except OSError as exc:
        stderr = str(exc)
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
    finally:
        if tempdir is not None:
            tempdir.cleanup()

    solver_result, proof_text = detect_solver_result(stdout)
    stem = f"{input_path.stem}-{input_hash[:12]}"
    stdout_path = out_dir / "raw" / f"{stem}.stdout"
    stderr_path = out_dir / "raw" / f"{stem}.stderr"
    write_text(stdout_path, stdout)
    write_text(stderr_path, stderr)

    proof_path: str | None = None
    proof_hash: str | None = None
    proof_report = {
        "rule_histogram": {},
        "rule_contexts": {},
        "unknown_rules": [],
        "malformed_fragments": [],
    }
    if proof_text.strip():
        proof_hash = sha256_bytes(proof_text.encode("utf-8"))
        raw_path = out_dir / "proofs" / f"{stem}.proof"
        write_text(raw_path, proof_text)
        proof_path = str(raw_path)
        proof_report = extract_rule_report(proof_text)

    return {
        "schema": SCHEMA,
        "kind": "proof-corpus-entry",
        "input": {
            "path": str(input_path),
            "sha256": input_hash,
            "effective_sha256": effective_hash or input_hash,
            "append_get_proof": append_get_proof,
        },
        "z3": {
            "executable": z3_executable,
            "version": version,
            "command_line": command,
            "exit_code": exit_code,
            "timed_out": timed_out,
            "stdout_path": str(stdout_path),
            "stderr_path": str(stderr_path),
        },
        "solver": {
            "result": solver_result,
            "z3_failure": bool(timed_out or (exit_code not in (0, None))),
        },
        "proof": {
            "available": bool(proof_text.strip()),
            "raw_path": proof_path,
            "raw_sha256": proof_hash,
            **proof_report,
        },
        "holsmt": {
            "proof_parse_status": "not-run",
            "proof_replay_status": "not-run",
            "failure": None,
        },
    }


def build_summary(entries: Iterable[dict[str, object]]) -> dict[str, object]:
    entries = list(entries)
    aggregate: collections.Counter[str] = collections.Counter()
    aggregate_by_version: dict[str, collections.Counter[str]] = collections.defaultdict(collections.Counter)
    version_entries: collections.Counter[str] = collections.Counter()
    version_proofs: collections.Counter[str] = collections.Counter()
    unknown: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    malformed_count = 0
    for entry in entries:
        proof = entry["proof"]  # type: ignore[index]
        version = entry["z3"]["version"]  # type: ignore[index]
        version_entries[version] += 1
        if proof["available"]:  # type: ignore[index]
            version_proofs[version] += 1
        for rule, count in proof["rule_histogram"].items():  # type: ignore[index, union-attr]
            aggregate[rule] += count
            aggregate_by_version[version][rule] += count
        for item in proof["unknown_rules"]:  # type: ignore[index, union-attr]
            unknown[item["rule"]].append(  # type: ignore[index]
                {
                    "input": entry["input"]["path"],  # type: ignore[index]
                    "z3_version": version,
                    "count": item["count"],  # type: ignore[index]
                    "contexts": item["contexts"],  # type: ignore[index]
                }
            )
        malformed_count += len(proof["malformed_fragments"])  # type: ignore[arg-type, index]

    return {
        "schema": SCHEMA,
        "kind": "proof-corpus-summary",
        "entry_count": len(entries),
        "proof_count": sum(1 for entry in entries if entry["proof"]["available"]),  # type: ignore[index]
        "z3_versions": [
            {
                "version": version,
                "entry_count": version_entries[version],
                "proof_count": version_proofs[version],
            }
            for version in sorted(version_entries)
        ],
        "discovered_rules": sorted(aggregate),
        "aggregate_rule_histogram": dict(sorted(aggregate.items())),
        "rules_by_version": [
            {
                "z3_version": version,
                "rules": sorted(histogram),
                "rule_histogram": dict(sorted(histogram.items())),
            }
            for version, histogram in sorted(aggregate_by_version.items())
        ],
        "unknown_rule_coverage": [
            {
                "rule": rule,
                "occurrences": sum(item["count"] for item in items),
                "inputs": items,
            }
            for rule, items in sorted(unknown.items())
        ],
        "proof_rule_support": {
            "replay_supported": sorted(REPLAY_SUPPORTED_RULES),
            "parse_only": sorted(PARSE_ONLY_RULES),
        },
        "malformed_fragment_count": malformed_count,
        "entries": [entry["input"]["path"] for entry in entries],  # type: ignore[index]
    }


def load_expected_rule_manifest(path: pathlib.Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def load_json(path: pathlib.Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def resolve_manifest_path(manifest_path: pathlib.Path, value: str) -> pathlib.Path:
    path = pathlib.Path(value)
    if path.is_absolute():
        return path
    root_path = ROOT / path
    if root_path.exists():
        return root_path
    return manifest_path.parent / path


def _rule_list(value: object) -> set[str]:
    if value is None:
        return set()
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError("expected proof-rule manifest entries must be string lists")
    return set(value)


def expected_rules_for_version(manifest: object, version: str) -> set[str]:
    if isinstance(manifest, list):
        return _rule_list(manifest)
    if not isinstance(manifest, dict):
        raise ValueError("expected proof-rule manifest must be a list or object")

    rules = _rule_list(manifest.get("default"))
    rules.update(_rule_list(manifest.get("rules")))
    versions = manifest.get("versions", {})
    if versions is None:
        versions = {}
    if not isinstance(versions, dict):
        raise ValueError("expected proof-rule manifest 'versions' must be an object")

    for key, value in versions.items():
        if not isinstance(key, str):
            raise ValueError("expected proof-rule manifest version keys must be strings")
        if key == version or (key.endswith("*") and version.startswith(key[:-1])):
            rules.update(_rule_list(value))
    return rules


def build_rule_gate_report(
    entries: Iterable[dict[str, object]],
    expected_manifest: object | None,
) -> dict[str, object]:
    unseen: list[dict[str, object]] = []
    replay_unknown: list[dict[str, object]] = []
    parse_only: list[dict[str, object]] = []
    malformed: list[dict[str, object]] = []

    def artifact_refs(entry: dict[str, object]) -> dict[str, object]:
        input_info = entry.get("input", {})
        z3_info = entry.get("z3", {})
        proof_info = entry.get("proof", {})
        artifacts: dict[str, object] = {}
        if isinstance(input_info, dict):
            for source, target in (
                ("sha256", "input_sha256"),
                ("effective_sha256", "effective_input_sha256"),
            ):
                value = input_info.get(source)
                if isinstance(value, str) and value:
                    artifacts[target] = value
        if isinstance(z3_info, dict):
            for source, target in (
                ("stdout_path", "stdout_path"),
                ("stderr_path", "stderr_path"),
            ):
                value = z3_info.get(source)
                if isinstance(value, str) and value:
                    artifacts[target] = value
        if isinstance(proof_info, dict):
            for source, target in (
                ("raw_path", "proof_path"),
                ("raw_sha256", "proof_sha256"),
            ):
                value = proof_info.get(source)
                if isinstance(value, str) and value:
                    artifacts[target] = value
        return artifacts

    for entry in entries:
        input_path = entry["input"]["path"]  # type: ignore[index]
        version = entry["z3"]["version"]  # type: ignore[index]
        proof = entry["proof"]  # type: ignore[index]
        artifacts = artifact_refs(entry)
        expected = (
            expected_rules_for_version(expected_manifest, version)
            if expected_manifest is not None
            else None
        )
        contexts = proof.get("rule_contexts", {})  # type: ignore[union-attr]

        for rule, count in sorted(proof["rule_histogram"].items()):  # type: ignore[index, union-attr]
            if rule in PARSE_ONLY_RULES:
                parse_only.append(
                    {
                        "z3_version": version,
                        "input": input_path,
                        "rule": rule,
                        "count": count,
                        "contexts": contexts.get(rule, []),  # type: ignore[union-attr]
                        "artifacts": artifacts,
                    }
                )

        if expected is not None:
            for rule, count in sorted(proof["rule_histogram"].items()):  # type: ignore[index, union-attr]
                if rule not in expected:
                    unseen.append(
                        {
                            "z3_version": version,
                            "input": input_path,
                            "rule": rule,
                            "count": count,
                            "contexts": contexts.get(rule, []),  # type: ignore[union-attr]
                            "artifacts": artifacts,
                        }
                    )

        for item in proof["unknown_rules"]:  # type: ignore[index, union-attr]
            replay_unknown.append(
                {
                    "z3_version": version,
                    "input": input_path,
                    "rule": item["rule"],  # type: ignore[index]
                    "count": item["count"],  # type: ignore[index]
                    "contexts": item["contexts"],  # type: ignore[index]
                    "artifacts": artifacts,
                }
            )

        fragments = proof["malformed_fragments"]  # type: ignore[index]
        if fragments:
            malformed.append(
                {
                    "z3_version": version,
                    "input": input_path,
                    "fragments": fragments,
                    "artifacts": artifacts,
                }
            )

    return {
        "schema": SCHEMA,
        "kind": "proof-rule-discovery-gate",
        "passed": not unseen and not replay_unknown and not malformed,
        "unseen_rules": unseen,
        "replay_unknown_rules": replay_unknown,
        "parse_only_rules": parse_only,
        "malformed_fragments": malformed,
    }


def _as_string_list(value: object, label: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        errors.append(f"{label} must be a list of strings")
        return []
    return value


def _read_version_entry(
    manifest_path: pathlib.Path,
    item: dict[str, object],
    input_by_id: dict[str, dict[str, object]],
    errors: list[str],
) -> dict[str, object] | None:
    version = item.get("version")
    input_id = item.get("input")
    if not isinstance(version, str) or not version:
        errors.append("version entry is missing version")
        return None
    if not isinstance(input_id, str) or input_id not in input_by_id:
        errors.append(f"version {version} references unknown input {input_id!r}")
        return None

    input_item = input_by_id[input_id]
    input_path_value = input_item.get("path")
    if not isinstance(input_path_value, str) or not input_path_value:
        errors.append(f"input {input_id} is missing path")
        return None
    input_path = resolve_manifest_path(manifest_path, input_path_value)
    if not input_path.exists():
        errors.append(f"input {input_id} path does not exist: {input_path_value}")
        return None
    expected_input_hash = input_item.get("sha256")
    actual_input_hash = sha256_file(input_path)
    if expected_input_hash != actual_input_hash:
        errors.append(
            f"input {input_id} sha256 mismatch: expected {expected_input_hash}, got {actual_input_hash}"
        )

    def read_artifact(field: str) -> tuple[pathlib.Path | None, str]:
        value = item.get(field)
        if not isinstance(value, str) or not value:
            errors.append(f"version {version} is missing {field}")
            return None, ""
        path = resolve_manifest_path(manifest_path, value)
        if not path.exists():
            errors.append(f"version {version} artifact does not exist: {value}")
            return path, ""
        actual_hash = sha256_file(path)
        expected_hash = item.get(f"{field}_sha256")
        if expected_hash != actual_hash:
            errors.append(
                f"version {version} {field} sha256 mismatch: "
                f"expected {expected_hash}, got {actual_hash}"
            )
        return path, path.read_text(encoding="utf-8")

    stdout_path, stdout = read_artifact("stdout")
    stderr_path, stderr = read_artifact("stderr")
    proof_path, proof_text = read_artifact("proof")
    if stdout_path is None or stderr_path is None or proof_path is None:
        return None

    solver_result, stdout_proof = detect_solver_result(stdout)
    if solver_result != "unsat":
        errors.append(f"version {version} expected unsat stdout, got {solver_result}")
    if stdout_proof != proof_text:
        errors.append(f"version {version} stdout proof payload does not match proof artifact")

    proof_report = extract_rule_report(proof_text)
    expected_rule_sets = item.get("expected_rule_sets")
    if not isinstance(expected_rule_sets, dict):
        errors.append(f"version {version} expected_rule_sets must be an object")
        expected_rule_sets = {}
    histogram = proof_report["rule_histogram"]
    assert isinstance(histogram, dict)
    actual_rule_sets = {
        "replay_supported": sorted(rule for rule in histogram if rule in REPLAY_SUPPORTED_RULES),
        "parse_only": sorted(rule for rule in histogram if rule in PARSE_ONLY_RULES),
        "unsupported": sorted(rule for rule in histogram if rule not in KNOWN_RULES),
        "unknown": sorted(item["rule"] for item in proof_report["unknown_rules"]),  # type: ignore[index]
    }
    for field, actual in actual_rule_sets.items():
        expected = expected_rule_sets.get(field, [])
        if expected != actual:
            errors.append(
                f"version {version} expected_rule_sets.{field} mismatch: "
                f"expected {expected}, got {actual}"
            )

    return {
        "schema": SCHEMA,
        "kind": "proof-corpus-entry",
        "input": {
            "path": input_path_value,
            "sha256": actual_input_hash,
            "effective_sha256": actual_input_hash,
            "append_get_proof": False,
        },
        "z3": {
            "executable": str(item.get("z3_executable", "z3")),
            "version": version,
            "command_line": [
                str(item.get("z3_executable", "z3")),
                *_as_string_list(item.get("proof_options", []), f"version {version} proof_options", errors),
                "-smt2",
                input_path_value,
            ],
            "exit_code": int(item.get("exit_code", 0)),
            "timed_out": bool(item.get("timed_out", False)),
            "stdout_path": str(item.get("stdout")),
            "stderr_path": str(item.get("stderr")),
        },
        "solver": {
            "result": solver_result,
            "z3_failure": bool(item.get("z3_failure", False)),
        },
        "proof": {
            "available": bool(proof_text.strip()),
            "raw_path": str(item.get("proof")),
            "raw_sha256": sha256_bytes(proof_text.encode("utf-8")),
            **proof_report,
        },
        "holsmt": {
            "proof_parse_status": "not-run",
            "proof_replay_status": "not-run",
            "failure": None,
        },
    }


def validate_corpus_manifest(manifest_path: pathlib.Path) -> list[str]:
    errors: list[str] = []
    manifest_obj = load_json(manifest_path)
    if not isinstance(manifest_obj, dict):
        return ["proof corpus manifest root must be an object"]
    if manifest_obj.get("schema") != MATRIX_SCHEMA:
        errors.append(f"proof corpus manifest schema must be {MATRIX_SCHEMA}")

    supported_versions = _as_string_list(
        manifest_obj.get("supported_z3_versions"),
        "supported_z3_versions",
        errors,
    )
    if sorted(supported_versions) != sorted(SUPPORTED_Z3_VERSIONS):
        errors.append(
            "supported_z3_versions mismatch: expected "
            + ", ".join(SUPPORTED_Z3_VERSIONS)
            + "; got "
            + ", ".join(supported_versions)
        )

    inputs = manifest_obj.get("inputs")
    if not isinstance(inputs, list) or not inputs:
        errors.append("inputs must be a non-empty list")
        inputs = []
    input_by_id: dict[str, dict[str, object]] = {}
    for index, input_item in enumerate(inputs, 1):
        if not isinstance(input_item, dict):
            errors.append(f"inputs[{index}] must be an object")
            continue
        input_id = input_item.get("id")
        if not isinstance(input_id, str) or not input_id:
            errors.append(f"inputs[{index}] is missing id")
            continue
        input_by_id[input_id] = input_item

    versions = manifest_obj.get("versions")
    if not isinstance(versions, list) or not versions:
        errors.append("versions must be a non-empty list")
        versions = []

    entries = []
    seen_versions: set[str] = set()
    for index, version_item in enumerate(versions, 1):
        if not isinstance(version_item, dict):
            errors.append(f"versions[{index}] must be an object")
            continue
        entry = _read_version_entry(manifest_path, version_item, input_by_id, errors)
        if entry is None:
            continue
        seen_versions.add(str(entry["z3"]["version"]))  # type: ignore[index]
        entries.append(entry)

    if sorted(seen_versions) != sorted(SUPPORTED_Z3_VERSIONS):
        errors.append(
            "versions must contain exactly the supported Z3 versions: "
            + ", ".join(SUPPORTED_Z3_VERSIONS)
        )

    expected_rules_path = manifest_obj.get("expected_rules")
    expected_rules = None
    if not isinstance(expected_rules_path, str) or not expected_rules_path:
        errors.append("expected_rules must point to an expected-rule manifest")
    else:
        resolved_expected_rules = resolve_manifest_path(manifest_path, expected_rules_path)
        if not resolved_expected_rules.exists():
            errors.append(f"expected_rules path does not exist: {expected_rules_path}")
        else:
            expected_rules = load_expected_rule_manifest(resolved_expected_rules)

    if entries:
        summary = build_summary(entries)
        expected_summary_path = manifest_obj.get("expected_summary")
        if not isinstance(expected_summary_path, str) or not expected_summary_path:
            errors.append("expected_summary must point to a checked-in summary")
        else:
            expected_summary = load_json(resolve_manifest_path(manifest_path, expected_summary_path))
            if expected_summary != summary:
                errors.append("checked-in proof corpus summary is stale")

        if expected_rules is not None:
            gate = build_rule_gate_report(entries, expected_rules)
            expected_gate_path = manifest_obj.get("expected_gate")
            if not isinstance(expected_gate_path, str) or not expected_gate_path:
                errors.append("expected_gate must point to a checked-in gate report")
            else:
                expected_gate = load_json(resolve_manifest_path(manifest_path, expected_gate_path))
                if expected_gate != gate:
                    errors.append("checked-in proof-rule gate report is stale")
            if not gate["passed"]:  # type: ignore[index]
                errors.append("proof-rule gate fails for checked-in corpus")

        discovered_rules = set(summary["discovered_rules"])  # type: ignore[index]
        replay_missing = sorted(REPLAY_SUPPORTED_RULES - discovered_rules)
        replay_justifications = manifest_obj.get("missing_replay_supported_justifications", {})
        if not isinstance(replay_justifications, dict):
            errors.append("missing_replay_supported_justifications must be an object")
            replay_justifications = {}
        for rule in replay_missing:
            if not isinstance(replay_justifications.get(rule), str) or not replay_justifications[rule]:
                errors.append(f"missing replay-supported rule lacks justification: {rule}")
        for rule in replay_justifications:
            if rule not in REPLAY_SUPPORTED_RULES:
                errors.append(f"justification names an unknown replay-supported rule: {rule}")

        parse_only_missing = sorted(PARSE_ONLY_RULES - discovered_rules)
        parse_only_justifications = manifest_obj.get("missing_parse_only_justifications", {})
        if not isinstance(parse_only_justifications, dict):
            errors.append("missing_parse_only_justifications must be an object")
            parse_only_justifications = {}
        for rule in parse_only_missing:
            if (
                not isinstance(parse_only_justifications.get(rule), str)
                or not parse_only_justifications[rule]
            ):
                errors.append(f"missing parse-only rule lacks justification: {rule}")

    return errors


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run Z3 on SMT-LIB inputs and record raw proof-rule histograms."
    )
    parser.add_argument("inputs", nargs="*", help="SMT-LIB files to run through Z3")
    parser.add_argument(
        "--z3",
        default=os.environ.get("HOL4_Z3_EXECUTABLE") or "z3",
        help="Z3 executable, defaulting to HOL4_Z3_EXECUTABLE or z3",
    )
    parser.add_argument(
        "--out",
        type=pathlib.Path,
        default=pathlib.Path("src/HolSmt/tools/proof-corpus/out"),
        help="output directory for JSON and raw solver artifacts",
    )
    parser.add_argument(
        "--entries",
        default="entries.jsonl",
        help="JSONL file name inside --out",
    )
    parser.add_argument(
        "--summary",
        default="summary.json",
        help="summary JSON file name inside --out",
    )
    parser.add_argument(
        "--append-get-proof",
        action="store_true",
        help="run a temporary copy with check-sat/get-proof/exit appended when missing",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=30,
        help="per-input Z3 timeout in seconds",
    )
    parser.add_argument(
        "--z3-option",
        action="append",
        default=[],
        help="additional option passed to Z3 before -smt2",
    )
    parser.add_argument(
        "--expected-rules",
        type=pathlib.Path,
        help=(
            "JSON manifest of expected proof rules. A list applies to every Z3 "
            "version; an object may contain default/rules and versions entries."
        ),
    )
    parser.add_argument(
        "--gate-report",
        default="rule-gate.json",
        help="rule-discovery gate JSON file name inside --out",
    )
    parser.add_argument(
        "--fail-on-unseen-rules",
        action="store_true",
        help="return nonzero if a discovered proof rule is absent from --expected-rules",
    )
    parser.add_argument(
        "--fail-on-unknown-rules",
        action="store_true",
        help="return nonzero if a discovered proof rule is not replay-supported by HolSmt",
    )
    parser.add_argument(
        "--validate-corpus-manifest",
        nargs="?",
        const=DEFAULT_SUPPORTED_VERSION_MANIFEST,
        type=pathlib.Path,
        help=(
            "validate a checked-in proof-corpus matrix manifest without running Z3; "
            "defaults to the supported-version corpus manifest"
        ),
    )
    args = parser.parse_args(argv)
    if args.validate_corpus_manifest is not None:
        return args
    if not args.inputs:
        parser.error("SMT-LIB input files are required unless --validate-corpus-manifest is used")
    if args.fail_on_unseen_rules and args.expected_rules is None:
        parser.error("--fail-on-unseen-rules requires --expected-rules")
    return args


def print_gate_findings(report: dict[str, object]) -> None:
    unseen = report["unseen_rules"]  # type: ignore[index]
    replay_unknown = report["replay_unknown_rules"]  # type: ignore[index]
    malformed = report["malformed_fragments"]  # type: ignore[index]
    if unseen:
        print("unseen proof rules:")
        for item in unseen[:10]:  # type: ignore[index]
            print(
                f"  {item['z3_version']} {item['input']}: "  # type: ignore[index]
                f"{item['rule']} ({item['count']})"  # type: ignore[index]
            )
    if replay_unknown:
        print("HolSmt replay-unknown proof rules:")
        for item in replay_unknown[:10]:  # type: ignore[index]
            print(
                f"  {item['z3_version']} {item['input']}: "  # type: ignore[index]
                f"{item['rule']} ({item['count']})"  # type: ignore[index]
            )
    if malformed:
        print("malformed proof fragments:")
        for item in malformed[:10]:  # type: ignore[index]
            print(f"  {item['z3_version']} {item['input']}")  # type: ignore[index]


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.validate_corpus_manifest is not None:
        errors = validate_corpus_manifest(args.validate_corpus_manifest)
        if errors:
            print("proof corpus manifest validation failed:")
            for error in errors:
                print(f"  {error}")
            return 1
        print(f"validated proof corpus manifest {args.validate_corpus_manifest}")
        return 0

    out_dir = args.out.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    version = z3_version(args.z3)

    entries = [
        record_one(
            pathlib.Path(path),
            out_dir,
            args.z3,
            version,
            args.z3_option,
            args.append_get_proof,
            args.timeout,
        )
        for path in args.inputs
    ]

    entries_path = out_dir / args.entries
    with entries_path.open("w", encoding="utf-8") as outfile:
        for entry in entries:
            json.dump(entry, outfile, sort_keys=True)
            outfile.write("\n")

    summary = build_summary(entries)
    json_dump(out_dir / args.summary, summary)

    print(f"wrote {len(entries)} corpus entries to {entries_path}")
    print(f"wrote summary to {out_dir / args.summary}")

    expected_manifest = None
    if args.expected_rules is not None:
        expected_manifest = load_expected_rule_manifest(args.expected_rules)

    should_write_gate = args.expected_rules is not None or args.fail_on_unknown_rules
    if not should_write_gate:
        return 0

    gate_report = build_rule_gate_report(entries, expected_manifest)
    gate_path = out_dir / args.gate_report
    json_dump(gate_path, gate_report)
    print(f"wrote proof-rule gate report to {gate_path}")

    fail_unseen = bool(gate_report["unseen_rules"]) or bool(gate_report["malformed_fragments"])
    fail_unknown = bool(gate_report["replay_unknown_rules"])
    if (args.fail_on_unseen_rules and fail_unseen) or (args.fail_on_unknown_rules and fail_unknown):
        print_gate_findings(gate_report)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
