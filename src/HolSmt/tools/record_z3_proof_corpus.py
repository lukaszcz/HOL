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
    "mp~",
    "nnf-neg",
    "nnf-pos",
    "not-or-elim",
    "quant-inst",
    "quant-intro",
    "refl",
    "rewrite",
    "sk",
    "symm",
    "th-lemma-arith",
    "th-lemma-array",
    "th-lemma-basic",
    "th-lemma-bv",
    "trans",
    "trans*",
    "true-axiom",
    "unit-resolution",
}

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
    "symm": "one",
    "th-lemma-arith": "list",
    "th-lemma-array": "list",
    "th-lemma-basic": "list",
    "th-lemma-bv": "list",
    "trans": "two",
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
            "unknown_rules": [],
            "malformed_fragments": malformed,
        }

    def record_unknown(rule: str, node: ListNode) -> None:
        if len(unknown_contexts[rule]) >= 3:
            return
        loc = line_col(proof_text, node.start)
        unknown_contexts[rule].append(
            {
                "line": loc["line"],
                "column": loc["column"],
                "context": context_for(proof_text, node.start, node.end),
            }
        )

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
        if head_name not in REPLAY_SUPPORTED_RULES:
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
    unknown: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    malformed_count = 0
    for entry in entries:
        proof = entry["proof"]  # type: ignore[index]
        for rule, count in proof["rule_histogram"].items():  # type: ignore[index, union-attr]
            aggregate[rule] += count
        for item in proof["unknown_rules"]:  # type: ignore[index, union-attr]
            unknown[item["rule"]].append(  # type: ignore[index]
                {
                    "input": entry["input"]["path"],  # type: ignore[index]
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
        "aggregate_rule_histogram": dict(sorted(aggregate.items())),
        "unknown_rule_coverage": [
            {
                "rule": rule,
                "occurrences": sum(item["count"] for item in items),
                "inputs": items,
            }
            for rule, items in sorted(unknown.items())
        ],
        "malformed_fragment_count": malformed_count,
        "entries": [entry["input"]["path"] for entry in entries],  # type: ignore[index]
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run Z3 on SMT-LIB inputs and record raw proof-rule histograms."
    )
    parser.add_argument("inputs", nargs="+", help="SMT-LIB files to run through Z3")
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
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
