#!/usr/bin/env python3
"""Bounded native regression tests for the two compact proof producers."""

import argparse
import itertools
import pathlib
import re
import subprocess


HERE = pathlib.Path(__file__).resolve().parent
TIMEOUT = 30


def run(command, source, output=None):
    with source.open("rb") as inp:
        result = subprocess.run(command,
                                stdin=inp,
                                stdout=output or subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                timeout=TIMEOUT,
                                check=False)
    return result


def tokens(text):
    pos = 0
    while pos < len(text):
        char = text[pos]
        if char.isspace():
            pos += 1
        elif char == ';':
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end + 1
        elif char in '()':
            yield char
            pos += 1
        elif char == '|':
            end = pos + 1
            while end < len(text):
                if text[end] == '\\':
                    end += 2
                elif text[end] == '|':
                    break
                else:
                    end += 1
            if end >= len(text):
                raise AssertionError("unterminated quoted symbol")
            yield text[pos:end + 1]
            pos = end + 1
        elif char == '"':
            end = pos + 1
            while end < len(text):
                if text[end] == '"':
                    if end + 1 < len(text) and text[end + 1] == '"':
                        end += 2
                        continue
                    break
                end += 1
            if end >= len(text):
                raise AssertionError("unterminated string")
            yield text[pos:end + 1]
            pos = end + 1
        else:
            end = pos + 1
            while (end < len(text) and not text[end].isspace()
                   and text[end] not in '();|"'):
                end += 1
            yield text[pos:end]
            pos = end


def forms(stream):
    stream = iter(stream)
    for first in stream:
        if first != '(':
            yield (first,)
            continue
        result = [first]
        depth = 1
        while depth:
            token = next(stream)
            result.append(token)
            depth += (token == '(') - (token == ')')
        yield tuple(result)


def z3_equivalent(legacy, compact):
    generated = re.compile(r'[@$?]x[0-9]+\Z')
    forward = {}
    reverse = {}
    for left, right in itertools.zip_longest(tokens(legacy), tokens(compact)):
        assert left is not None and right is not None
        if generated.fullmatch(left):
            expected = "?&" if left[0] == '?' else left[0]
            assert right[0] in expected
            assert forward.setdefault(left, right) == right
            assert reverse.setdefault(right, left) == left
        else:
            assert left == right


def decode_z3_quoted(token):
    assert token.startswith('|') and token.endswith('|')
    decoded = []
    pos = 1
    while pos + 1 < len(token):
        if token[pos] == '\\':
            assert pos + 2 < len(token)
            decoded.append(token[pos + 1])
            pos += 2
        else:
            decoded.append(token[pos])
            pos += 1
    return ''.join(decoded)


def cvc_commands(text):
    stream = iter(tokens(text))
    assert next(stream) == "unsat" and next(stream) == '('
    for first in stream:
        if first == ')':
            assert next(stream, None) is None
            return
        assert first == '('
        command = [first]
        depth = 1
        while depth:
            token = next(stream)
            command.append(token)
            depth += (token == '(') - (token == ')')
        yield command
    raise AssertionError("truncated CPC wrapper")


SCALAR = re.compile(
    r'(?:true|false|-?[0-9]+(?:\.[0-9]+|/[0-9]+)?|#[bx][0-9a-fA-F]+|'
    r'roundNearestTiesToEven|roundNearestTiesToAway|roundTowardPositive|'
    r'roundTowardNegative|roundTowardZero)\Z')


def scalar_body(body):
    if len(body) == 1:
        return bool(SCALAR.fullmatch(body[0])) or body[0].startswith('"')
    if len(body) < 3 or body[0] != '(' or body[-1] != ')':
        return False
    if body[1] not in ('-', '/', 'fp', '_'):
        return False
    allowed = {'(', ')', '-', '/', 'fp', '_', '+zero', '-zero',
               '+oo', '-oo', 'NaN'}
    return all(token in allowed or SCALAR.fullmatch(token)
               or re.fullmatch(r'bv[0-9]+', token) for token in body)


def cvc_equivalent(legacy, compact):
    old = cvc_commands(legacy)
    new = cvc_commands(compact)
    literals = {}
    first = next(new)
    while (first[:2] == ['(', 'define'] and first[3:5] == ['(', ')']
           and scalar_body(first[5:-1])):
        name, body = first[2], first[5:-1]
        assert name not in literals
        literals[name] = body
        first = next(new)
    new = itertools.chain([first], new)
    forward = {}
    reverse = {}
    binders = {'define', 'assume', 'assume-push', 'step', 'step-pop'}
    for left, right in itertools.zip_longest(old, new):
        assert left is not None and right is not None
        if left[1] in binders:
            assert right[1] == left[1]
            old_name, new_name = left[2], right[2]
            assert new_name not in literals
            assert forward.setdefault(old_name, new_name) == new_name
            assert reverse.setdefault(new_name, old_name) == old_name
        expanded = (part for token in right
                    for part in literals.get(token, [token]))
        for old_token, new_token in itertools.zip_longest(left, expanded):
            assert old_token is not None and new_token is not None
            assert forward.get(old_token, old_token) == new_token


def check_success(result):
    assert result.returncode == 0, result.stderr.decode(errors="replace")
    return result.stdout.decode()


def check_z3(executable):
    source = HERE / "z3-lexical.smt2"
    base = [executable, "proof=true", "pp.simplify_implies=false", "-in"]
    implicit = check_success(run(base, source))
    explicit = check_success(run(base + ["pp.compact_proof_names=false"],
                                 source))
    assert implicit == explicit
    compact = check_success(run(base + ["pp.compact_proof_names=true"],
                                source))
    z3_equivalent(implicit, compact)

    escaped = HERE / "z3-escaped-symbol.smt2"
    escaped_implicit = check_success(run(base, escaped))
    escaped_explicit = check_success(
        run(base + ["pp.compact_proof_names=false"], escaped))
    assert escaped_implicit == escaped_explicit
    escaped_compact = check_success(
        run(base + ["pp.compact_proof_names=true"], escaped))
    z3_equivalent(escaped_implicit, escaped_compact)
    printed_symbols = [token for token in tokens(escaped_compact)
                       if token.startswith('|')]
    assert printed_symbols
    assert {decode_z3_quoted(token) for token in printed_symbols} == {
        'p\\|  (x)'}

    one = HERE / "z3-proof-closure-one.smt2"
    one_legacy = check_success(run(base, one))
    one_explicit = check_success(
        run(base + ["pp.compact_proof_names=false"], one))
    assert one_legacy == one_explicit
    one_compact = check_success(
        run(base + ["pp.compact_proof_names=true"], one))
    z3_equivalent(one_legacy, one_compact)
    one_closures = set(re.findall(r'\(let\(\((&[A-Za-z]+)\(lambda',
                                  one_compact))
    assert len(one_closures) == 1
    assert all("proof-bind " + name in one_compact
               for name in one_closures)

    nested = HERE / "z3-proof-closure-nested.smt2"
    nested_legacy = check_success(run(base, nested))
    nested_explicit = check_success(
        run(base + ["pp.compact_proof_names=false"], nested))
    assert nested_legacy == nested_explicit
    nested_compact = check_success(
        run(base + ["pp.compact_proof_names=true"], nested))
    z3_equivalent(nested_legacy, nested_compact)
    nested_closures = set(re.findall(r'\(let\(\((&[A-Za-z]+)\(lambda',
                                     nested_compact))
    assert len(nested_closures) == 2
    assert "&a" in nested_compact
    assert "&a" not in nested_closures
    assert all("proof-bind " + name in nested_compact
               for name in nested_closures)

    semantic = HERE / "z3-semantic-lambda.smt2"
    semantic_legacy = check_success(run(base, semantic))
    semantic_compact = check_success(
        run(base + ["pp.compact_proof_names=true"], semantic))
    z3_equivalent(semantic_legacy, semantic_compact)
    assert re.search(r'\(let\(\(\?[A-Za-z]+\(lambda', semantic_compact)
    assert not re.search(r'\(let\(\(&[A-Za-z]+\(lambda', semantic_compact)


def cvc_command(executable, compact, local=False):
    command = [executable,
               "--produce-proofs",
               "--proof-format-mode=cpc",
               "--proof-granularity=dsl-rewrite",
               "--fp-exp",
               "--sets-exp",
               "--lang=smt2"]
    command.append("--proof-compact-names" if compact
                   else "--no-proof-compact-names")
    if local:
        command.append("--no-proof-dag-global")
    return command


def check_cvc5(executable):
    lexical = HERE / "cvc5-lexical.smt2"
    implicit = check_success(run(cvc_command(executable, False)[:-1], lexical))
    explicit = check_success(run(cvc_command(executable, False), lexical))
    assert implicit == explicit
    compact = check_success(run(cvc_command(executable, True), lexical))
    cvc_equivalent(implicit, compact)
    assert "|u(a);b|" in compact and "|f p|" in compact

    local_legacy = check_success(
        run(cvc_command(executable, False, True), lexical))
    local_compact = check_success(
        run(cvc_command(executable, True, True), lexical))
    cvc_equivalent(local_legacy, local_compact)

    repeated = HERE / "cvc5-local-repeated.smt2"
    local = check_success(run(cvc_command(executable, True, True), repeated))
    local_forms = list(forms(tokens(local)))
    assert local_forms[0] == ("unsat",)
    assert len(local_forms) == 3
    assert local_forms[1] == local_forms[2]

    fp = HERE / "cvc5-fp-operands.smt2"
    fp_output = check_success(run(cvc_command(executable, True), fp))
    pattern = re.compile(
        r'\(@fp\.(?:NAN|INF|ZERO|SIGN|EXPONENT|SIGNIFICAND)\s*'
        r'\(_\s+BitVec\s+[0-9]+\)\s*(@[A-Za-z0-9]+)\)')
    assert len(set(pattern.findall(fp_output))) >= 2

    collision = HERE / "cvc5-semantic-collision.smt2"
    collision_legacy = check_success(
        run(cvc_command(executable, False), collision))
    collision_compact = check_success(
        run(cvc_command(executable, True), collision))
    cvc_equivalent(collision_legacy, collision_compact)
    assert "asserted" in collision_compact
    assert "refl" in collision_compact


def check_cvc5_unit(source, build):
    executable = build / "compact_names_smoke"
    compile_result = subprocess.run(
        ["c++", "-std=c++17",
         "-D__BUILDING_CVC5LIB_UNIT_TEST",
         "-I", str(source / "include"),
         "-I", str(build / "include"),
         "-I", str(source / "src"),
         "-I", str(source / "src/include"),
         "-I", str(build / "src"),
         "-I", str(build / "deps/include"),
         str(HERE / "compact_names_smoke.cpp"),
         "-L", str(build / "src"),
         "-Wl,-rpath," + str(build / "src"),
         "-lcvc5", "-o", str(executable)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=TIMEOUT,
        check=False)
    assert compile_result.returncode == 0, compile_result.stderr.decode()
    test_result = subprocess.run([str(executable)],
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE,
                                 timeout=TIMEOUT,
                                 check=False)
    assert test_result.returncode == 0, test_result.stderr.decode()


def check_z3_unit(source, build):
    executable = build / "z3_proof_closure_smoke"
    compile_result = subprocess.run(
        ["c++", "-std=c++17", "-D_EXTERNAL_RELEASE", "-D_MP_INTERNAL",
         "-I", str(build / "src"),
         "-I", str(source / "src"),
         str(HERE / "z3_proof_closure_smoke.cpp"),
         str(build / "libz3.a"),
         "-lpthread", "-o", str(executable)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=TIMEOUT,
        check=False)
    assert compile_result.returncode == 0, compile_result.stderr.decode()
    test_result = subprocess.run([str(executable)],
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE,
                                 timeout=TIMEOUT,
                                 check=False)
    assert test_result.returncode == 0, test_result.stderr.decode()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cvc5", required=True)
    parser.add_argument("--z3", required=True)
    parser.add_argument("--z3-source", type=pathlib.Path)
    parser.add_argument("--z3-build", type=pathlib.Path)
    parser.add_argument("--cvc5-source", type=pathlib.Path)
    parser.add_argument("--cvc5-build", type=pathlib.Path)
    args = parser.parse_args()
    check_z3(args.z3)
    check_cvc5(args.cvc5)
    if args.z3_source or args.z3_build:
        assert args.z3_source and args.z3_build
        check_z3_unit(args.z3_source, args.z3_build)
    if args.cvc5_source or args.cvc5_build:
        assert args.cvc5_source and args.cvc5_build
        check_cvc5_unit(args.cvc5_source, args.cvc5_build)
    print("native compact producer tests: OK")


if __name__ == "__main__":
    main()
