# TASK_03 — string/regex operator provability sweep

Date: 2026-07-24

## Result

Thirty-two of the 34 operators have a semantic ground script that
returns `unsat` with a full Z3 proof on every supported version.
Two operators, `str.replace_re` and `str.replace_re_all`, are explicit
owner-escalation items: every tested semantic ground evaluation returns
`unknown` and then `proof is not available` on both the oldest and
newest versions.

The table refers to validation commit
`18b2576207f19ebd5bd205d39a080ac5512d22c8`; paths are relative to
that checkout.  Frozen recordings and direct reruns agree
byte-for-byte for all 34 operator-presence inputs on Z3 4.11.2 and
4.15.3.  The two self-disequality recordings are not accepted as
semantic provability evidence and are escalated below.

## Operator-to-script table

| Operator | Provable script or escalation | Matrix evidence |
| --- | --- | --- |
| `str.++` | `inputs/operator_str_concat.smt2` | full proof, 5/5 |
| `str.len` | `inputs/operator_str_len.smt2` | full proof, 5/5 |
| `str.<` | `inputs/operator_str_lt.smt2` | full proof, 5/5 |
| `str.<=` | `inputs/operator_str_le.smt2` | full proof, 5/5 |
| `str.at` | `inputs/operator_str_at.smt2` | full proof, 5/5 |
| `str.substr` | `inputs/operator_str_substr.smt2` | full proof, 5/5 |
| `str.prefixof` | `inputs/operator_str_prefixof.smt2` | full proof, 5/5 |
| `str.suffixof` | `inputs/operator_str_suffixof.smt2` | full proof, 5/5 |
| `str.contains` | `inputs/operator_str_contains.smt2` | full proof, 5/5 |
| `str.indexof` | `inputs/operator_str_indexof.smt2` | full proof, 5/5 |
| `str.replace` | `inputs/operator_str_replace.smt2` | full proof, 5/5 |
| `str.replace_all` | `inputs/operator_str_replace_all.smt2` | full proof, 5/5 |
| `str.is_digit` | `inputs/operator_str_is_digit.smt2` | full proof, 5/5 |
| `str.to_code` | `inputs/operator_str_to_code.smt2` | full proof, 5/5 |
| `str.from_code` | `inputs/operator_str_from_code.smt2` | full proof, 5/5 |
| `str.to_int` | `inputs/operator_str_to_int.smt2` | full proof, 5/5 |
| `str.from_int` | `inputs/operator_str_from_int.smt2` | full proof, 5/5 |
| `str.to_re` | `inputs/operator_str_to_re.smt2` | full proof, 5/5 |
| `str.in_re` | `inputs/operator_str_in_re.smt2` | full proof, 5/5 |
| `str.replace_re` | **ESCALATION E-01** | no semantic proof-producing instance found |
| `str.replace_re_all` | **ESCALATION E-02** | no semantic proof-producing instance found |
| `re.none` | `inputs/operator_re_none.smt2` | full proof, 5/5 |
| `re.all` | `inputs/operator_re_all.smt2` | full proof, 5/5 |
| `re.allchar` | `inputs/operator_re_allchar.smt2` | full proof, 5/5 |
| `re.++` | `inputs/operator_re_concat.smt2` | full proof, 5/5 |
| `re.union` | `inputs/operator_re_union.smt2` | full proof, 5/5 |
| `re.inter` | `inputs/operator_re_inter.smt2` | full proof, 5/5 |
| `re.diff` | `inputs/operator_re_diff.smt2` | full proof, 5/5 |
| `re.*` | `inputs/operator_re_star.smt2` | full proof, 5/5 |
| `re.+` | `inputs/operator_re_plus.smt2` | full proof, 5/5 |
| `re.opt` | `inputs/operator_re_opt.smt2` | full proof, 5/5 |
| `re.range` | `inputs/operator_re_range.smt2` | full proof, 5/5 |
| `re.^` | `inputs/operator_re_power.smt2` | full proof, 5/5 |
| `re.loop` | `inputs/operator_re_loop.smt2` | full proof, 5/5 |

The common path prefix is
`tools/proof-corpus/strings/`.  Each listed script asserts the
negation of a concrete semantic result.  For example,
`str.replace_all "aba" "a" "x" = "xbx"` is proof-producing even
though the corresponding operator is incomplete on symbolic goals.

`re.comp` is outside the frozen 21-plus-13 table but was also checked:
the ground `inputs/extra_re_comp.smt2` and the targeted symbolic
complement-range probe both produce full proofs on all five versions.
The extra `(_ char H)` input is likewise proof-producing.

## Owner escalation — solver-incomplete operators

### E-01: `str.replace_re`

The corpus input
`inputs/operator_str_replace_re.smt2` is a self-disequality.  It
does produce a full proof and retains the operator application, but
it proves only equality reflexivity and is therefore not evidence
that Z3 can establish any semantic result for the operator.

Six semantic ground classes were attempted on both Z3 4.11.2 and
4.15.3:

| Class | Representative intended equality |
| --- | --- |
| matching literal | `replace_re("abc",to_re("b"),"X") = "aXc"` |
| non-matching literal | `replace_re("abc",to_re("z"),"X") = "abc"` |
| empty source | `replace_re("",to_re("a"),"X") = ""` |
| empty language | `replace_re("abc",re.none,"X") = "abc"` |
| all-character language | `replace_re("a",re.allchar,"X") = "X"` |
| deletion | `replace_re("a",to_re("a"),"") = ""` |

All 12 runs returned:

```text
unknown
(error "... proof is not available")
```

Recommendation for the owner: authorize an enumerated
`theory-behavior:z3-unsupported` row for the semantic unsat-proof
case.  Keep the self-disequality only as proof-parser/operator-presence
evidence; do not present it as semantic coverage.

### E-02: `str.replace_re_all`

The corpus input
`inputs/operator_str_replace_re_all.smt2` has the same
self-disequality limitation.

Six semantic ground classes were attempted on both Z3 4.11.2 and
4.15.3:

| Class | Representative intended equality |
| --- | --- |
| repeated matching literal | `replace_re_all("aba",to_re("a"),"X") = "XbX"` |
| non-matching literal | `replace_re_all("abc",to_re("z"),"X") = "abc"` |
| empty source | `replace_re_all("",to_re("a"),"X") = ""` |
| empty language | `replace_re_all("abc",re.none,"X") = "abc"` |
| all-character language | `replace_re_all("abc",re.allchar,"X") = "XXX"` |
| deletion | `replace_re_all("aaa",to_re("a"),"") = ""` |

All 12 runs returned `unknown` with no proof.  The same owner action
is recommended: one explicit `z3-unsupported` semantic row, while the
self-disequality remains occurrence evidence only.

## Verification

The frozen 34 operator-presence scripts were directly rerun:

| Z3 | scripts | `unsat` plus full proof | byte-identical to frozen stdout |
| --- | ---: | ---: | ---: |
| 4.11.2 | 34 | 34 | 34 |
| 4.15.3 | 34 | 34 | 34 |

This verifies the 32 accepted scripts and confirms that the two
escalated operator applications can occur in proof objects.  The
separate 24-run semantic sweep is the evidence that those two cannot
currently back meaningful unsat-proof rows.
