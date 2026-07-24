# TASK_02 — Z3 string/regex proof corpus and symbol inventory

Date: 2026-07-24

## Recorded corpus

The separately versioned `holsmt-validation` branch
`phase4-task02` (commit `18b2576207f19ebd5bd205d39a080ac5512d22c8`)
contains the corpus under
`tools/proof-corpus/strings/`.

The checked corpus has 47 inputs per Z3 version:

- 11 named drafting probes: concat, length, regex membership,
  substr, contains, `str.<`, `str.to_int`, `re.loop`, `re.comp`,
  ground `str.replace_all`, and literal escapes;
- 34 proof-producing unsat inputs covering every operator in the
  current 21-`str.*` plus 13-`re.*` surface;
- two extra ground inputs for the missing frontend entries
  `re.comp` and `(_ char H)`.

`str.replace_re` and `str.replace_re_all` return `unknown` when Z3
is asked to evaluate the obvious concrete result, including on
4.11.2 and 4.15.3. Their operator-presence recordings therefore
use self-disequality contradictions, which produce full proofs and
retain the operator applications in the raw proof. The ground
semantic provability sweep remains TASK_03/TASK_05 scope.

| Z3 | entries | unsat proofs | Z3 failures/timeouts | `seq` lemmas | `char` lemmas | gate |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 4.11.2 | 47 | 47 | 0 | 50 | 39 | pass |
| 4.12.4 | 47 | 47 | 0 | 68 | 39 | pass |
| 4.13.0 | 47 | 47 | 0 | 68 | 39 | pass |
| 4.14.1 | 47 | 47 | 0 | 68 | 39 | pass |
| 4.15.3 | 47 | 47 | 0 | 72 | 39 | pass |

Every version passes all four deterministic occurrence gates:
`th-lemma-seq`, `th-lemma-char`, `seq:*`, and `char:*`.

## Internal-symbol inventory

The recorder now extracts exact string-internal spellings into each
entry and the per-version summaries. All five versions contain:

- `seq.unit`;
- the internal `Char` head and decimal literals `(_ Char n)`;
- `seq.nth_i`;
- indexed `(_ seq.tail seq.tail)`;
- indexed `(_ seq.eq seq.eq)`;
- `seq.stoi`;
- `seq.digit2int`;
- indexed prefix witnesses;
- indexed `(_ char.bit char.bit k)`;
- `char.is_digit`;
- indexed `(_ aut.accept aut.accept)`.

The plan's spelling `seq.digit` was not emitted by any of the five
versions. The actual proof symbol is `seq.digit2int`; TASK_10 and
TASK_17 should recognize the observed spelling and may retain
`seq.digit` only as a defensive alias.

| Z3 | `seq.prefix.*` spellings | occurrences each | char-bit indices |
| --- | --- | ---: | --- |
| 4.11.2 | `c`, `d`, `x`, `y`, `z` | 1 | 0–17 |
| 4.12.4 | `c`, `d`, `x`, `y`, `z` | 2 | 0–17 |
| 4.13.0 | `c`, `d`, `x`, `y`, `z` | 2 | 0–17 |
| 4.14.1 | `c`, `d`, `x`, `y`, `z` | 2 | 0–17 |
| 4.15.3 | `c`, `d`, `x`, `y`, `z` | 2 | 0–17 |

The exact indexed witness heads are
`(_ seq.prefix.c seq.prefix.c)` through
`(_ seq.prefix.z seq.prefix.z)`. The observed name set is stable
in this corpus; only occurrence counts differ on 4.11.2.

## String-literal escape pin

The literal probe supplies equivalent inputs using `\uXXXX`,
`\u{...}`, doubled quotes, a literal backslash, a non-BMP code
point, and the maximum `0x2FFFF` code point. Every matrix version
prints the same normalized proof spellings:

```text
""""
"A\u{1f642}"
"\"
"\u{2ffff}"
"\u{7}"
```

Consequences for TASK_12:

- hex digits are lowercased;
- four-digit escapes normalize to braced minimal-width form when
  an escape remains;
- printable ASCII remains literal;
- quotes use SMT-LIB doubling;
- backslash remains a literal backslash;
- non-BMP and maximum code points use lowercase braced escapes.

## Rule-head delta

The corpus has no replay-unknown rule head and no malformed proof
fragment. It does expose two ordinary heads outside the historical
§0.3 histogram:

- `commutativity`;
- `true-axiom`.

Both were already in the recorder's known/replay vocabulary, so no
new general rule plumbing was added. They are nevertheless flagged
here because the acceptance criterion requires every delta from the
§0.3 histogram to be prominent. The theory heads observed are
`th-lemma-arith`, `th-lemma-seq`, and the newly registered
`th-lemma-char`.

## Reproduction and checks

The validation corpus includes a deterministic generator,
per-version raw stdout/stderr and proof payloads, normalized
entries, summaries, rule gates, and `matrix-summary.json`.
`verify_z3_versions.sh` now records and gates this string corpus for
every selected version.

Verified locally:

- recorder unit tests: 26/26 pass;
- supported-version static manifest validation: pass;
- oldest/newest corpus regeneration with all occurrence gates:
  pass;
- all five checked corpus directories: 47/47 unsat proofs and
  passing rule gates;
- full conformance suite: 1,230/1,230 expected outcomes pass;
- HOL selftest shards: 8/8 pass;
- `h4pedant`: pass.

The validation repository's broader Python discovery has four
pre-existing `test_generate_complete_corpus` failures: its fixture
still expects the pre-refactor `parsedicts_of_logic` case expression,
whereas this HolSmt branch uses the refactored `SmtLib_Logics`
structure. The recorder's own 26-test suite is green.
