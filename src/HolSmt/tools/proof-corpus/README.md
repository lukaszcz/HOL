# HolSmt Z3 Proof Corpus Recorder

`record_z3_proof_corpus.py` records raw Z3 proof output for SMT-LIB inputs
without requiring HolSmt proof parsing or replay to succeed.

Example:

```sh
python3 src/HolSmt/tools/record_z3_proof_corpus.py \
  --out /tmp/holsmt-proof-corpus \
  src/HolSmt/tools/proof-corpus/minimal_bool_unsat.smt2
```

The tool writes:

- `entries.jsonl`: one `holsmt-z3-proof-corpus-v1` JSON object per input.
- `summary.json`: aggregate rule histogram and unknown-rule coverage, intended
  as input for the support-matrix task. The summary includes `discovered_rules`,
  `z3_versions`, `rules_by_version`, and `proof_rule_support` so proof-format
  drift is visible per solver version and parse-only proof wrappers are
  explicit.
- `rule-gate.json`: when `--expected-rules` or `--fail-on-unknown-rules` is
  used, a regression-gate report for unseen or replay-unknown proof rules.
- `raw/*.stdout` and `raw/*.stderr`: exact solver process output.
- `proofs/*.proof`: raw proof text after the solver result line, when present.

Each entry separates Z3 process status from HolSmt proof parse/replay status.
The current recorder does not run the ML proof parser, so the HolSmt statuses
are `not-run`; later tooling can fill those fields without changing the
corpus schema.

The proof-rule histogram is extracted directly from raw proof S-expressions.
Each rule keeps up to three local proof contexts. Rules not supported by the
current `Z3_ProofParser`/`Z3_ProofReplay` proofterm table are emitted under
`unknown_rules` with local proof context. Transparent parser-only wrappers such
as `proof-bind` are listed under the summary's
`proof_rule_support.parse_only` and under `rule-gate.json` `parse_only_rules`
when they are discovered.
Malformed proof syntax is emitted under `malformed_fragments` with line,
column, and context so the fragment can be minimized later.

For a local regression gate over the checked-in minimal corpus:

```sh
python3 src/HolSmt/tools/record_z3_proof_corpus.py \
  --out /tmp/holsmt-proof-corpus \
  --expected-rules src/HolSmt/tools/proof-corpus/minimal_expected_rules.json \
  --fail-on-unseen-rules \
  --fail-on-unknown-rules \
  src/HolSmt/tools/proof-corpus/minimal_bool_unsat.smt2
```

For the checked-in supported-version corpus matrix:

```sh
python3 src/HolSmt/tools/record_z3_proof_corpus.py \
  --validate-corpus-manifest
```

This validates `supported_versions/manifest.json`, the raw stdout/stderr/proof
artifacts for Z3 2.19.1, 4.12.4, and 4.13.0, the normalized
`supported_versions/summary.json`, and `supported_versions/rule-gate.json`.
The validation recomputes input and artifact hashes, extracts the proof-rule
histogram from the raw proof text, checks the expected replay-supported,
parse-only, unsupported, and unknown-rule sets for each version, and fails if
the checked-in unseen-rule gate would no longer pass.

The expected-rule manifest may be either a JSON list of rule names for every
Z3 version, or an object with `default`/`rules` and `versions` entries. Version
keys match exactly; keys ending in `*` match by prefix, for example `4.*`.
The gate reports Z3 version, input file, rule name, count, and local proof
context for every unseen or replay-unknown rule. Malformed proof fragments are
reported separately so unknown rules are not hidden behind parser failures.

The checked-in `minimal_bool_unsat.smt2` is a small HolSmt-style SMT-LIB proof
input suitable for selftests and minimized repros.
The supported-version matrix uses this intentionally small input for stable
cross-version proof evidence; `supported_versions/manifest.json` records
justifications for supported replay rules that do not occur in that minimal
raw corpus.
