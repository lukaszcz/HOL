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
  as input for the support-matrix task.
- `raw/*.stdout` and `raw/*.stderr`: exact solver process output.
- `proofs/*.proof`: raw proof text after the solver result line, when present.

Each entry separates Z3 process status from HolSmt proof parse/replay status.
The current recorder does not run the ML proof parser, so the HolSmt statuses
are `not-run`; later tooling can fill those fields without changing the
corpus schema.

The proof-rule histogram is extracted directly from raw proof S-expressions.
Rules not supported by the current `Z3_ProofParser`/`Z3_ProofReplay`
proofterm table are emitted under `unknown_rules` with local proof context.
Malformed proof syntax is emitted under `malformed_fragments` with line,
column, and context so the fragment can be minimized later.

The checked-in `minimal_bool_unsat.smt2` is a small HolSmt-style SMT-LIB proof
input suitable for selftests and minimized repros.
