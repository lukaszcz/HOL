# Native compact producer regression tests

`run_native_compact_tests.py` exercises patched release binaries through their
public command-line interfaces. Pass the cvc5 and Z3 prototype executables:

```sh
python3 tests/run_native_compact_tests.py \
  --cvc5 /path/to/cvc5 --z3 /path/to/z3 \
  --cvc5-source /path/to/cvc5-source --cvc5-build /path/to/cvc5-build \
  --z3-source /path/to/z3-source --z3-build /path/to/z3-build
```

The source/build arguments compile small tests against the already-built
cvc5 and Z3 libraries; omit each pair when running only the CLI checks. The
Z3 native test constructs both `Array Bool Proof` and
`Array Bool (Array Bool Proof)` lambda values, then checks exact intrinsic-sort
classification. Each subprocess has a 30-second timeout. The tests compare
complete native outputs only; they do not replace HOL parsing, replay, or
theorem checks.
The Z3 cases retain one-level and nested proof-result closures, a semantic
lambda, a source `&a` collision, and an escaped bar/backslash whose decoded
symbol is checked exactly. The cvc5 collision case uses semantic functions
named `asserted` and `refl` and compares every complete command after exact
scalar expansion.
The cvc5 patch also adds `compact_names_black` to its native unit suite for
the exact scalar boundary, transactional allocation, collision skipping,
lexical compaction, and injected counting/emission stream failures.
