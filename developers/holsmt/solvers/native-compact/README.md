# Native compact certificate producers

This directory retains the reviewed native producer patches, pinned source
identities, and conformance tests.  HOL's Z3 driver selects the compact typed
parser and native printer option only for the explicit replacement version
`4.11.2.0-holsmt-compact-prototype2`.  Ordinary Z3 versions retain the legacy
proof format.  The cvc5 patch remains producer evidence for later semantic FP
component integration; the HOL cvc5 driver does not enable compact output.

The Z3 patch includes a subsequently found quoted-symbol lexical repair and
an explicit proof-result closure category.
The initial measured binary mishandled escaped bars inside quoted identifiers;
`tests/z3-escaped-symbol.smt2` retains that semantic token regression. The
patch now handles escaped bars/backslashes in both reservation and output.
The corrected build passes the escaped-symbol token comparison and produces
a byte-identical canonical Agreement certificate at the size reported below.
The final executable identity is recorded with the measurements below.

Both printers traverse the existing native proof twice. The first traversal
reserves printed identifiers and counts actual reference emissions into a
discard stream. The second emits fresh frequency-ranked names through a lexical
whitespace writer. Neither pass materializes an oversized legacy certificate
for a downstream normalizer. The solver input, proof schedule, premises,
conclusions, scoped assumptions and metadata remain the native printer's input.

cvc5 also shares closed scalar literals when the measured reference saving
strictly exceeds the complete compact definition and reference cost. Rejected
scalar candidates do not consume an alias; names already reserved by the proof
or bundled EO signatures remain permanently skipped. The counting and emitting
streams propagate failures before allocation or successful return. In compact
Z3 output, `@` identifies Proof, `&` identifies one-or-more function/array
domains ending in Proof, `$` identifies Boolean terms, and `?` identifies
other semantic terms. Classification uses the intrinsic native sort only.
Both options default to off.

The cvc5 patch additionally repairs six FP component constructors that discarded
their operand. Their EO declarations now carry that operand too. This makes
origin information available; a HOL adapter must still interpret and prove the
full component semantics. EXPONENT and SIGNIFICAND are SymFPU's normalized
unpacked components, not raw IEEE field extracts.

## Source pins and builds

Use official release source archives from the corresponding repository tags.
Verify the archive hash before extraction or patch application:

| Source tag | Archive SHA-256 |
| --- | --- |
| Z3 `z3-4.11.2` | `e3a82431b95412408a9c994466fad7252135c8ed3f719c986cd75c8c5f234c7e` |
| cvc5 `cvc5-1.3.4` | `40e7a0d311ebd583972f412701a0f4bc325632bab74ca25f407b3acbb66db44e` |

From each extracted source root, apply the corresponding patch with `patch -p1`.
Build out of tree, using the project's normal bounded process wrapper:

```sh
cmake -S z3-source -B z3-build -DCMAKE_BUILD_TYPE=Release \
  -DZ3_BUILD_LIBZ3_SHARED=OFF -DZ3_BUILD_TEST_EXECUTABLES=ON
cmake --build z3-build --target shell libz3 -j1

cmake -S cvc5-source -B cvc5-build -DCMAKE_BUILD_TYPE=Production \
  -DENABLE_GPL=ON -DENABLE_AUTO_DOWNLOAD=ON
cmake --build cvc5-build --target cvc5-bin -j1
```

cvc5's source build pins its dependency revisions/hashes. Its GPL/auto-download
settings match the measured build, including LibPoly. Record compiler,
dependency, executable and shared-library identities alongside measurements;
the source recipe does not promise identical binary hashes across toolchains.

Explicit native version labels:

- Z3: `4.11.2.0-holsmt-compact-prototype2`.
- cvc5: `1.3.4-holsmt-compact-prototype2`.

Enable only the native output option, retaining the existing query and proof
configuration:

```sh
z3-build/z3 -t:30000 proof=true pp.simplify_implies=false \
  pp.compact_proof_names=true -smt2 emitted.smt2

cvc5-build/bin/cvc5 --tlimit-per=30000 --produce-proofs \
  --proof-format-mode=cpc --proof-granularity=dsl-rewrite \
  --proof-compact-names --fp-exp --sets-exp --lang smt emitted.smt2
```

Keep HOL's 16 MiB raw certificate gate before parsing. A compact native stream
still needs bounded tokens, edges, nesting, literal sizes and live graph state.
Renaming is syntax preservation, and scalar definitions are term sharing;
neither establishes a theorem. HOL must reconstruct the admitted certificate
and check its exact conclusion, hypotheses and oracle tags.

## Measured prototype gates

| Input | Legacy bytes | Compact bytes | Complete comparison |
| --- | ---: | ---: | --- |
| Exact emitted word32 Agreement | 20,745,951 | 13,049,403 | 3,761,683 tokens; injective typed reference renaming |
| Small variable-mode FP | 610,191 | 473,910 | 9,819 commands / 141,989 tokens; renaming + exact scalar expansion |
| Strong variable-mode positive FP | 23,040,748 | 13,269,637 | 25,273 commands / 3,693,462 tokens; same comparison |
| Strong variable-mode negative FP | 22,777,678 | 13,121,607 | 25,301 commands / 3,650,287 tokens; same comparison |

All compact streams have over 20% byte headroom against 16 MiB. The Z3 compact
dialect is integrated behind its exact prototype version label and the
Agreement stream has passed direct typed parsing and checked HOL replay. The FP
measurements remain producer evidence: the cvc5 compact dialect still awaits
the semantic component adapter and is disabled in the HOL driver. The FP inputs
are the preserved strong natural public-is_finite probes, and are separately
hashed from historical inputs.

The final-source Z3 executable has SHA-256
`b3b935d3afd31d7d6e494426df78c5bfdb0523b84e0560e791f29a3addc683f3`.
The final Agreement output remains byte-identical to the earlier compact
output, with SHA-256
`4048af60d919a17c4282e7e513124ea771bf21ced7098f55173d3d66f1e26064`.

The final-source cvc5 binary has SHA-256
`7f7b5f0323fbfe7dd735e4d1d60e349afe15e52a52ae451e529564f8ec296527`.
The changed shared library `libcvc5.so.1.3.4`, which carries the serializer,
has SHA-256
`dd63f205ceb85e6bb559cc9f7bb98229dc7dfddc95b48773700093a8e0fab3b0`.
The three final compact outputs have SHA-256 values, in table order,
`07beeec2dfc89edde915d03dfbad157b78ba43990563f843488ab6fe117af073`,
`0e7815c30a3a3d5fe8a2768973512d6050733332b2d43ae2aa6ba8464f0ad60e`,
and `7ef00b56638a049a3517d289f16e145875668e07487c87977f5b92e45bb1a998`.
The independent binder/quoted-symbol fixtures also preserve every compared
command and token. The pinned Ethos checker reports `correct` for those two
fixtures and `incomplete` for the earlier small FP certificate, which contains
trust steps. Ethos was not rerun after the scalar accounting repair. Its full
strong positive check reached a separate 45-second cap; completion and complete
parsing are not claimed.

## Automated tests

The cvc5 patch adds `compact_names_black` to `test/unit/printer`. It covers the
exact six/seven-use negative-rational boundary, transactional alias allocation,
reserved-name skipping, lexical compaction, and injected counting/emission
stream failures. `tests/run_native_compact_tests.py` adds bounded public-CLI
coverage for both patches: option-off identity, quoted and rule-like symbols,
injective fresh names, repeated complete cvc5 printing, local DAG mode,
distinct FP-component operands, proof-result closures, semantic lambdas,
source-name collisions, and complete token/scalar equivalence. See
`tests/README.md` for the command.

The patch files, pins, build commands and automated tests in this directory are
the reproducible shipping record.  Preserve the reviewed patch bytes when
updating parser or driver integration, and independently review any producer
change together with its version selection and negative conformance tests.
