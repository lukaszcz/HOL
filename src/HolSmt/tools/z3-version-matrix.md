# HolSmt Z3 Version Matrix

HolSmt supports Z3 proof reconstruction as an evidence-backed compatibility
range, not as an assumption that Z3 proof output is stable.  The verification
tool is:

```sh
src/HolSmt/tools/verify_z3_versions.sh
```

By default it tests the representative supported Z3 releases:

```text
2.19.1 4.11.2 4.12.4 4.13.0 4.14.1 4.15.3
```

The tool downloads compatible official release binaries when available, runs
the minimal proof-corpus gate, runs a checked nonlinear replay smoke test, runs
the full `src/HolSmt/selftest.exe`, and writes:

```text
.holsmt-z3-version-matrix/report.json
```

Use `--z3 VERSION:PATH` for a locally installed Z3, for example when GitHub
does not provide a Linux binary for the host architecture:

```sh
src/HolSmt/tools/verify_z3_versions.sh \
  --z3 4.11.2:/home/lukasz/.opam/default/bin/z3
```

To build the representative modern source releases locally, including the TPTP
frontend, run:

```sh
src/HolSmt/tools/build_z3_versions.sh
```

This installs modern versioned binaries under `~/.local/bin`:

```text
z3-4.11.2      z3_tptp-4.11.2
z3-4.12.4      z3_tptp-4.12.4
z3-4.13.0      z3_tptp-4.13.0
z3-4.14.1      z3_tptp-4.14.1
z3-4.15.3      z3_tptp-4.15.3
```

The verifier downloads the legacy 2.19.1 binary on compatible hosts or accepts
it through `--z3 2.19.1:PATH`.

## Local Source Build Notes

Datatype replay coverage is part of the checked proof matrix.  The datatype
rows are considered passing only when the verifier sees `th-lemma-datatype`
proof-rule evidence, `datatype:<none>` theory-subkind evidence, and the
HolSmt selftest goals for constructor disjointness, injectivity, selectors,
testers, exhaustiveness, acyclicity, mutual families, option constructor
distinctness and lists all complete without oracle tags.  Record and HOL case
syntax coverage remains in the broader selftest suite, but those frontend
forms are not part of the checked datatype proof-replay matrix.

```text
Datatype th-lemma parser/replay     required by record_z3_proof_corpus.py
Datatype symbolic proof shapes      required for Z3 4.11.2 corpus recordings
Datatype native selftests           required by src/HolSmt/selftest.exe
```

On 2026-06-30 and 2026-07-01, the following source-built Z3 versions were
checked on `Linux-aarch64` using versioned binaries in `~/.local/bin`:

```text
2.19.1  not-run     no local Linux-aarch64 legacy binary
4.11.2  incomplete  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.12.4  incomplete  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.13.0  incomplete  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.14.1  incomplete  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.15.3  incomplete  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
```

Those checks did not include the broad HolSmt selftest for every version and
therefore are not a passing version matrix.  A valid version matrix must run
the verifier without suppressing any phase:

```sh
src/HolSmt/tools/verify_z3_versions.sh \
  --versions "2.19.1 4.11.2 4.12.4 4.13.0 4.14.1 4.15.3" \
  --z3 2.19.1:$HOME/.local/bin/z3-2.19.1 \
  --z3 4.11.2:$HOME/.local/bin/z3-4.11.2 \
  --z3 4.12.4:$HOME/.local/bin/z3-4.12.4 \
  --z3 4.13.0:$HOME/.local/bin/z3-4.13.0 \
  --z3 4.14.1:$HOME/.local/bin/z3-4.14.1 \
  --z3 4.15.3:$HOME/.local/bin/z3-4.15.3 \
  --out-dir .holsmt-z3-version-matrix-source-built
```

The TPTP smoke test was:

```text
fof(ax, axiom, p).
fof(goal, conjecture, p).
```

Each `z3_tptp-<version>` returned `% SZS status Theorem` when invoked with
`-file:<path>`.  Nonlinear real-arithmetic replay requires CSDP to be
available.

A full verifier run on the source-built `z3-4.11.2` binary completed the unit
tests and then reported:

```text
4.11.2  blocked  selftest-dependency  CSDP not found
```

The blocked phase was the nonlinear real replay dependency, not Z3 version
detection or proof parsing.

## Post-CSDP Local Checks

On 2026-07-01, after installing `coinor-csdp` (`csdp` 6.2.0 at
`/usr/bin/csdp`), the focused SOS/CSDP selftest passed:

```sh
Holmake -C src/real selftest_sos.exe
(cd src/real && timeout 600 ./selftest_sos.exe)
```

The Z3 proof-corpus gate still passed for all five source-built versions:

```text
4.11.2  pass
4.12.4  pass
4.13.0  pass
4.14.1  pass
4.15.3  pass
```

The previous nonlinear replay dependency case,
`(x:real) pow 3 = x * x * x`, was then tested directly with `Z3_TAC`.
Before the zero-factor arithmetic replay fast path, source-built Z3 4.11.2
timed out after 300 seconds while checking the Z3 proof:

```text
4.11.2  timeout after 300s while checking the Z3 proof  (before fix)
4.12.4  pass
4.13.0  pass
4.14.1  pass
4.15.3  pass
```

After the replay fix, the proof-corpus plus nonlinear replay smoke checks
passed for all five source-built versions, but that run still did not include
the full selftest and is not a passing version matrix.  The required command is:

```sh
src/HolSmt/tools/verify_z3_versions.sh \
  --versions "2.19.1 4.11.2 4.12.4 4.13.0 4.14.1 4.15.3" \
  --z3 2.19.1:$HOME/.local/bin/z3-2.19.1 \
  --z3 4.11.2:$HOME/.local/bin/z3-4.11.2 \
  --z3 4.12.4:$HOME/.local/bin/z3-4.12.4 \
  --z3 4.13.0:$HOME/.local/bin/z3-4.13.0 \
  --z3 4.14.1:$HOME/.local/bin/z3-4.14.1 \
  --z3 4.15.3:$HOME/.local/bin/z3-4.15.3 \
  --out-dir .holsmt-z3-version-matrix-source-built-replay-fixed
```

This command must pass every requested Z3 version.  If the broad selftest fails
for any version, the matrix status is failed or blocked and the support claim
must say so explicitly.

Report statuses:

```text
pass      The proof-corpus gate, checked replay smoke test and full HolSmt
          selftest passed.
fail      HolSmt ran and exposed a parser/replay/version incompatibility.
blocked   A local prerequisite is missing, such as CSDP for nonlinear real
          arithmetic replay.
not-run   The tool could not obtain a compatible Z3 executable.
error     The configured executable or test harness setup was invalid.
```

Broad support claims should cite the generated report and list the exact
versions that passed.  Expanding the supported range requires adding
representative versions to the default list and checking in any parser/replay
fixes needed for the matrix to pass.
