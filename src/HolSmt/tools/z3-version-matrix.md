# HolSmt Z3 Version Matrix

HolSmt supports Z3 proof reconstruction as an evidence-backed compatibility
range, not as an assumption that Z3 proof output is stable.  The verification
tool is:

```sh
src/HolSmt/tools/verify_z3_versions.sh
```

By default it tests representative modern Z3 releases:

```text
4.11.2 4.12.4 4.13.0 4.14.1 4.15.3
```

The tool downloads compatible official release binaries when available, runs
the minimal proof-corpus gate, runs a focused checked nonlinear replay smoke
test, runs `src/HolSmt/selftest.exe`, and writes:

```text
.holsmt-z3-version-matrix/report.json
```

Use `--z3 VERSION:PATH` for a locally installed Z3, for example when GitHub
does not provide a Linux binary for the host architecture:

```sh
src/HolSmt/tools/verify_z3_versions.sh \
  --z3 4.11.2:/home/lukasz/.opam/default/bin/z3
```

To build the representative source releases locally, including the TPTP
frontend, run:

```sh
src/HolSmt/tools/build_z3_versions.sh
```

This installs versioned binaries under `~/.local/bin`:

```text
z3-4.11.2      z3_tptp-4.11.2
z3-4.12.4      z3_tptp-4.12.4
z3-4.13.0      z3_tptp-4.13.0
z3-4.14.1      z3_tptp-4.14.1
z3-4.15.3      z3_tptp-4.15.3
```

## Locally Verified Source Builds

On 2026-06-30 and 2026-07-01, the following source-built Z3 versions were
verified on `Linux-aarch64` using versioned binaries in `~/.local/bin`:

```text
4.11.2  pass  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.12.4  pass  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.13.0  pass  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.14.1  pass  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
4.15.3  pass  proof-corpus gate, nonlinear replay smoke test, TPTP smoke test
```

The proof-corpus and nonlinear replay smoke report was generated with:

```sh
src/HolSmt/tools/verify_z3_versions.sh \
  --versions "4.11.2 4.12.4 4.13.0 4.14.1 4.15.3" \
  --z3 4.11.2:$HOME/.local/bin/z3-4.11.2 \
  --z3 4.12.4:$HOME/.local/bin/z3-4.12.4 \
  --z3 4.13.0:$HOME/.local/bin/z3-4.13.0 \
  --z3 4.14.1:$HOME/.local/bin/z3-4.14.1 \
  --z3 4.15.3:$HOME/.local/bin/z3-4.15.3 \
  --skip-selftest \
  --out-dir .holsmt-z3-version-matrix-source-built
```

The TPTP smoke test was:

```text
fof(ax, axiom, p).
fof(goal, conjecture, p).
```

Each `z3_tptp-<version>` returned `% SZS status Theorem` when invoked with
`-file:<path>`.  Full `selftest.exe` replay is a separate check; nonlinear
real-arithmetic replay requires CSDP to be available.

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

After the replay fix, the proof-corpus plus nonlinear replay smoke verifier
passed for all five source-built versions with:

```sh
src/HolSmt/tools/verify_z3_versions.sh \
  --versions "4.11.2 4.12.4 4.13.0 4.14.1 4.15.3" \
  --z3 4.11.2:$HOME/.local/bin/z3-4.11.2 \
  --z3 4.12.4:$HOME/.local/bin/z3-4.12.4 \
  --z3 4.13.0:$HOME/.local/bin/z3-4.13.0 \
  --z3 4.14.1:$HOME/.local/bin/z3-4.14.1 \
  --z3 4.15.3:$HOME/.local/bin/z3-4.15.3 \
  --skip-selftest \
  --timeout 120 \
  --out-dir .holsmt-z3-version-matrix-source-built-replay-fixed
```

This confirms CSDP is no longer the blocker and that the checked nonlinear
proof-reconstruction smoke case passes across the representative
4.11.2--4.15.x range.  The broad `src/HolSmt/selftest.exe` also exercises
non-proof Z3 oracle paths and is not the canonical version-matrix gate for
checked proof reconstruction.

Report statuses:

```text
pass      The proof-corpus gate and selected HolSmt checks passed.
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
