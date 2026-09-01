# Phase 3 anchor and preflight harness

This directory contains the maintained source for the bounded Phase 3 anchor
derivation harness. `freeze-runtime.sh` is the only supported way to stage
runtime tools into an immutable run-input directory. It records the tracked
origin and SHA-256 of every staged file; `runtime-inventory-selftest.sh`
rejects a staged runtime whose bytes no longer equal its tracked source.

The six `Holmakefile-*` files are explicit heap-selection templates for the
two certified historical execution states. The current checkpoint runner
keeps all eight profiles for a goal atomic, binds every durable checkpoint to
the target model and runtime inventory, uses a hard ten-minute atom bound,
and limits heavy HOL atoms with eight advisory-flock slots across the
16-worker scheduler.

The two `refresh-overlay-*` tools mechanically stage and rebuild the current
tracked Phase 3 source closure in each certified historical host.  They update
the immutable source/object hashes only after the exact allowlist has built.

Generated corpus, historical-object, and run-result evidence is deliberately
not source. It belongs under a single ignored evidence root and must be
independently hash-bound by the immutable run inventory.
`seal-inputs.sh` records the tracked runtime provenance and relevant main-tree
diff, rejects symlinks, writes the complete input inventory, rechecks it, and
only then makes the staged directory immutable.

`cross-tuple-certificate.sh` binds both tuple headers and inventories, the
exact challenger command and diagnostic, and the runner/verifier hashes while
proving that the accepted directory, state, and invocation log did not
change. `certificate-selftest.sh` exercises this rejection certificate and
the final-acceptance binding hermetically.
