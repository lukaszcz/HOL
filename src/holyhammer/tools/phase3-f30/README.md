# Phase 3 full-corpus F30 gate

This directory contains the tracked TASK11 harness. It runs the frozen
eight-condition F30 matrix as deterministic goal partitions. Each partition
has an initially empty private cache, a hard 600-second worker lifetime, an
append-only journal checkpoint, and an atomic durable copy-back before its
tmpfs state is removed.

The atomic artifact contains the completed journal only. Generated problems,
prover output, and caches are temporary execution state and are never copied
to durable storage. Final compaction retains the independent journal copy and
its atom certificate, then removes the now-redundant artifact copy and logs.

Every corpus theory is bound to a sealed source directory and `.ui`/`.uo`
digest. Workers start on the full HOL heap, change directory only after heap
selection, and turn any theory-load exception into a process failure. The
sealed TASK10-derived goal inventory is also an execution allowlist, so a
later theorem database cannot silently enlarge the measured corpus.

`seal-inputs.sh` creates the immutable run tuple. `run.sh RUN` accepts only
that tuple and resumes incomplete partitions without re-running completed
cells. `fold-result.sh` independently checks exact full-corpus coverage,
every frozen field of canonical and excluded cells, journal uniqueness, the
MeSh gate, and the seen/fresh criteria. The measurement phase stops after its
result and cleanup records are durable. After the service has exited,
`certify-terminal-run.sh` seals its terminal log, changes the copied start
envelope to a hash-bound completed envelope, freezes the verifier, and creates
the final certificate.

`verify-result.sh` dispatches to the run's frozen verifier when one exists.
That read-only bundle includes every project script needed to re-fold the
journals, independently reconstruct the excluded-goal inventory and criterion
(b) report, and validate the terminal and final certificates. It therefore
continues to verify a compacted run from an unrelated or later-mutated source
tree. Final compaction removes redundant artifacts and logs only after a
complete verification; canonical journals, per-atom certificates, the frozen
verifier, and any immutable predecessor-certificate lineage remain durable.

The production service must provide a 32-core quota, 124 GiB memory high,
128 GiB memory maximum, and zero swap. F30 results are evidence only; this
harness has no tuning interface.
