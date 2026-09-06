# Phase 3 S30-v5 paired sample and K witness

This directory is the maintained TASK12 evidence harness.  The owner stopped
the original full-corpus attempt at its next atomic shard certificate after
more than 26 hours.  That run remains endurance and exact-resume evidence; it
does not provide, and this harness forbids claiming, full-corpus S30-v5 totals.

`sample-and-fold.sh` validates the exact fixed-order prefix of completed
atoms, including each atomic journal/certificate pair.  It selects the 3,000
lowest bytewise SHA-256 hashes of goal IDs from that complete 3,119-goal
frame.  Selection uses no outcome or timing field and is sealed before the
Phase 2 join.  It then performs a paired S30-v5/S30-v3 comparison, records a
paired binary-difference 95% confidence interval, retains every sampled loss,
and reports each of the eight new slices separately and by filter.

`run-k-current.sh` invokes the retained seed and replay scripts for the first
128 rows of the sealed hash order.  It populates an initially empty cache with
the exact frozen 24-slice schedule.  `finish-k.sh` takes canonical path, size,
and content-hash snapshots of that real cache immediately before and after
replay and requires byte equality.  In every fresh HOL process its paired
driver explicitly resolves all three prover versions, records those three
probe spawns, and only then resets the in-process counter. It performs a
cache-check pass and, after a second reset, a replay into a second fresh
journal without leaving the process. Both roots must have been absent when
the finishing phase began; neither pass may resume. Each journal must contain
the exact 128-goal subset, 24 cached slice results per row, and exactly zero
post-reset prover spawns.

`certify-final.sh` retains only compact immutable evidence, removes runtime
state, freezes verifier dependencies, and creates the terminal certificate.
`verify-result.sh` independently recomputes source/sample linkage, paired
outcomes and intervals, every loss row, slice/filter aggregates, atom journal
segments, structured terminal records, and K cache decomposition without the
source tree.  It does not mutate the evidence. `safe-remove-state.sh`
canonicalizes and restricts cleanup to one exact TASK12-owned runtime child.
`selftest.sh` checks nonmutation and rejects coherently resealed semantic,
schedule, duplicate-row, atom-segment, cleanup-path, and dependency tampering.

`endurance-runner-reference.sh` is an executable equivalent of the compacted
endurance wrapper.  It computes the real `hhEval.sample_hash` partition set,
accepts the target database's deterministic row order, and requires the
worker journal to contain exactly that set with no duplicate, missing,
cross-theory, or extra row.  Both journal and atom certificate are published
through output-local partial files and atomic renames.  The real HOL adapter
checks a recorded commit with an explicit empty allowed-diff manifest, the
HOL executable and heap, all three provers, all 3,023 compiled runtime
artifacts, all six artifacts for each of 229 target theories, and the host
runtime libraries before and after a controller run.  The exhaustive object
manifest deliberately
over-approximates the transitive theory dependency closure.  The original
untracked wrapper bytes were lost, so no exact-byte reconstruction is
claimed.  A shuffled-order bounded fixture covers restart, membership,
atomic publication, copy-back, and cleanup without launching provers; its
restart cause and status are intentionally not retained.
