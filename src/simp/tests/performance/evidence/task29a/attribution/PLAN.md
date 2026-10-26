# TASK29A fail attribution — predeclared before any observation (2026-10-26)

Question: are the four grid fails (frag_create-10000, frag_named-10000,
frag_named_rules-1, frag_named_rules-10) a cost of the candidate's ordinary
path? Production simpLib.sml is byte-identical to develop; the fragment
constructors never call Cond_rewr. The only ordinary-path source difference
is Cond_rewr's tracking moved to a separate SimpTracking module (plus two
Cond_rewr.sig exports).

Runs (task29a_grid.py run --only, 20 pairs, 5 samples, policy v2), in order:
- R1 reproduce: candidate 6f62229c0, the four cells, predeclared counts.
- R2 probe: candidate 8d4a84417 (Cond_rewr.sml = develop byte-for-byte,
  note_rewrite exported, Cond_rewrExt reports to Cond_rewr, no SimpTracking),
  the four cells, predeclared counts.
- R3 count: candidate 6f62229c0, frag_named_rules-1/-10 at half the
  predeclared count (the historical self-selected counts).
Reading: R1 fail & R2 pass => the extraction is the cause (repair).
R1 pass => the grid fails were not reproducible. R3 pass with R1 fail =>
count-dependent. Every result is reported; none is a grid decision.

## R4 — layout randomization (predeclared 2026-10-26, before any R4 data)

R1–R3 results: fails reproduce (R1); the develop-Cond_rewr probe passes
rules-1/-10 but fails create/named worse (R2); rules-10 still fails at half
the count (R3). Code-area size at batch start tracks speed, including in
develop/develop processes, so the hypothesis is a code-layout artefact.

R4: harness commit 3ef5b380b, candidate 6f62229c0, --layout-seed
task29a-r4, 20 pairs, 5 samples, predeclared counts; the four failing cells
plus frag_record-0 (passed in the pilot) as a sanity cell.
Reading: if the four cells stop failing (pass or inconclusive with the
candidate CI covering 1) while frag_record-0 still passes, layout explains
the fails, and the full grid is rerun with a fresh predeclared seed. If any
of the four still fails, it is a real cost under randomized layout. All
results are reported; none is a grid decision.
