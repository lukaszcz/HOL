# Recovering the local ordinary baseline costs

This is a **source and codegen argument**, not acceptance by noisy timings.
Pinned develop is `cccaa27d7099cbadc886983020cbe745db7793f3`.
`final-source.json` seals the entire byte-identical `simpLib.sml/.sig`.
The final timing and codegen receipts seal the same selected source inventory,
shared `hol.state0` and dependencies. These are private selected-source runs,
not independently clean-built repositories.

## Source staging (all byte-identical to pinned develop)

| Rows | Source in `src/simp/src/simpLib.sml` | Local baseline work retained |
| --- | --- | --- |
| simp / asm | 915–918 | Original `process_taclist_then` and `NoAsms` construction/application boundary |
| conv | 881–884 | `process_tags` still occurs only when the term arrives; partial construction must not eta-apply it |
| rule / asm_rule | 911–913 | Original `CONV_RULE`, and original per-application hypothesis mapping/append |
| full / rev / both no-strip | 952–984 | Original `GEN_FULL_SIMP_TAC`, direction/drop composition, `mk_require_tac`, `ABBRS_THEN`, per-assumption `SIMP_RULE`, and final `ASM_SIMP_TAC` |
| global / global_req | 993–1017 | Original `psr`, `allasms`, tag processing and local simpset construction inside the existing wrappers; `ReqD rule` remains in measured construction/complete |

`markerLib.sml/.sig` also compare byte-identically against the pin (58,827 /
7,576 bytes; SHA256 respectively
`1e29a10f16d9deea6ec8938241a370c71b7e9bcd8ced3484522e074c5acf6dc0` /
`3bacfdda805a1c3455e6010004c28f1373dbc18d2556b2748b79cba427e7d6ec`).
Those wrappers are shared dependencies, with loaded paths/products sealed by
the receipts. No configured/extension entry point or extension marker is used
by these ordinary workloads. The fixture has two distinct rewrite scenarios,
not a controlled assumption-count slope.

## Native evidence

Commands are in `RESULTS.md`; recheck with `python3 -B evidence/recheck.py`.
Poly/ML 5.9.2 Release, AArch64. Both current and independent baseline-control
collections pass load/proof/source/product gates. Each retains 390 actual
compiler records: 11 optimized-tree, 20 backend-tree, 290 ICode and 69 native
occurrences. Local declaration blocks do **not** emit `fn(...)` optimized trees
for the tactic roots: the collector initially failed closed on that assumption.
The corrected adapter preserves their actual nested `LAMBDA` backend trees.
The failed attempt is archived; no optimized body is invented.

All **53 named simpLib native occurrences**, plus 16 selected library/top-level
occurrences, match after only adjacent `adrp; ldr` constant-pool relocation.
All instruction offsets, branches, field/stack loads, call sites and static
allocation reservations remain. Repeated names/specializations are retained.
For example, `SIMP_CONV(1)` still reserves 40 bytes, its next partial stage 48;
`SIMP_TAC(1)(1)` retains its 24/40/32-byte reservations, `ASM_SIMP_TAC(1)(1)`
40/32; `GEN_FULL_SIMP_TAC(3)(1)(1)` 72; `global_simp_tac(2)` 56/24/24/32.
These are **static sites**, not executed counts or cumulative allocation.
Their exact baseline/candidate bodies and full compiler extents are archived.
`SIMP_QCONV` is inlined/not emitted as a separate optional body on both sides;
its source and caller evidence is retained, not treated as zero work.

Current/control non-native comparison:

- Control: all 321 non-native records exactly equal.
- Current: 316 of 321 exactly equal. One aggregate backend tree and its four
  top-level ICode passes change a single symbolic exported tracking target:
  `Cond_rewr.with_tracking(1)` -> `SimpTracking.with_tracking(1)`. This is the
  `track` export at line 1022, not extra work inserted into an ordinary tactic.
  The differences are retained verbatim, not normalized away.
- Every selected named ordinary tactic/conversion/rule body has unchanged
  local instructions/reservations; there is no added local extension lookup,
  dispatch, extra assumption pass or moved construction stage to charge there.

This recovers the **local** baseline staging costs by retaining the original
implementation and emitted bodies. It does not establish whole-callgraph,
heap-layout, thread-local tracking, dynamic allocation or GC equivalence.
`Cond_rewr.sml` now aliases tracking to `SimpTracking`; the source difference
and actual symbolic target difference are archived. Identical local code is
compatible with different GC costs in its downstream/runtime environment.

## Measurements do not override the limits

`ROWS.md` preserves every row. All CPU/wall/non-GC/user/system family intervals
are unresolved, **not parity**. `no_strip_full_complete.0` is individually
slower for CPU/wall/non-GC. Seven current GC family intervals are slower;
three remain slower in the independent-control contrast. GC's small absolute
share is context, not a waiver. This subtree has not demonstrated cost-parity
acceptance, diagnosed a GC cause, or changed production code to fix it.
