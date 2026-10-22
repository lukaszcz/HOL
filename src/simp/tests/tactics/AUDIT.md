# TASK18 ordinary tactic source boundary

Reference: develop `cccaa27d7099cbadc886983020cbe745db7793f3`.
At this audit, the **entire bytes**, including comments/whitespace, match that
reference for all four files below; no production edit is needed or made.
TASK16's mechanical whole-file restoration already restored these bodies.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `src/simp/src/simpLib.sml` | 44419 | `ee324439ac66cd14858d6ea5dc45a867d44fa6762298f1cf7df45b13aed6c3cd` |
| `src/simp/src/simpLib.sig` | 10369 | `d1979668da105341e6e97e900848a2d382eaac3a50650c89bbdeae8ee3689666` |
| `src/marker/markerLib.sml` | 58827 | `1e29a10f16d9deea6ec8938241a370c71b7e9bcd8ced3484522e074c5acf6dc0` |
| `src/marker/markerLib.sig` | 7576 | `3bacfdda805a1c3455e6010004c28f1373dbc18d2556b2748b79cba427e7d6ec` |

## Exact baseline bodies (reference/current line numbers coincide)

All ranges below are in `src/simp/src/simpLib.sml` unless stated otherwise.
These identify the actual bodies, not API-equivalent replacement wrappers.

| Lines / bodies | Preserved composition and behavior |
| --- | --- |
| 797–802 `Cong/AC/Excl/ExclSF/Req0/ReqD` | Direct generic-marker aliases, no extension classifier. |
| 806–879 `frag_of`, `SF`, `tactic_only`, `process_tags` | Ordinary directive vocabulary; ordered fold/removal/Cong-AC/force-add/deletion. Requirements reject at conversion/rule level; assumption policies, Abbr and labels are dropped there. No Split/ExclX dispatch or rejection scan. |
| 881–896 `SIMP_CONV`, `SIMP_PROVE`, `&&` | Process tags when called, then direct QCONV/proving/ordinary rewrite installation. No strategy/prepared companion. |
| 911–919 rules, ASM/SIMP, lower-case aliases | ASM uses generic `process_taclist_then`; SIMP prepends NoAsms. Direct ASM/SIMP requirement wrappers are intentionally application-time, unlike full/global. |
| 936–949 `BF_ASSUME_TAC`, `caa_tac0` | Front/back insertion, contradiction/accept/assume, optional true dropping; no solver fallback. |
| 952–984 local `caa_tac`, `STRIP_ASSUME_TAC'`, `drop`, `GEN_FULL_SIMP_TAC`, all six full variants/aliases | Sequential `SIMP_RULE` assumption fold; full and reverse use opposite fold/drop direction. Abbr preprocessing composes during construction; requirements compose outside the full tactic. No-strip variants retain disjunctions. |
| 986–1000 `stdcon`, `psr`, `allasms` | Optional substitution/strip, oldest-vs-newest pop, exactly original assumption-count iterations. No extension loops or strategy inspection. |
| 1002–1016 `global_simp_tac` | `mk_require_tac (ABBRS_THEN (LLABEL_RES_THEN ...))`; requirement diagnostics and Abbr partition early; label resolution, tags/fragment lookup and assumption iteration late. Finish with ordinary ASM. |

Generic `src/marker/markerLib.sml` remains unchanged:

- 120–144: `req0_modify`, `reqD_modify`, `mk_require_tac`. Each list item
  restarts from original `tac`, not accumulated checks; Req0 then ReqD stripping.
  Preserve the list quirk (even discarded wrappers print/infer/throw).
- 320–324: `ABBRS_THEN` partitions/extracts at construction but expansions run
  on goals. 467–477: `LLABEL_RES_THEN` resolves in assumption order and silently
  omits missing labels, unlike direct ASM's `process_tacoption` error.
- 673–785: `dest_directive` reports requirement wrappers before bounds/head;
  `dest_tacmarked`/option processing/filtering preserve original policy;
  `process_taclist_then` decodes at application, then pretactic/filtering and
  `mk_require_tac`. It has no recursive extension entry point.

## Explicit extension boundary

`src/simp/src/simpMarkerLib.sml`: `strip_wrappers` (27–32), accumulating
`require_split` (41–56), and `process_taclist_then_recur` (138–151) belong to the
explicit extension module. Its recur closure filters fresh goal assumptions
with saved policy and stripped arguments, without repeating Abbr pretactics.
This is **not** develop's ordinary `markerLib.mk_require_tac` list behavior.
Existing `tests/markers/selftest.sml` already checks recursion stripping,
accumulated requirements, once-only Abbr, and re-filtering after new facts.
Do not migrate that implementation or its semantics into ordinary markers.

`simpExtLib.gen_simp_tac_with_xdata` (2509–2541) alone invokes that recursive
marker path, compiles invocation xdata, applies configured solver/looper tactics,
and bounds looper rounds; explicit GEN_SIMP_TAC/child-first APIs select it.
Split/ExclX/configured strategies stay there (TASK20). Ordinary supplemental
coverage checks recursive wrapper payload inspection and saved-tactic reentry,
not extension looper execution. The isolated ordinary runner rejects any loaded
Ext/ExtLib/simpMarker/split module, including indirect loads.

## Behavioral ownership

`selftest.sml` adds 307 checks / 116 real validation calls per selection:
all direct/full aliases, full-vs-reverse assumption dependency propagation,
ordered disjunctive branches vs no-strip, contradiction, public psr/allasms
configuration, rule/conversion/proving hypotheses and directive rejection,
nested Req0/ReqD/Once payloads, changing-assumption reentry, and early-full vs
late-direct printer/exception stages. Native validator controls reject wrong
conclusion, foreign hypotheses, oracle tags and reversed branch order.

TASK05's sealed fixture/matrix remains authoritative for global construction,
exact inference/callback counts, saved grammar/context, dropped requirements,
late/missing labels/fragments/Abbr and malformed/bounded arguments. No frozen
expectations are regenerated. Its strict baseline run remains a separate gate.
Source equality is not by itself runtime, performance or fresh-load evidence;
this suite uses source snapshots and common shared dependencies, not independent
clean repository builds. The normal `ordinary-tactics` target now runs this supplemental pair and the
strict original/expanded staging suite at selftest level 1. The measured
performance matrix, native correspondence and separate GC investigation are in
`performance/evidence/`. Final bounded acceptance and uncertainties are in
`../compatibility/TASK_18_HANDOFF.md`; no ordinary body or generic service was
changed by TASK18.
