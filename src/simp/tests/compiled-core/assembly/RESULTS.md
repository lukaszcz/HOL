# TASK16: emitted local compilation work

## Result

Both `evidence/current/manifest.json` (pinned versus worktree) and
`evidence/control/manifest.json` (pinned versus pinned) passed collection,
source/load provenance, fixture checks, and native comparison on AArch64,
Poly/ML 5.9.2 Release. Pinned revision:
`cccaa27d7099cbadc886983020cbe745db7793f3`.

* Private `simpLib.sml` **and** `simpLib.sig` match the pin byte-for-byte on
  both sides; this is asserted before building each private launcher.
* All **31 selected simpLib native bodies** match after the narrow adjacent
  ADRP/LDR pool-relocation normalization. This preserves offsets, branch
  targets, field/stack operands, registers, calls, reservations and padding.
* The extended comparison includes **43 native bodies**, adding compiler
  library specializations and top-level initialization. All 43 match in both
  inspections: no instruction, reservation, call, or emission-count delta.
* All **29 selected optimized trees** match exactly. Of **18 backend trees**
  and **210 ICode passes**, only one backend tree and four top-level ICode
  passes differ in the current pair. Each difference is the binding below.
  In the pinned control, every non-native compiler record matches exactly.
* Raw native records differ in 35 current-pair bodies and 36 control-pair
  bodies. These differences are retained, not erased from the evidence;
  their normalized forms match. Pool addresses do **not** prove equal pool
  contents. The exact trees/ICode identify the visible binding change.

No timings, runtime allocation measurements, closure introspection, or
production edits were used. These are private-source compilations sharing
sealed heap/dependency products, not two complete repository builds.

## Source-tied local work

Source: `src/simp/src/simpLib.sml`; exact source spans are embedded in each
manifest and full private source bytes are archived. Counts below are equal
baseline/candidate. Calls include emitted slow/error/tracing-path calls;
these are static body counts, not dynamic execution counts.

| Source/helper, emitted suffix | Instructions | Calls | Reservation immediates (bytes) |
| --- | ---: | ---: | --- |
| `++` (646–682), `(2)` | 336 | 32 | 32,24,24,32,24,24,64,24,16 |
| `++`, `(1)` | 12 | 1 | none |
| `mk_rewr_convdata` (65–86), `(2)` | 375 | 26 | 16,24,16,24,16,32,40,24,16,24,24,24,24,24,24 |
| its `(2)(1)` trace closures, occurrence 1 / 2 | 89 / 91 | 3 / 3 | none |
| `appconv` (53–62), `(2)(1)` | 26 | 2 | 40 |
| its `(2)(1)(1)` | 28 | 2 | 48 |
| its `(2)(1)(1)(1)` bounded body | 52 | 4 | none |
| `USER_CONV` (350–367), `(4)` | 362 | 7 | 72 |
| its `(4)(1)` / `(4)(1)(1)` | 36 / 38 | 2 / 2 | 80 / 88 |
| its `(4)(1)(1)(1)` | 278 | 22 | 13 sites; exact operands in manifest |
| `mk_named_rewrs` (629–639), `(3)` | 75 | 7 | 24,24 |
| its `reduce(6)`, **each of two emissions** | 202 | 8 | 24,16,24,24 |
| `mk_ac` (381–389), `(2)` | 303 | 24 | 24,16,24,24,24,24,24,24,24,24,24 |
| AC `List.foldr(3)()`, each of two emissions | 22 | 2 | none |
| net `List.foldr(3)()`, each of three emissions | 97 | 7 | 24,24,24,24 |
| rewrite `List.mapPartial(2)()`, each of three emissions | 45 | 4 | 24 |
| `SSFRAG` (109–114), `(1)` | 59 | 4 | 72 |
| `ssf_upd_rewrs` (117–124), `(1)` / `(1)(1)` | 22 / 60 | 2 / 3 | 24 / 72 |
| `fupdlimit` (402–406), `(1)(1)`, occurrence 1 / 2 | 36 / 26 | 3 / 2 | 16,64 / 64 |
| `limit` (408), `(1)` | 22 | 2 | 24 |
| initial `empty_ss` maker, emitted `empty_ss-(1)` | 21 | 2 | 24 |
| final `<top level>` initialization (whole structure) | 1050 | 53 | all 47 sites retained |

A reservation list describes static `sub xN,x27,#N` sites, **not** a sum
allocated by an invocation. Callee work, loop iterations and GC behavior
cannot be recovered from this table. Duplicate specializations are counted
and archived separately, not deduplicated or multiplied into a runtime cost.

### Inlined helpers and constructors

`net_add_conv` (371–375), `net_add_convs` (377–378), and `ac_rewrites`
(391) have no standalone named native bodies in either side. They are not
reported as zero work:

* `++(2)`'s optimized tree folds the AC list through specialized
  `List.foldr(3)()` calling `simpLib.mk_ac(2)`; rewrite conversion filtering
  uses specialized `List.mapPartial(2)()` calling `mk_rewr_convdata`.
* The specialized net fold contains the key/NONE branches, invokes
  `USER_CONV(4)`, builds the net payload and invokes `Ho_Net.net_update(3)`.
  The exact emitted optimized fragment is identical on both sides:

  ```sml
  val Local11 (* [] *) =
     FUN "simpLib.USER_CONV(4)"
           (Local3[0], Local3[1], Local3[2], Local3[3]);
  val Local12 (* [] *) = TUPLE(Local6, Local11);
  val Local13 (* [] *) = TUPLE(Local12, Local4);
  val Local14 (* [] *) = TUPLE(Local8, Local10);
  val Local15 (* [] *) = DATATYPE(Local14, LIT0)
  in
    FUN "Ho_Net.net_update(3)" (Local13, Local15, Local2)
  ```

* `ssupd_net`, `unlimit`, `split_name`, and `option_cases` also lack separate
  named bodies. `fupdlimit` has two differently specialized emitted bodies;
  neither occurrence is discarded.
* `empty_ss`, `empty_ssfrag`, `empty_excluded`, and datatype constructors
  `SS`, `SSFRAG_CON`, `ADDFRAG` are not standalone named bodies. Their source
  definitions and whole-structure initialization are retained, alongside
  constructor uses in emitted trees. There is no asserted per-constructor
  instruction cost, and initialization's 1050 instructions must **not** be
  attributed solely to the empty values. `empty_ss-(1)` is the emitted
  initial rewrite-maker function, not construction of the complete value.

## Mechanical tracking attribution

The archived `Cond_rewr.sml` source diff is precisely removal of its private
thread-local tracking implementation in favor of aliases to `SimpTracking`.
The candidate tracking source is also archived. The compiler does **not**
turn that source change into a local extra call/reservation in the selected
compilation functions: their optimized trees and native bodies agree.

The one selected backend-tree change is:

```diff
-    FUN "Cond_rewr.with_tracking(1)",
+    FUN "SimpTracking.with_tracking(1)",
```

The same change appears in four successive final top-level ICode passes,
for example (pre-register assignment):

```diff
- LoadAddress FUN "Cond_rewr.with_tracking(1)" => R216
+ LoadAddress FUN "SimpTracking.with_tracking(1)" => R216
  StoreConstOffset64 R216 => [R212+512]
```

Final register assignment retains destination `X3` and field offset 512 on
both sides. This is a changed exported function constant, **not** proof of
equal function identity. Final native initialization remains equal modulo
pool relocation. No tracking implementation body, transitive Cond_rewr
runtime cost, or process-wide allocation equality is inferred from this.

## Reproduction and evidence

Commands are in `README.md` and each manifest. Both runs completed with all
seven public fixture checks and the complete observation. The fixture uses
named maker expansion, shared bounded allowance, keyed/unkeyed conversions,
empty addition, persistence, limit/updaters, and AC compilation.

`python3 -m unittest discover -s src/simp/tests/compiled-core/assembly`:
**10 tests passed**, including nonrelocation sensitivity, duplicate bodies,
nested optimized lambdas, specialized library bodies, missing-tree rejection,
strict-failure acceptance boundaries, source spans, archive hashes and exact
stdout ranges. Original fragment assembly parser controls: **15 tests
passed**. Raw test output: `tests.log`.

Each side retains compressed raw full compiler extent (~28 MB uncompressed),
selected exact native code, selected exact compiler records, private source
bytes, build receipt and validated run receipt. Manifests retain source,
fixture, collector, tool and shared-product seals plus exact diffs. The full
extent preserves unselected initialization/anonymous code without pretending
it has a precise per-helper attribution. Temporary build roots and failed
exploratory output were removed; no commit was made.
