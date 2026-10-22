# Executed fragment assembly comparison

Poly/ML 5.9.2 Release, AArch64. Both selections compiled in fresh private
HOL processes. Production sources and shared simplifier products were not
changed. No timings or benchmarks were run. All temporary source trees were
removed, including those from development attempts.

## Result: five required roots match; merge is not instruction-identical

`evidence/current/manifest.json.gz` records a **validated collection but a
rejected strict equality gate** (`collection_validated: true`,
`strict_equality_accepted: false`, `success: false`). Both paired process
receipts are accepted: seven public-API/reset checks passed on each side,
and their source/path/product audits passed. This is not a failed build or
an unexecuted test, and must not be described as a blanket parity pass.

Baseline is `cccaa27d7099cbadc886983020cbe745db7793f3`; candidate is the
worktree snapshot sealed in the manifest (not an assertion about later
worktree edits). Exact emitted bodies are in the two
`*.sml-assembly.txt.gz` files, sealed both compressed and uncompressed.

| Emitted body, excluding `simpLib.` | Baseline instructions | Current |
|---|---:|---:|
| `ac_ss(1)` | 33 | 33 |
| `SSFRAG(1)` | 59 | 59 |
| `ssf_upd_rewrs(1)` | 22 | 22 |
| `ssf_upd_rewrs(1)(1)` | 60 | 60 |
| `name_ss(1)` | 22 | 22 |
| `name_ss(1)(1)` | 37 | 37 |
| `rewrites(1)` | 37 | 37 |
| `merge_ss(1)` | 184 | **185** |

Except for `merge_ss`, every paired selected body is identical after only
the documented adjacent constant-pool `adrp`/`ldr` operand normalization.
There is no register, record-offset, branch-target, call, allocation-size
or instruction-count normalization in the equality comparison.

### The actual merge difference

The sole additional real instruction is at current offset `0x34`:

```
                 baseline                  current
0x30             blr x16                    blr x16
0x34             adrp x16,POOL_PAGE          mov w1,#1
0x38             ldr x16,[x16,#POOL_OFFSET]  adrp x16,POOL_PAGE
0x3C             blr x16                    ldr x16,[x16,#POOL_OFFSET]
0x40             str x0,[x28,#-8]!           blr x16
0x44             ...                        str x0,[x28,#-8]!
```

A diagnostic alignment of the retained listings confirms that all later
code offsets move by four bytes, and all corresponding in-body control
addresses move by four where their targets follow the insertion. No other
instruction, register, field offset, reservation operand or GC-map content
changes after pool relocation. This diagnostic does **not** alter or bypass
the maintained strict comparator, which retains the original addresses.

| Static merge body property | Baseline | Current |
|---|---:|---:|
| Instructions | 184 | 185 |
| `mov` | 15 | 16 |
| `blr` call sites (including runtime slow paths) | 23 | 23 |
| Inline GC maps | 7 | 7 |
| `?` padding entries | 1 | 2 |
| All listed entries | 192 | 194 |

Every other mnemonic count is unchanged. Heap reservation sites remain
`sub x9,x27,#72`, two `sub x11,x27,#24`, and `sub x9,x27,#16`.
These are static reservation sites, not dynamic allocation totals.
The 72-byte record reservation and its field stores are unchanged.
Thus the two extra listing entries are **one instruction and one padding
entry**, not two instructions and not just padding. There is no extra
local call or reservation site.

The extra instruction materializes the tagged `NONE`/empty value in the
second argument register. Baseline additionally emits two
`merge_names(1)` wrappers (11 instructions each), each containing exactly
`mov w1,#1` at `0x20` followed by a pool-loaded tail branch. Current emits
neither wrapper. This is consistent with moving that argument setup from
a wrapper into its caller. The assembly-only listings do not expose the
literal-pool values/callee identities; this initial collection could not
establish the relationship. The optimized-tree follow-up below resolves
the compiler's named call chain without closure introspection. Strict
equality remains rejected rather than normalizing away or granting an
exception for the real added instruction.

### Helper coverage and limits

All six required roots emit code on both sides. `frag_name`,
`frag_rewrites`, `rewrites_with_names`, both `add_named_rwt` stages,
`named_rewrites`, `named_rewrites_with_names`, `named_merge_ss`, and eight
common nested `merge_names` emissions also compare identically.

There are 34 selected baseline emissions versus 24 current emissions:
23 common bodies match, one common body differs, and ten baseline-only
`merge_names` emissions (the two wrappers plus eight additional nested
emissions) are explicitly reported, never silently discarded. Repeated
compiler names have occurrence keys `@2`, `@3`, etc.; all exact emitted
headers/bodies remain intact. `D` is not independently emitted on either
side and is reported unsupported, possibly inlined, not zero work.
Comparisons of local code cannot establish equal literal contents, callees,
GC behavior, cache behavior, dynamic instructions or runtime performance.

## Controls and validation

- `evidence/unchanged-control/manifest.json.gz`: baseline versus the same
  baseline commit, in two fresh processes. **Pass**: all 34 emitted bodies
  match, both paired receipts pass, strict equality accepted.
- Ten Python unit controls pass: relocation-only changes, preserved field/
  branch/call/allocation operands, extra instructions, unknown/truncated
  pool pairs, separate metadata/padding counts, trace extent, repeated
  specializations, missing required bodies and unpaired helper emissions.
- Final artifact and maintained-input fingerprints were independently
  rechecked against both manifests. No private source directories remain.

The driver writes `manifest.json` for fresh invocations; retained manifests
here are gzip-compressed without changing their contents. Exact listings,
receipts and manifests are compact evidence, not copied build trees.

## Optimized-tree follow-up: named callee relationship resolved

Collected with explicit `--optimized-tree`, only after
`/tmp/task15-logs/fixed-control.exit` existed and no `run_fragments.py`
process remained. No compiler/build process was started during that wait.
Only the private `simpLib.sml` compilation enabled optimized-tree/ICode
printing. Evidence is in `evidence/optimized-tree-current/`; baseline is
the same frozen commit, candidate is the source snapshot in this manifest.

The optimized caller trees state, verbatim:

```
baseline:
  val Local0 (* [] *) =
       FUN "simpLib.merge_names(1)" (FUN "List.map(2)()" (Arg0));

candidate:
  val Local0 (* [] *) = FUN "List.map(2)()" (Arg0);
    val Local1 (* [] *) = FUN "List.foldr(3)()" (Local0, LIT0);
```

The baseline wrapper's complete optimized tree is:

```
fn( Arg0 [_] ) (* "simpLib.merge_names(1)"  1 locals, closure=()
      recursive use=[] *)
    FUN "List.foldr(3)()" (Arg0, LIT0)
```

The final **concrete-register** ICode independently identifies the targets
and the argument materialization (spacing shortened here only):

```
baseline merge_ss:
  FunctionCall CODE "simpLib.merge_names(1)" (X0=X0 ) X0=>X0
baseline merge_names:
  LoadNonAddress 1 => X1
  TailCall CODE "List.foldr(3)()" X30=X30 X0=X0 X1=X1 adjust=0 stackSize=0
candidate merge_ss:
  LoadNonAddress 1 => X1
  FunctionCall CODE "List.foldr(3)()" (X0=X0 X1=X1 ) X0=>X0
```

Thus this is actual compiler-generated caller/callee evidence, not an
inference from closure layouts or matching instruction counts. `LIT0`
in the tree is the tagged value materialized by `mov w1,#1` in native
code: the `NONE` fold seed. The wrapper is absent from the candidate.
Original text, whitespace, all selected passes and line ranges remain in
the sealed `*.optimized-tree.json.gz` artifacts. Useful exact references:

| Record | Baseline stdout lines | Candidate stdout lines |
|---|---:|---:|
| Optimized `merge_ss(1)` | 56298-56456 | 276120-276278 |
| Concrete `merge_ss(1)` | 58092-58210 | 277920-278039 |
| First optimized wrapper | 51456-51458 | not emitted |
| First concrete wrapper | 51475-51479 | not emitted |

### Underlying work, not just the same printed helper name

The retained fold specializations explicitly reference
`"simpLib.merge_names(1)(1)"`: four baseline and two candidate occurrences.
All six have exactly identical final concrete ICode, whose text SHA-256 is
`3c07e9f155ff51abf6132661b2fa9f6ce6a4cd0a82659e56e12a112d425a7d15`.
They recursively fold the list, call that reducer stage and tail-call its
returned closure. All six native bodies are identical under the existing
pool-relocation-only comparison: 29 instructions, one GC map, two padding
entries, no inline allocation reservations. Common emitted reducer bodies
also retain the original strict matches. Optimized-tree usage annotations
can differ; they are preserved, not normalized or claimed equal.

The added caller instruction therefore does **not** represent an extra
fold/reducer operation: its argument setup moved out of a removed wrapper.
On the normal no-stack-growth path, the baseline wrapper executes seven
instructions (`ldr`, `cmp`, `b.cs`, `mov`, `adrp`, `ldr`, `br`); candidate
moves the one `mov` into the caller and bypasses the other six. The fold
and reducer work is unchanged. This resolves the local dynamic-operation
concern; it is not a measurement of total dynamic instructions, allocation,
GC, cache effects or wall-clock performance. Printed names are not a claim
of pointer identity between independently compiled processes.

### Sealing and controls

- The current pair has both receipts accepted and
  `collection_validated: true`, but **`strict_equality_accepted: false` and
  `success: false`**. Merge remains 184 versus 185 instructions, and the
  one-sided helper inventory still rejects strict equality.
- `evidence/optimized-tree-control/` runs the same optional mode with the
  frozen baseline on both sides: both receipts and strict equality pass.
- Enabling printing changes no selected native body/inventory versus the
  prior assembly-only pair after the allowed pool-relocation comparison.
- Fifteen Python tests pass, including opt-in/default CLI behavior,
  private-path/exception switch handling, exact selected text/line ranges,
  repeated ICode passes, padded compiler headers, backend/unrelated-fold
  exclusion, selected fold/native linkage and missing tree/call rejection.
- Source, fixture, tool and shared-product fingerprints were independently
  rechecked for both new manifests. All private trees and intermediate
  development dumps were removed.

Full stdout is deliberately not retained: baseline's 28,408,698 bytes have
SHA-256 `7680c7d07ab03a68599eb832260836f02e5390c3da0a8643d2d82a1bcbe3ab5a`;
candidate's 50,238,152 bytes have SHA-256
`c1f12fb788267a0f5f2c10c85ce476b5630e268fff77f3b08c16882faaf293ec`.
These original full-output seals remain in the accepted receipts, separate
from hashes of compact selected evidence.
