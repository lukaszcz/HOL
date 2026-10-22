# TASK12 application assembly follow-up

Read-only inspection of the retained Poly/ML 5.9.2 AArch64 listings in
`../evidence/task12-allocation/{baseline,candidate}-assembly.log.gz`.
Both compressed-log SHA-256 seals were checked against `manifest.json`.
This analysis performed no builds, fixture executions, or timing runs.
A final allocation-only rerun (after making the runner default to HEAD)
seals this note too and reproduces the same listings/graph results.

## The four entries really are instructions

For `Cond_rewr.COND_REWR_CONV(3)(1)(1)(1)`:

| 32-bit listing entries | Baseline | Candidate | Delta |
|---|---:|---:|---:|
| Machine instructions | 805 | 809 | +4 |
| Inline GC register maps (`[x…]`, including `[]`) | 36 | 36 | 0 |
| Trailing zero (`?`) | 1 | 1 | 0 |
| Total | 842 | 846 | +4 |

The literal pool itself is outside these listed entries. Five register
maps change contents, not size. The complete mnemonic-count delta is
`adrp +5, ldr -3, str +4, stp -2`; all other counts are unchanged.
Thus neither “four extra executed instructions per rewrite” nor “only
metadata/padding” describes the result.

## Compact normalized diff

Normalization removes listing addresses, branch/literal addresses, and
PC-relative pool offsets (the `ldr` following `adrp`). Capture offsets
are treated as field identities, not extra work. The following uses
symbolic register roles to suppress tracking-update register renaming;
`ENV` is the application closure, `KEY` the thread-local tracking key,
and `TAG` the existing stored-value tag. Offsets below are hexadecimal
and relative to the application function, baseline -> candidate.

1. TLS lookup probe, `9A0 -> 9A0`, and TLS update probe,
   `B74 -> B78` (same replacement at both sites):

   ```diff
   - ldr  env,[stack,#48]
   - ldr  key,[env,#72]
   + adrp key,POOL_PAGE
   + ldr  key,[key,#KEY_LITERAL]
   ```

   Two instructions become two; **two loads become one load**. This is
   loading the constant key from the code object's literal pool, not
   loading a tracking-function alias and calling through it. The ordinary
   TLS lookup/update and their `ldar` operations already existed.

2. Found-key validation, `9D0 -> 9D0`:

   ```diff
   - ldr  key,[env,#72]
   + adrp key,POOL_PAGE
   + ldr  key,[key,#KEY_LITERAL]
   ```

   **+1 instruction (`adrp`), unchanged load count.** The following
   comparison/error branch is unchanged except for its shifted location.

3. Update an existing TLS entry, `BA0..BE0 -> BA4..BEC`:

   ```diff
   - ldr  key,[env,#72]          // before allocation check
     ... allocate same 40 bytes; fill same value fields ...
     adrp tag,POOL_PAGE
     ldr  tag,[tag,#TAG_LITERAL]
   - stp  key,tag,[node,#0]
   + str  tag,[node,#8]
   + adrp key,POOL_PAGE
   + ldr  key,[key,#KEY_LITERAL]
   + str  key,[node,#0]
     stlr node,[entry]
   ```

   **+2 instructions**: the key load gains an address instruction and
   one paired store becomes two stores. Allocation/check/call counts do
   not increase. Key materialization moves after the allocation check,
   so the corresponding GC register map also shrinks.

4. Insert a new TLS entry, `BE4..C24 -> BF0..C34`:

   ```diff
     ldr  thread,[runtime,#64]
   - ldr  env,[stack,#48]
   - ldr  key,[env,#72]
     ... allocate same 40 bytes; fill same value fields ...
     adrp tag,POOL_PAGE
     ldr  tag,[tag,#TAG_LITERAL]
   - stp  key,tag,[node,#0]
   + str  tag,[node,#8]
   + adrp key,POOL_PAGE
   + ldr  key,[key,#KEY_LITERAL]
   + str  key,[node,#0]
   ```

   **+1 instruction**: two removed loads balance `adrp; ldr`, but the
   store is split. The following 16/24-byte allocations and TLS-list
   publication retain their instruction counts, with register renaming
   and changed GC maps.

Net static code growth: `0 + 0 + 1 + 2 + 1 = 4`. These are all remaining
application instruction-shape differences after normalization; exception
paths otherwise have only relocated literals/targets. There is no new
`note_rewrite` call: the tracking logic remains inlined.

## Successful nontracking execution is not one path

The existing `null stack` guard is at `958..964`. A nonempty stack skips
tracking entirely. With an empty stack, TLS lookup starts at `968` and
walks entries from `990`. Its empty-list exit is `A20 -> A24`; a found
key goes through validation at `9CC`, then reads the saved option.
`NONE` rejoins the normal final trace/return at `AAC -> AB0`.

| Successful case, tracking off | Added instructions in this body |
|---|---:|
| Nonempty rewrite stack: skip `note_rewrite` | 0 |
| No entry for this tracking key, including untouched thread | 0 |
| Existing tracking-key entry whose saved value is `NONE` | +1 `adrp` |

Each visited TLS entry replaces the two-load probe with `adrp; ldr`:
there is no added ordinary-path load; there is one fewer load per probe.
The existing-key case's extra address instruction is real even though
tracking is off (for example, after a tracking extent restores `NONE`).
The update blocks are tracking-on/set fallback paths, not mandatory work
on successful nontracking rewrites. Both update alternatives occur in the
static listing but are mutually exclusive. With tracking enabled and an
existing entry, lookup validation plus existing-entry update adds three
instructions, not four, absent runtime slow-path detours.

## Constructor/helper versus reuse

The candidate additionally emits a standalone `Cond_rewr.is_var_perm(1)`
(public in its signature); this is not an added call on construction or
application. The constructor `(3)` still contains the inlined predicate:
the decomposition, `vperm` call, and free-variable-set work at
`70..14C` have the same normalized shape. All constructor `blr` sites
remain; the standalone helper's emission does not mean it is newly called.

The constructor's actual closure-building difference is a 72 -> 64-byte
reservation and deletion of `ldr x10,[x8,#16]; str x10,[x9,#56]` at
baseline `1E0..1E4`: it stops capturing the key. The solver-bound and
stack-bound stages likewise drop one key-copy load/store pair, with
80 -> 72 and 88 -> 80-byte reservations. These are construction/binding
changes, not repeated extra work when applying a saved AC conversion.
The solver callback has no normalized instruction-shape difference.

Conclusion: this evidence rules out an added tracking helper call or
extra loads on ordinary AC reuse, but **not all extra instructions on
all nontracking paths**. Key placement changes executed instructions
and memory dependencies; literal/closure/code layout and cache effects
can differ even on the zero-instruction-delta path. This is static path
analysis, not measured runtime equality, a dynamic instruction total
including callees/GC, or an explanation of the earlier noisy AC ratio.
