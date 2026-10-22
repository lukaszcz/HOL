# Fragment compiler-generated instruction audit

```
python3 -B -m unittest discover -s src/simp/tests/fragments/assembly -v
python3 -B src/simp/tests/fragments/assembly/run_assembly.py \
  --output /tmp/fragment-assembly-evidence
```

Requires Poly/ML 5.9.2 Release on AArch64 and built shared HOL dependencies.
Uses `run_fragments.snapshot` and `run_paired.validate`: frozen baseline
`cccaa27d7099cbadc886983020cbe745db7793f3` versus current worktree by default.
`--candidate COMMIT` supports unchanged-source controls. Two fresh private
processes, private simplifier source copies, shared `hol.state0` and non-simp
products; not independent clean repository builds. Never changes production.
Temporary source trees are removed on success, failure, or interruption.

The private `runner.sml` enables `PolyML.Compiler.assemblyCode` only while
`tracedUse` compiles the exact private `simpLib.sml` path, disabling it on
success or exception. Optional `--optimized-tree` also enables
`PolyML.Compiler.codetreeAfterOpt` and `PolyML.Compiler.icode` for that extent
only. The default remains assembly-only. All three switches are disabled
before dependencies or the selftest are compiled, including on exceptions.
The minimal `selftest.sml` verifies that reset plus public fragment names,
rewrite order, update/merge persistence. No casts, closure introspection,
allocation instrumentation, timing, or benchmark runs.

Retains exact selected named function listings (including nested emitted
helpers), structured paired receipts, and a manifest sealing source snapshots,
fixture inputs, compiler/runtime/heap, dependency products and listing files.
The full compiler-output byte count/hash is retained, not its entire dump.
All six required constructor roots must emit code. Optional helpers absent
from a dump are reported as unsupported, possibly inlined (not zero work).
Duplicate emitted names retain every occurrence with `@2`, `@3`, ... keys;
exact listing headers are unchanged. One-sided helper emissions are explicit
comparison failures, not silently dropped from the inventory.

## Optional callee-identity evidence

```
python3 -B src/simp/tests/fragments/assembly/run_assembly.py \
  --optimized-tree --output /tmp/fragment-optimized-tree-evidence
```

The extra `*.optimized-tree.json.gz` artifacts retain exact optimized lambdas
and ICode passes for `merge_ss` and `merge_names` (including nested helpers),
plus `List.foldr(3)()` specializations explicitly referencing `merge_names`
and their native bodies. Unrelated folds and backend trees are discarded.
Each record includes its original stdout line interval and text hash; the
manifest seals both the compressed artifact and its uncompressed bytes.
The original **full merged stdout** byte count/SHA-256 remains in each process
receipt even though unrelated compiler output is discarded. Assembly bodies
remain separately sealed and are compared by the unchanged strict comparator.
No casts, application-side closure inspection, or source normalizations are
used to discover targets. Compiler-emitted `CODE`/`FunctionCall`/`TailCall`
names, argument setup, and helper bodies are diagnostic evidence, not a
permission to waive real assembly differences. Missing trees/call dumps fail
collection rather than silently claiming a resolved relationship.

Do not run this compiler workload concurrently with fragment benchmarks.
For the task15 fixed run, wait until `/tmp/task15-logs/fixed-control.exit`
exists **and** no `run_fragments.py` process remains before invoking it.

## Comparison policy

Static instruction counts exclude inline GC register maps and `?` padding;
those entries are separately counted. Calls, mnemonic counts and literal
`sub xN,x27,#bytes` reservation instructions are reported. These are static
sites, **not dynamic execution or total allocation counts**.

Comparisons preserve listing offsets, registers, branch targets, calls, GC
maps, record/closure/stack offsets, allocation sizes and instruction order.
Only an adjacent `adrp R,page; ldr X,[R,#offset]` pair's page/offset operands
are replaced by pool placeholders: the compiler uses those PC-relative
operands to load relocatable constant-pool entries, not record fields.
Instruction encodings are retained in exact listings but compared by decoded
mnemonic/operands. This deliberately does not claim equal pool contents or
callee implementations; snapshots seal the inputs and this is a local
fragment-construction code comparison, complementary to allocation evidence.
No branch-target, field-offset or register-renaming normalization is allowed.
Any nonrelocation difference fails acceptance, even with equal instruction
counts; there is no tolerance, unexplained extra-call/allocation exemption,
or candidate-specific golden regeneration.

Output directories must not already exist. `manifest.json` records failures;
accepted equality requires `success: true`, both accepted paired receipts,
`collection_validated: true`, `strict_equality_accepted: true`, and all
`identical_after_pool_relocation` flags true. A validated collection with
rejected equality is still useful negative evidence, never a parity pass.
See `RESULTS.md` and retained `evidence/`.
