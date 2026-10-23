# TASK_08 interface design gate

**Current production ownership and closure:**
[../migration/TASK27.md](../migration/TASK27.md). All temporary rows, including
M6's executable test integration, are closed. Production `.sig` files are the
current interface authority; these TASK08 files remain checked design
prototypes, not a replacement for production/runtime evidence. The final
ledger distinguishes source closure, actual consumer execution, documentation
status and remaining plan-wide acceptance limits.

[DESIGN.md](DESIGN.md) finalizes types, control/identity ownership, recipes and
the explicit provider boundary. [CUTOVERS.md](CUTOVERS.md) assigns build/test and
transitional-removal obligations for TASK_09–16. The finalized 193-row API mapping
is [../migration/final-apis.tsv](../migration/final-apis.tsv); actual callers and
construction sites remain in the source-tied TASK_07 consumer ledgers.

From the repository root:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/compatibility/interfaces -j1 design-check
# Same checks with a durable receipt and executed-source paths:
python3 -B src/simp/tests/compatibility/interfaces/check_design.py \
  --run --negative-controls --output /path/to/evidence
```

`design-check` runs 15 Python validator tests and an executed 29-check HOL
selftest. The latter elaborates full interface signatures/consumer and cutover
functors, exercises real proof-producing paired runners/lifting/control binding,
and rejects eight cross-engine type misuses statically. Accepted-body and
missing-file controls must fail. `.uo` creation is not success.

There is no production engine implementation or permissive engine stub here.
The 193 rows are **migration decisions**, not 193 compiled downstream clients.
External output names bind to the typed Default provider boundary, with actual
external implementation validation owned by TASK_25. Shared exports are checked
in their existing owner signatures; extension exports are checked in their
specific prototype signature blocks. The graph is the declared design, not an
audit of final production imports. Actual intermediate builds are TASK_09–16.

`Task08Controls` models prepared-event rebinding with the actual current paired
matcher. It does not implement native source identities/history or recover
opaque controls. `Task08Reducers` implements only the explicit reducer boundary.
Final capability/runtime/allocation acceptance remains in the implementation
plan. No frozen baseline fixture, original assertion or production source changes
in this task. See [../TASK_08_HANDOFF.md](../TASK_08_HANDOFF.md).
