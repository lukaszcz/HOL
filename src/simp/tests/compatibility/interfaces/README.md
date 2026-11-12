# Interface design gate

Production `.sig` files are the current interface authority; the `Task08*`
files here are checked design prototypes, not a replacement for
production/runtime tests.

[DESIGN.md](DESIGN.md) finalizes types, control/identity ownership, recipes and
the explicit provider boundary. The finalized 189-row API mapping
is [../migration/final-apis.tsv](../migration/final-apis.tsv).

From the repository root:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/compatibility/interfaces -j1 design-check
# Same checks with a durable receipt and executed-source paths:
python3 -B src/simp/tests/compatibility/interfaces/check_design.py \
  --run --negative-controls --output /path/to/output
```

`design-check` runs 15 Python validator tests and an executed 29-check HOL
selftest. The latter elaborates full interface signatures/consumer and cutover
functors, exercises real proof-producing paired runners/lifting/control binding,
and rejects eight cross-engine type misuses statically. Accepted-body and
missing-file controls must fail. `.uo` creation is not success.

There is no production engine implementation or permissive engine stub here.
The 189 rows are **migration decisions**, not 189 compiled downstream clients.
External output names bind to the typed Default provider boundary; the
consumer driver `run_task25_consumer.py` validates an actual external
implementation. Shared exports are checked
in their existing owner signatures; extension exports are checked in their
specific prototype signature blocks. The graph is the declared design, not an
audit of final production imports.

`Task08Controls` models prepared-event rebinding with the actual current paired
matcher. It does not implement native source identities/history or recover
opaque controls. `Task08Reducers` implements only the explicit reducer boundary.
No frozen baseline fixture, original assertion or production source is
changed by these prototypes.
