# Tracked default provider regression tests

Run from the repository root:

```sh
bin/Holmake --no-project --no-cache \
  -C src/boss/tests/tracked-defaults -j1 check
```

On the configured-path/bwrap checkout used during development:

```sh
sh src/simp/tests/compatibility/tools/root-wrapper.sh \
  bin/Holmake --no-project --no-cache \
  -C src/boss/tests/tracked-defaults -j1 check
```

`check` builds and runs `selftest.sml` using `testutils` and `hol.state0`,
following the provider's normal dependency closure. A separate fresh
`ordinary.sml` process dynamically loads BasicProvers, num/list/set recipes
and bossLib; after each import it checks module/namespace absence of all
extensions and the provider, then validates three closed ordinary proofs.
No ordinary default is replaced and no production files are patched.
The deliberate static-error diagnostics at the end are successful negative
tests; missing files or non-static failures are **not** accepted.

## Contracts maintained here

- Exact initial seed fragment order, fresh installations, and complete
  theorem (conclusion **and hypotheses**) differential tests. The oracle is
  an independent reconstruction of `BasicProvers.initial_simpset`, followed
  by its ordered TypeBase initialization fold. The initialized result also
  agrees with the real `BasicProvers.merge_simpsets ["min"]` initialization,
  not an arbitrary current `srw_ss` with later declarations mixed in.
- `TheoryBatch` reverses only additions, installs even an empty named batch,
  and applies removals afterward in supplied order. A nonconfluent fixture
  distinguishes addition priorities; distinct strict-name errors distinguish
  removal order. Local deltas remain sequential.
- Explicit fragments, supplied TypeInfo data and ordered `typebase_steps`,
  positioned updates, construction/installation HOL_ERR handling, and
  propagation of foreign exceptions. `Update` does not absorb `UNCHANGED`.
- Seeds run once; deliberately reused tracked seeds share live and exhausted
  bounded controls. Fresh builds install fresh sources. Provider retrieval
  and traversal/source projections do not rerun rewrite makers or reset
  exhausted allowances.
- `map`, pure context install/get/map, precise absent-provider errors,
  immutable snapshots, nested windows, success/HOL_ERR/foreign/UNCHANGED
  rollback, failed updates, unrelated-slot preservation and pinned contexts.
  Windows and snapshot restoration preserve actual source identities and
  quota consumption, not just equivalent theorem ingredients.
- Ordinary SRW proofs and fragment order remain unchanged; ordinary updates
  neither enter the provider nor influence `initial_seed`.
- Executable static rejection of ordinary seeds, fragments and update
  closures in `negative/*.ML`.

The suite creates only process-local values and restores its initial context
before exiting. All conversions run through this executable selftest, not
through an ad hoc interactive HOL session.
