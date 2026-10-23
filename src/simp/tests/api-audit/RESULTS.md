# TASK27 fixture validation

Executed the standalone gate and the integrated normal-level target, from
the repository root:

```sh
sh src/simp/tests/compatibility/evidence/task26/root-wrapper.sh \
  bin/Holmake -C src/simp/tests/api-audit check
```

Final receipt: `evidence/20261023T084819Z-7b0ad6ac/receipt.json`.
All eight fresh-process cases passed: **1,374 testutils assertions** in total.
The receipt seals all six fixture/build/runner sources, runtime/tools/heap,
the complete compressed logs and the compressed 420-file actual used/loaded
path inventory (generated theory files resolve into `.hol/objs`). The logs
retain every actual loader path, separate from requested module paths.

| Import order | Foreign owner | Owner before imports | Owner after imports |
| --- | --- | --- | --- |
| simpLib, congLib | attribute | 172 | 168 |
| simpLib, congLib | exporter | 176 | 171 |
| congLib, simpLib | attribute | 172 | 168 |
| congLib, simpLib | exporter | 176 | 171 |

Counts include repeated entry/import absence and identity assertions, not
1,374 distinct API scenarios. The parent routine selftest-enabled build
passed and reran this target; a full/release build is not claimed. No production
implementation/signature or existing assertion fixture was edited. Generated launcher/cache products and
superseded development receipts were removed after validation; `check`
recreates its own products and always writes a new uniquely named receipt.

During development, the gate correctly rejected combining a foreign exporter
with a separately registered same-name attribute (the exporter installs its
own dispatcher), and rejected missing explicit `boolLib` opens in the fresh
runtime namespace. The final matrix separates owner types and the examples
open their required modules. These development failures are not counted as
passes or represented as production changes.
