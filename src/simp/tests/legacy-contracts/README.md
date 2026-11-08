# Ordinary-only native contracts

Normal entry: `src/simp/src/Holmakefile` target `legacy-contracts`, included
in `HOLSELFTESTLEVEL=1 all`. Explicit entry:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/legacy-contracts -j1 check
python3 -B src/simp/tests/legacy-contracts/run.py --negative-controls \
  --output /tmp/new-legacy-receipts
```

The driver creates a disposable native fixture directory and executes separate
launchers for all nine unchanged public source clients (18 checks), the unchanged
six `PriorLimits` quota/rollback checks, and one new original-import scope check.
Original signature bytes are verified against Git and only their signature
headers are renamed, using the existing differential installation code. No
assertion bodies are copied into a second maintained oracle or edited.

Each of the 11 processes verifies its exact check count and a unique completion
footer. The driver compares ordered case labels and actual module paths. Every
process additionally rejects both loaded and bound extension modules, markers,
splitters or persistence owners. `OriginalScope.sml` covers the complete original
selftest import closure, including COMBIN and SATISFY. Source/runtime/product
seals and complete command/exit/output receipts are retained with `--output`;
otherwise all scratch is removed on success or failure.

Negative execution controls deliberately load an extension and supply a wrong
completion count. Both must fail at their intended guard. Unit controls also
reject missing paths, foreign products, changed labels, zero-exit incomplete
output and missing native aggregate fields. They run in the normal entry too.

The compatibility Python tests include historical source-audit mutation tests.
Their whole-source inputs are pinned to the sources they were written against,
not weakened to accept arbitrary later extension edits. Live ordinary sources
still have byte-exact checks. These historical unit controls are not a final
current-tree dependency/performance acceptance claim.
