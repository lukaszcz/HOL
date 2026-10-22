# Literal exclusions and ordinary history replay

`selftest.sml` supplements the immutable 929-check differential suite, rather
than modifying its observations. `run_behavior.py` privately compiles pinned
develop and the working simplifier sources, executes both launchers, checks
loaded paths and source/product hashes, and requires the exact ordered stream.
All 42 checks include callback schedules, declared quota reset, preserved limits
and excluded names, missing nonempty history reparsing after a genuine theory
change, conversions, and saved/reused tactic proof validations.

From repository root:

```sh
python3 -B src/simp/tests/exclusions/run_behavior.py --output /tmp/excl-behavior
bin/Holmake --holstate="$PWD/bin/hol.state0" -C src/simp/tests/exclusions check
```

The normal `HOLSELFTESTLEVEL=1` simplifier build runs `check`. Python protocol
negative controls reject omissions, order/count changes, bad proofs and missing
completion. This is source-isolated/shared-dependency evidence, not an
independent repository build.

`performance/` has the consumed-result four-size, eleven-operation matrix,
source/codegen correspondence, raw AB/BA campaigns and allocation/GC analysis.
No legacy production wrapper, inventory, namespace resolver or fast-path flag
is introduced. Literal Excl is never changed to ExclX.
