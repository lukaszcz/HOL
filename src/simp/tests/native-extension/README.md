# Native simplifier integration regression

`selftest.sml` is the extension engine's integration suite, relocated from
`src/simp/src/`. It imports both engines, binding the extension modules to
the familiar names (`simpLib`, `boolSimps`, …) and keeping the ordinary ones
as `OrdinarySimp`, `OrdinaryBool`, … for the interleaved ordinary controls.
It is therefore never linked into the ordinary `src/simp/src/selftest.sml`.

## Run

After the option/list theory exports have been built:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/native-extension -j1 check
```

`tools/sequences/base-hol` runs this directory at selftest level 1 **after
`src/list/src` uploads its exports**. `src/simp/src` also runs it earlier
through its `native-extension` target; at that point the option, pair and
list cases are skipped because those theories do not exist yet.
