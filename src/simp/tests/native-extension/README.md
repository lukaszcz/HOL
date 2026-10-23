# Native simplifier integration regression

`selftest.sml` is the **byte-for-byte** TASK25 mixed selftest, relocated from
`src/simp/src/`. It owns all 630 reviewed assertions plus the 12 explicitly
mapped extension-registry repetitions. Its interleaved ordinary controls,
proof/hypothesis predicates, exceptions, callback counters, warnings, source
identities, conjunct/view/bundle quotas and replay assertions are unchanged.
Historical comments/aliases remain deliberately intact. This is an integration
suite that imports both types, **not** the ordinary selftest dependency scope.

The ordinary `src/selftest.sml` is now the complete pinned develop input.
Additional ordinary contracts live alongside this suite, not inside that input.
See [the ownership map](../compatibility/migration/TASK26.md).

## Run

After the option/list theory exports have been built:

```sh
bin/Holmake --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/native-extension -j1 HOLSELFTESTLEVEL=1 all
```

`check-full` executes the launcher and requires the entire mapped stream:
**642 checks, seven warnings, and all 11 original aggregate result vectors
(128 Boolean observations)**. The frozen TASK06 ledger and TASK10 mapping are
not regenerated. Missing datatype cases, reordered/changed labels or warnings,
missing vector fields and truncated output fail the gate.

`tools/sequences/base-hol` schedules this directory at normal selftest level 1
**after `src/list/src` uploads its exports**. A fresh bootstrap cannot run the
five option/pair/list assertions earlier: the unchanged suite conditionally
skips them. `src/simp/src` may run that bootstrap smoke test through its
`native-extension` target, but its 637 checks are never complete coverage or a
compatibility pass. The later `check-full` is mandatory and rejects that output.
No later-theory assertions are silently waived on a clean checkout.
