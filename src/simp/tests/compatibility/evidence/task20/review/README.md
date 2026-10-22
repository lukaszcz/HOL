# TASK20 verification at 510641058 — incomplete

The maintained tests do not cover two failing intersections. A fresh
Holmake-built `selftest.sml` launcher exits 1 with two failed assertions
(`output.log`); no static errors remain in that execution.

- `GEN_SIMP_TAC` with a missing Abbr and missing FRAG raises
  `simpLib.process_tags: No frag called review_missing_frag` before running
  the Abbr pretactic. `process_taclist_then_bind` eagerly invokes its binding
  callback while constructing `THEN`; that callback prepares supplied rules.
  Previously preparation ran after pretactics. The retained original native
  assertion at `src/simp/src/selftest.sml:5625` pins Abbr-before-FRAG ordering,
  but does not cover this explicit configured path.
- `prepare_rewrite_arguments` changes the selected bound of the genuine rule
  `Once (Ntimes rule 2)` from 1 to 2. Its DBounded branch recursively treats
  the remaining bound as a directive and discards the initially selected
  rewrite allowance. This violates preserved bounded controls.

The third assertion is a passing comparison, not a blocker: on the tested
empty simpset, wrapped NoAsms leaves one residual goal through both entry
points. A suggested alias discrepancy was not reproduced.

Reproduce from repository root (normal state0/shared dependencies):

```sh
out=$(mktemp -d /tmp/task20-review.XXXXXX)
cp src/simp/tests/compatibility/evidence/task20/review/selftest.sml "$out/"
printf 'HOLHEAP = %s/bin/hol.state0\nINCLUDES = %s/src/simp/src\n\nselftest.exe: selftest.uo\n\t$(HOLMOSMLC) -o $@ $<\n' \
  "$PWD" "$PWD" > "$out/Holmakefile"
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C "$out" -j1 selftest.exe
(cd "$out" && ./selftest.exe) # expected exit 1 until repaired
rm -rf "$out"
```

No production source or original assertion was changed. TASK20 remains the
next unblocked repair task; TASK21 depends on its full acceptance.
