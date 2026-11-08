# TASK18 ordinary tactic contracts

Maintained `selftest.sml` supplements (does not replace or regenerate) the
43-scenario staged matrix in `../compatibility/staging/`. `run_behavior.py`
uses the fragments snapshot (`../fragments/run_fragments.py`) and the
private-first traced runner `../compatibility/run_paired.py`. It executes
pinned develop and current
worktree in fresh processes, with common state0/shared nonsimplifier dependencies;
these are isolated-source experiments, not independent clean builds.

```sh
python3 -B -m unittest discover -s src/simp/tests/tactics -p 'test_*.py'
python3 -B src/simp/tests/tactics/run_behavior.py --output /tmp/tactics-pair
# Positive runner control (use a fresh output directory):
python3 -B src/simp/tests/tactics/run_behavior.py \
  --candidate cccaa27d7099cbadc886983020cbe745db7793f3 \
  --output /tmp/tactics-control
```

`Holmake -C src/simp/tests/tactics check` runs Python behavior/performance/
codegen controls, a temporary supplemental pair, and the strict original plus
expanded staging fixtures. `ordinary-tactics` integrates it at simplifier
selftest level 1. It preserves exits and removes private artifacts. To retain
source-tied receipts, invoke the Python command directly. Output directories
must not exist. Temporary source trees are automatically removed, including
on errors. The driver seals source/fixture/tool/heap/shared-product bytes and
checks actual elaboration paths, preloaded inventory, process exits, exact
ordered observations and completion count. No golden regeneration switch.

307 native checks / 116 real validations per selection cover ordinary aliases,
assumption policies, explicit/missing labels, full/reverse/no-strip branching
and contradiction, psr/allasms configuration, rules/conversions/proving,
nested requirement/bound payloads,
reentry against changing assumptions, and direct/full requirement stage
contrasts. Proof checks compare complete hypothesis sets where specified and
always reject foreign hypotheses/oracle tags; residual proofs are kernel-built.
Native controls test those rejection predicates and reversed branch detection.
Both zero-subgoal and multiple-subgoal validations execute. No `VALID` synthetic
oracle proofs are used. Python controls reject every omitted/wrong result,
changed validation count, extra/reordered results and malformed sequence IDs.

Exact inference counts, grammar/context changes, late fragment/abbreviation
lookup, malformed bounds, ordering quirks and global tactic construction are
covered by the staged matrix; see `../compatibility/STAGING_CONTRACTS.md`.
Explicit extension recursion and marker controls are in
`../markers/selftest.sml`;
ordinary reentry here never imports those modules. The ordinary
`simpLib.{sml,sig}` pair is byte-identical to develop
(`cccaa27d7099cbadc886983020cbe745db7793f3`), checked by
`performance/audit_sources.py`. Numerical parity and independent clean builds
are not inferred from identical local source/native instructions.
