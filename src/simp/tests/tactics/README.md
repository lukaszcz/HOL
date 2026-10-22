# TASK18 ordinary tactic contracts

Maintained `selftest.sml` supplements (does not replace or regenerate) TASK05's
43-scenario staged matrix. `run_behavior.py` uses the existing TASK15 snapshot
and TASK02 private-first traced runner. It executes pinned develop and current
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

TASK05 separately owns exact inference counts, grammar/context changes, late
fragment/abbreviation lookup, malformed bounds, ordering quirks and global tactic
construction. See `../compatibility/STAGING_CONTRACTS.md`. Explicit extension
recursion and marker controls remain in `../markers/selftest.sml`/TASK20;
ordinary reentry here never imports those modules. See `AUDIT.md` for the exact
source boundary. No production or generic-marker body needs a further edit:
TASK16 already restored the original implementation. Final commands, source
seals and receipts are in `evidence/task18/validation.json`; recheck offline:

```sh
python3 -B src/simp/tests/tactics/audit_evidence.py
python3 -B src/simp/tests/tactics/performance/evidence/recheck.py
python3 -B src/simp/tests/tactics/performance/evidence/followup.py --archive
```

Bounded acceptance and measured uncertainties are recorded in
`../compatibility/TASK_18_HANDOFF.md`. Numerical parity and independent clean
builds are not inferred from identical local source/native instructions.
