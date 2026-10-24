# TASK29A numerical-policy review

**Disposition: policy-owner input required; TASK29A is NOT complete.**
This review does not amend the acceptance contract. All existing failures and
inconclusive decisions remain blockers. No tolerance, subtraction, special
zero/zero pass, manufactured collection, favorable-rerun selection or matrix
reduction is authorized. Nothing here closes allocation coverage or TASK29B.

## Contract reviewed

`PROTOCOL.md`, Statistics and decisions, requires every scoped metric to pass:

- Lower ratio-CI bound >1: fail; upper bound <=1: pass; otherwise inconclusive.
- Any zero denominator, including GC 0/0: null ratio/CI and inconclusive.
- A nonpassing B/B control prevents a candidate pass, never excuses a failure.

These are executable in `acceptance.py`: `decision`, `paired_statistics`,
`apply_control`, and `report_exit_status`. `policy_review.py` calls those
actual functions; it does not implement a replacement decision rule.

## Finding 1: exact zero GC has no passing ratio-only outcome

The original `compile_single/0` archive has **40 fresh timed processes** across
B/B and B/C and **120 measured batches**, all with exactly zero GC user and
system time. Both ten-pair GC analyses have ten null ratios and null intervals.
The positive-GC timer-accounting observations are preserved separately; none
is inserted into a timed workload or used to manufacture a denominator.

`policy_review.py` verifies the inventory/archive seal, unpacks losslessly,
then invokes the existing full `task29_gate.check_report` replay. That repeats
source/runtime/path/protocol admission and paired statistics for both B/B and
B/C, not just inspection of stored conclusions. It extracts every sample from
the admitted receipts, preserving pair, selection, sample index, iteration
count, GC operands, receipt seal and timer-accounting control in the review
receipt. Its temporary unpack tree is removed on success or failure.

The obstruction is conditional but exact: **any baseline process median equal
to zero makes the ratio analysis inconclusive**. More observations that remain
zero cannot define division by zero. A single zero denominator is sufficient;
nonzero observations elsewhere do not allow dropping that pair. This does not
prove that every future run must observe zero GC, nor that zero GC means zero
allocation. It does prove that these observations cannot pass this contract.

For size zero the `compile_single` workload folds an empty fragment list in
`MatrixSupport.sml`; adding collections or different work is not an admissible
repair. Historical-driver evidence is not acceptance for the repaired driver.
This review does not extrapolate its observations to that unmeasured full grid.

## Finding 2: B/B is directional, not a specified stability criterion

The same upper-bound <=1 rule applies to B/B admission. An interval
[0.999999, 1.000001] remains inconclusive however narrow it is. This alone does
**not** establish host instability. A quieter host or more repetitions cannot
be promised to put every upper bound below equality.

This is not an absolute impossibility theorem about B/B: exact positive paired
equality gives [1,1], which passes. The review deliberately exercises both
examples. With the equality-straddling control, a synthetic faster candidate
remains inconclusive and a slower one still fails. These are mathematical
contract demonstrations, not measurements of host behavior or a noise budget.

## Decision required from the policy owner

1. Is it intentional that exact zero/zero GC can never pass, and that even one
   zero baseline process median blocks an otherwise complete GC comparison?
2. Is B/B intended to prove directional upper-CI<=1, or was an independently
   specified control-validity/stability criterion intended?

**No alternative rule is selected or implemented by this review.** If the
current contract is retained, these regimes remain nonpassing. If a change is
requested, its exact scope, statistics, negative controls and treatment of
historical observations require separate explicit approval before use. A
clarification cannot by itself repair the measured fragment slowdown.

## Reproduction and limits

From the repository root, using a new output file:

```sh
python3 -B src/simp/tests/performance/policy_review.py --output NEW_REVIEW.json
# Exit 2: review reproduced, policy-owner input required; NOT task acceptance.
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p test_policy_review.py -v
```

The durable result is `evidence/task29/policy-review/review.json`; its source
and archive seals bind this review. Tests cover additional zero repetitions,
a single undefined denominator at every pair position, the precise-straddling
control, exact positive equality, failure preservation, full actual-archive
re-admission, archive/cell mutation, and refusal to overwrite an old receipt.
The synthetic examples are explicitly separated from the archived observations.
This is one historical cell replay, **not** a full-grid replay or a new timing,
heap/pool/indirect-target attribution, repair or allocation experiment.

The independent repaired-driver replay still reports fragment/0 CPU
**[1.014519, 1.032057]**, a failure; collector/10000 CPU
**[0.988111, 1.032104]**, inconclusive. The full repaired-driver 162-cell grid
and ordinary-process heap/pool/indirect-target attribution remain unsatisfied
acceptance requirements. No exclusive-host availability or causal host-noise
explanation is inferred from this review. There is no completion-log entry.
