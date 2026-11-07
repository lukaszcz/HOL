"""The TASK31 matrix cases: which ClientPerformance cells the gates cover.

Data only, plain tuples, so the allocation matrix (allocation_matrix.py,
task `task31`) and any other TASK31 gate cannot disagree about the scope.
The sizes of a case are those of its size set in matrix.json
(`traversal_*`: singleton `0` or depth `0/1/10/100`; `tactic_*`: assumptions
`0/1/10/100/1000/10000`); INFEASIBLE removes the cells that no gate can
run. `downstream_*` belongs to TASK_32/33 and is not listed.
"""

TRAVERSAL = (
    "traversal_construct", "traversal_context_construct",
    "traversal_complete", "traversal_reuse_hit", "traversal_reuse_miss",
    "traversal_deep", "traversal_congruence", "traversal_weakening",
    "traversal_side_conditions", "traversal_failed_candidates",
    "traversal_saved")

# The families whose size-10000 cells are feasible: one apply costs under
# a second, so setup and every stage fit the process timeout.
LIGHT_FAMILIES = ("supplied", "installed", "asm")
# The other eleven: setup alone is 1426 s for full at 10000 (the cost
# survey), one apply 300-1100 s.
HEAVY_FAMILIES = (
    "full", "reverse", "no_strip_full", "no_strip_reverse", "global",
    "req0", "reqd", "req0_reqd", "reqd_req0", "dependency_full",
    "dependency_reverse")
STAGES = ("construct", "reuse", "complete")
HUGE = 10000

CASES = TRAVERSAL + tuple(
    "tactic_%s_%s" % (family, stage)
    for family in LIGHT_FAMILIES + HEAVY_FAMILIES for stage in STAGES)

# (case, size) cells that cannot run: the 33 heavy tactic cells at 10000.
INFEASIBLE = tuple(
    ("tactic_%s_%s" % (family, stage), HUGE)
    for family in HEAVY_FAMILIES for stage in STAGES)
