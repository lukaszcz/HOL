"""The TASK30 matrix cases: what the timing and allocation gates cover.

Data only, so the timing grid (task30_grid.py) and the allocation matrix
(allocation_matrix.py) cannot disagree about which cases are in scope.
"""

# Direct deletions from a simpset (`-*`), the operations whose single call is
# short: a batch of them needs a longer calibrated time to stand clear of the
# per-batch overhead.
DELETIONS = (
    "exclude_empty", "exclude_missing", "exclude_matching", "exclude_batch",
    "exclude_qualified", "exclude_partial", "exclude_literal_namespace",
    "exclude_literal_exact", "exclude_dproc", "exclude_mixed")
CASES = DELETIONS + (
    "exclude_marker", "exclude_marker_reuse", "exclude_tactic_construct",
    "exclude_tactic_reuse", "exclude_tactic_complete", "exclude_replay",
    "history_remove", "history_force", "history_excluded",
    "history_bounded", "history_limit", "history_collectors",
    "history_makers", "history_theory_change")
