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

# In the timing gate but not in the allocation gate, with the reason. The
# allocation gate treats TMPDIR and the scratch path length as a place, not
# content (allocation_matrix.PLACE_KEYS); that holds only while no bracket
# reads the environment or a path.
ALLOCATION_EXCLUDED = {
    "history_theory_change":
        "new_theory exports the current theory: it writes *Theory files "
        "into the working directory (the private selection, whose sealed "
        "tree must not change during a cell) and builds documentation "
        "paths from the working directory, so the words depend on the "
        "path structure and not only on its length"}
ALLOCATION_CASES = tuple(c for c in CASES if c not in ALLOCATION_EXCLUDED)
