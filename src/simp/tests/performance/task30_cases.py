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

# The source files on the path of the TASK30 operations that develop and the
# candidate must hold identically for the timing and allocation gates to
# measure the same code: the simpset exclusion and its nets and dprocs, the
# bounded-rewrite history, the conditional rewriter that builds rewrite
# conversions, and the marker library the tactic cases use. The timing gate
# records the git blob of each at both commits, and a run whose candidate
# differs in one is never a pass (the scan allocates nothing a gate counts, so
# it is invisible to every other check). Repository-relative paths.
SOURCES = (
    "src/simp/src/simpLib.sml", "src/simp/src/simpLib.sig",
    "src/1/Ho_Net.sml", "src/1/Ho_Net.sig",
    "src/1/BoundedRewrites.sml", "src/1/BoundedRewrites.sig",
    "src/simp/src/Traverse.sml", "src/simp/src/Traverse.sig",
    "src/simp/src/Travrules.sml", "src/simp/src/Travrules.sig",
    "src/simp/src/Opening.sml", "src/simp/src/Opening.sig",
    "src/simp/src/Cond_rewr.sml", "src/simp/src/Cond_rewr.sig",
    "src/simp/src/Trace.sml",
    "src/marker/markerLib.sml", "src/marker/markerLib.sig")

# Differences from the baseline in SOURCES that were reviewed and are
# accepted: each path maps to the exact candidate git blob (at the commit
# that introduced the pin) and the reason. The timing gate publishes them in
# its decisions and does not count them as a failure of source identity; any
# other revision of the file, or any other differing file, still does.
PINNED = {
    "src/simp/src/Cond_rewr.sml": dict(
        blob="a67c08102a6467765eba4febfb89c2e0c032b821",
        reason="Moves the rewrite-tracking helper to SimpTracking and "
        "aliases note_rewrite and with_tracking, leaving mk_cond_rewrs and "
        "COND_REWR_CONV textually unchanged and adding no loop."),
    "src/simp/src/Cond_rewr.sig": dict(
        blob="ece2594285431754f43b3a293a6c0dd24dd70fbd",
        reason="Exports the existing is_var_perm and adds comments."),
}
