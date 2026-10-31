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
# conversions, the marker library the tactic cases use, and the modules those
# call on every path the cases run: the theory history and its context
# snapshot (Theory, Context), the rule and conversion basis (Drule, Conv,
# Tactical), the term-set and marker helpers (liteLib, markerSyntax) and
# the reference cells of the traversal (Uref). The timing gate records the
# git blob of each at both commits, and a run whose candidate differs in one
# is never a pass (the scan allocates nothing a gate counts, so it is
# invisible to every other check). Repository-relative paths.
#
# The boundary: the kernel, the parser and the build files stay outside
# the list (they are shared by every operation and by the harness itself, so
# a change there moves both gates' baselines and is for review, not for a
# list of this size). Other modules sit outside it too (`ThmAttribute`,
# `Lib`, `testutils`, the build files). A file of the list being identical
# says nothing of the data it works on, such as the size of the theory
# graph; the fixtures fix that. The decisions hold the identity of the
# listed files only; the inventory publishes every file under src/ that
# differs (its source_tree), whether listed here or not.
SOURCES = (
    "src/simp/src/simpLib.sml", "src/simp/src/simpLib.sig",
    "src/1/Ho_Net.sml", "src/1/Ho_Net.sig",
    "src/1/BoundedRewrites.sml", "src/1/BoundedRewrites.sig",
    "src/simp/src/Traverse.sml", "src/simp/src/Traverse.sig",
    "src/simp/src/Travrules.sml", "src/simp/src/Travrules.sig",
    "src/simp/src/Opening.sml", "src/simp/src/Opening.sig",
    "src/simp/src/Cond_rewr.sml", "src/simp/src/Cond_rewr.sig",
    "src/simp/src/SimpTracking.sml", "src/simp/src/SimpTracking.sig",
    "src/simp/src/Trace.sml", "src/simp/src/Trace.sig",
    "src/marker/markerLib.sml", "src/marker/markerLib.sig",
    "src/marker/markerSyntax.sml", "src/marker/markerSyntax.sig",
    "src/lite/liteLib.sml", "src/lite/liteLib.sig",
    "src/postkernel/Theory.sml", "src/postkernel/Theory.sig",
    "src/prekernel/Context.sml", "src/prekernel/Context.sig",
    "src/portableML/Uref.sml", "src/portableML/Uref.sig",
    "src/1/Drule.sml", "src/1/Drule.sig",
    "src/1/Conv.sml", "src/1/Conv.sig",
    "src/1/Tactical.sml", "src/1/Tactical.sig")
