"""The reviewed differences of the TASK30 candidate from the baseline.

Data only. The pins are facts about the candidate, not about the counts: the
counts derive from develop-only measurements, so this file is not among the
`sealed` files the counts are bound to, and a pin may change after the
counts were made. Its seal is recorded in the inventory of every grid
instead (`pins`), so a grid replays with the pins it was judged by: when
this file changes, the sha256 of its earlier version and the pins that
version held are added to `PIN_HISTORY` below. The history lives here, and
not in task30_grid.py, so that adding to it changes no driver seal.
"""

# Differences from the baseline in SOURCES that were reviewed and are
# accepted: each path maps to the exact candidate git blob (at the commit
# that introduced the pin) and the reason. The timing gate publishes them in
# its decisions and does not count them as a failure of source identity; any
# other revision of the file, or any other differing file, still does. A file
# the candidate adds (absent at the baseline) is listed in SOURCES and is
# accepted only with such a pin.
PINNED = {
    "src/simp/src/Cond_rewr.sml": dict(
        blob="a67c08102a6467765eba4febfb89c2e0c032b821",
        reason="Moves the rewrite-tracking helper to SimpTracking and "
        "aliases note_rewrite and with_tracking, which now call through "
        "SimpTracking's opaque signature, leaving mk_cond_rewrs and "
        "COND_REWR_CONV textually unchanged and adding no loop."),
    "src/simp/src/Cond_rewr.sig": dict(
        blob="ece2594285431754f43b3a293a6c0dd24dd70fbd",
        reason="Exports the existing is_var_perm and adds comments."),
    "src/simp/src/SimpTracking.sml": dict(
        blob="534f1637f1130bac873c5ffbb0466d60355cc280",
        reason="New file: the rewrite-tracking code removed from "
        "Cond_rewr, textually the same, held behind an opaque signature."),
    "src/simp/src/SimpTracking.sig": dict(
        blob="6aacb35d97fb7190e489cb2cb319fe6ea01ce2bb",
        reason="New file: the signature of the moved rewrite-tracking "
        "code."),
}

# The sha256 (hex) of each earlier version of this file, changed after
# grids were judged by it, mapped to the pins that version held, for the
# grids that were judged by them.
PIN_HISTORY = {}
