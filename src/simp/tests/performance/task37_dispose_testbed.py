"""The record `task37_dispose.lines` reads, as the dispose tests build it
(test_task37_dispose and test_task37_gates). Nothing here is evidence."""


def lines_record(**over):
    """A record with every key `lines` reads, empty; `over` replaces keys
    (`attempts` is a dict with `allocation`, a table to attempts)."""
    record = dict(
        timing_attempts={}, startup_attempts=[], identity_unaccounted={},
        cells={}, task32={}, task33={}, gates={}, identity_grid={},
        allocation_case={}, timing_grid={}, retained_slope={},
        attempts=dict(allocation={}))
    record.update(over)
    return record
