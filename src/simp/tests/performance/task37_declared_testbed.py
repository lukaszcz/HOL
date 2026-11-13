"""Fixtures of the TASK37 declaration tests (test_task37_declared and
test_task37_retarget). Nothing here is evidence."""
import json

import task37_declared as t


def prefill():
    """The committed declaration as it was before `fill`: its S2 closure
    total entry is the placeholder (an in-test fixture for the paths that
    handle a placeholder; the committed file is filled)."""
    data = json.loads(t.DECLARED.read_text())
    entry = data["s2"]["total_delta"][0]
    entry.update(value=None, observed=None, pending=True,
                 mechanism=["PLACEHOLDER: measured live, then filled in by",
                            "`task37_declared.py fill`."])
    return data
