"""Fail-closed ordered compiled-core observations; no candidate exceptions."""
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "fragments/routes"))
import run_routes as routes
paired = routes.paired
require = paired.require
SIZES = (0, 1, 10, 100, 1000, 10000)
LABELS = ("fragment", "compiled", "merge", "projection", "cells")
CHECKS = (
    "source first expansion", "source second expansion",
    "qualified deletion wrong theory preserves",
    "qualified deletion removes first only", "qualified deletion keeps second",
    "source deletion removes all expansions", "source deletion is persistent",
    "bounded shared persistent allowance and recompile",
    "zero limit survives empty addition", "unlimit restores compiled rules",
    "empty addition preserves rules and hypotheses",
    "empty addition records history",
    "relsimp fragment compiles reducer", "relsimp direct compiles reducer",
    "relsimp merge compiles reducer", "relsimp history retained",
    "TypeBase data compiles first rule", "TypeBase data compiles second rule",
    "TypeBase lookup preserves fragment payload", "TypeBase lookup compiles",
)


def graph(text):
    events = routes.fragments.payload(text)
    expected, result = [], {label: [] for label in LABELS}
    cursor = 0
    for n in SIZES:
        expected.append(["check", "proofs " + str(n), "pass"])
        require(cursor < len(events) and events[cursor] == expected[-1],
                "missing graph proof")
        cursor += 1
        for label in LABELS:
            require(cursor < len(events), "missing graph observation")
            event = events[cursor]
            require(len(event) == 3 and
                    event[:2] == ["observation", "graph." + label],
                    "wrong ordered graph observation")
            fields = event[2].split(",")
            require(len(fields) == 4 and all(f.isdecimal() for f in fields),
                    "invalid graph integer row")
            size, anchor, union, increment = map(int, fields)
            require(size == n and union - anchor == increment,
                    "invalid graph size/subtraction")
            if label == "cells":
                require(increment == 5 * n, "graph sensitivity control failed")
            result[label].append(dict(rules=n, anchor=anchor, union=union,
                                      increment=increment))
            expected += [event, ["check", label + " " + str(n), "pass"]]
            cursor += 2
    expected.append(["observation", "complete",
                     "TASK16-compiled-core-graph-v1"])
    require(events == expected, "incomplete/extra graph observations")
    return events, result


def behavior(text):
    events = routes.fragments.payload(text)
    expected = [["check", name, "pass"] for name in CHECKS]
    expected[12:12] = [["observation", "pp.simpset." + str(width), None]
                      for width in (40, 80)]
    expected.append(["observation", "complete",
                     "TASK16-compiled-core-behavior-v1"])
    require(len(events) == len(expected), "incomplete/extra core observations")
    for actual, want in zip(events, expected):
        require(len(actual) == 3 and actual[:2] == want[:2],
                "wrong ordered core observation")
        if want[2] is None:
            require(actual[2] and actual[2].isascii() and "\\n" in actual[2],
                    "missing escaped complete simpset rendering")
        else:
            require(actual == want, "wrong core result")
    return events


def comparison(selections):
    result = {}
    for label in LABELS:
        sides = {side: selections[side]["graphs"][label]
                 for side in ("baseline", "candidate")}
        result[label] = dict(
            candidate_minus_baseline_words=[b["increment"] - a["increment"]
                for a, b in zip(sides["baseline"], sides["candidate"])],
            adjacent_words_per_rule={side: [
                (b["increment"] - a["increment"]) / (b["rules"] - a["rules"])
                for a, b in zip(rows, rows[1:])]
                for side, rows in sides.items()})
    return result
