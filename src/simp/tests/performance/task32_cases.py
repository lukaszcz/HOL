"""The TASK32 workloads: the proof builds and selftests of the downstream
areas that the independent snapshots (task32_snapshots.py) are timed on.

Data only, so the timing driver (task32_downstream.py) and its tests cannot
disagree about which units are in scope. Fifteen units, five areas:

  theory    one theory script, rebuilt from its prebuilt dependencies by
            `Holmake <name>Theory.uo` in `dir` (the unit's products are
            deleted first and restored byte for byte afterwards);
  selftest  the `hol run ... selftest` command that the directory's
            `selftest.exe` holds, run in `dir`.

`heap` is the heap the unit's script or test runs in, relative to the
snapshot root: the four heaps of the tree (hol.state0, the numheap of
src/num/termination, hol.state and the realheap of src/real/analysis) are
all covered. The hol.state0 units load the simplifier at run time, so they
pay the startup difference TASK31 handed over. `serial` is the serial target
time of `.hol/build-logs/target-times` (seconds), an expectation for the
pilot's duration check and not a gate.
"""

AREAS = ("arithmetic", "reduce", "integer", "real", "boss")


def theory(name, area, directory, heap, serial):
    return dict(name=name, area=area, kind="theory", dir=directory,
                theory=name, heap=heap, serial=serial)


def selftest(name, area, directory, heap, serial):
    return dict(name=name, area=area, kind="selftest", dir=directory,
                theory=None, heap=heap, serial=serial)


NUMHEAP = "src/num/termination/numheap"
REALHEAP = "src/real/analysis/realheap"

UNITS = (
    theory("arithmetic", "arithmetic", "src/num/theories",
           "bin/hol.state0", 7.4),
    theory("rat", "arithmetic", "src/rational", "bin/hol.state", 7.2),
    selftest("arith-selftest", "arithmetic", "src/num/arith/src",
             "bin/hol.state0", 7.1),
    theory("logroot", "reduce", "src/num/extra_theories", NUMHEAP, 2.1),
    selftest("reduce-selftest", "reduce", "src/num/reduce/src",
             "bin/hol.state0", 6.2),
    theory("integer", "integer", "src/integer", "bin/hol.state", 5.7),
    theory("integer_word", "integer", "src/integer", "bin/hol.state", 8.6),
    selftest("integer2-selftest", "integer", "src/integer/testing",
             "bin/hol.state", 6.7),
    theory("real", "real", "src/real", "bin/hol.state", 10.6),
    theory("real_sigma", "real", "src/real", "bin/hol.state", 8.6),
    theory("lim", "real", "src/real/analysis", REALHEAP, 13.0),
    selftest("real-selftest", "real", "src/real", "bin/hol.state", 6.2),
    theory("rich_list", "boss", "src/list/src", NUMHEAP, 7.7),
    theory("pred_set", "boss", "src/pred_set/src", NUMHEAP, 10.8),
    selftest("boss-selftest", "boss", "src/boss", NUMHEAP, 7.3),
)
NAMES = tuple(u["name"] for u in UNITS)
BY_NAME = {u["name"]: u for u in UNITS}
# The unit of the live negative control (the cheapest one).
CONTROL_UNIT = "logroot"
HEAPS = tuple(sorted({u["heap"] for u in UNITS}))
# The heap each heap is built on (hol.state0 is the bare one): numheap with
# `buildheap -b hol.state0` (src/num/termination/Holmakefile), hol.state on
# hol.state0, realheap by `hol buildheap` from hol.state
# (src/real/analysis/Holmakefile).
HEAP_PARENTS = {NUMHEAP: "bin/hol.state0", "bin/hol.state": "bin/hol.state0",
                REALHEAP: "bin/hol.state"}
