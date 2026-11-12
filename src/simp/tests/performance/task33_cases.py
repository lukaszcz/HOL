"""The TASK33 timing workloads: fresh-process startup and first-load cost of
the simplifier on the two independent snapshots (task32_snapshots.py).

Data, like task32_cases.py, plus the table's digest and the helpers that
read a unit's controls, so the timing driver (task32_downstream.py
`--table task33`), the storage driver and their tests cannot disagree about
which units are in scope. Five units, all of the kind `probe`: the process
is

    root/bin/hol --gcthreads=1 run --holstate=root/HEAP reporter.uo PROBE

(PROBE a bare module name) run in the side's probe directory (the
reporter's directory, outside the snapshot, where the sealed probe sources
of `task33/` are built by that side's own Holmake in their final
directory: the compiled unit lives in `.hol/objs/`, so nothing names or
tests the physical `PROBE.uo`). A unit carries `probe`, the probe module;
`env`, the variables that select its work (the probe reads them, so one
module serves every kind: T33_KIND is the unit's name, the `kind` of its
records, and a `load-*` kind has T33_MODULE, the module it loads); `heap`,
the heap relative to the snapshot root; `loads`, the modules the kind loads
(each must be in the process's `loaded` and not in `loaded_before`; for `()`
no module of SIMPLIFIER_LIBS is newly loaded); and `min_checks`, the least
number of `@@T33` check records the process must print (a digest of them is
the unit's output, equal in every process of both sides). Every key of `env`
is `T33_*` (the driver's own T32_* variables cannot be set by a unit). A
control (T33_LEAK, T33_HOOK, T33_GRAPH_EXTRA) is a separate unit
(`control_unit`): a receipt's environment must equal its unit's.

  state0-empty  hol.state0, nothing (startup)
  state-empty   hol.state, nothing (startup)
  load-simpLib  hol.state0, `load "simpLib"`, then one SIMP_CONV check
  load-congLib  hol.state0, `load "congLib"`, then one congruence check
  first-use     hol.state, first and second SIMP_CONV and SIMP_TAC

`serial` is a rough expectation of the whole-process CPU in seconds (only
fakes use it; the pilot measures the real figure and the unit floor is
`task32_downstream.Table.min_unit_cpu`).
"""

import task33_records as records

AREAS = ("startup", "load", "use")
PROBE = "T33Load"
# What an empty or first-use process must not newly load.
SIMPLIFIER_LIBS = ("simpLib", "congLib")


def probe(name, area, heap, module, min_checks, serial):
    """A unit of T33Load: its process kind (T33_KIND, the `kind` of its
    records) is its name, and a `load-*` kind names the module it loads
    (T33_MODULE)."""
    return dict(name=name, area=area, kind="probe", dir=None, theory=None,
                heap=heap, probe=PROBE, serial=serial,
                loads=(module,) if module else (),
                env=dict(T33_KIND=name, **(
                    dict(T33_MODULE=module) if module else {})),
                min_checks=min_checks)


# Every file of the probe directory, relative to this directory: the sealed
# probe sources (`task33/*`, records.PROBE_SOURCES), the unchanged
# RuntimeMetrics.sml they `use`, and the parser that reads their output.
# They are in the table's CODE, `build_probes` checks their seals, and a run
# report records them.
PROBE_FILES = tuple("task33/" + n for n in records.PROBE_SOURCES) + \
    records.PROBE_REUSED
CODE_FILES = PROBE_FILES + ("task33_records.py",)


def controls_of(unit):
    """The control switches (names of records.SWITCHES, the `controls` of
    records.validate) a unit's environment sets: a unit with T33_LEAK=1 is
    a control unit. A switch that is set but not "1" is refused: the probe
    treats only "0" and "1" as set values and refuses the rest."""
    env = unit.get("env") or {}
    out = []
    for switch, name in zip(records.SWITCHES, records.CONTROLS):
        value = env.get(name)
        if value not in (None, "0", "1"):
            raise ValueError("unit %s: %s=%r is not 0 or 1" % (
                unit.get("name"), name, value))
        if value == "1":
            out.append(switch)
    return tuple(out)


def control_unit(unit, switch):
    """`unit` with one control switch set (a separate unit: a receipt's
    environment must equal its unit's, so a control process is never the
    ordinary unit with a changed environment). `switch` is a name of
    records.SWITCHES; it must act in the unit's probe, as the validator
    requires of the records."""
    probe = records.PROBE_OF_MODULE.get(unit["probe"])
    if switch not in records.SWITCHES or \
            probe not in records.CONTROL_PROBES[switch]:
        raise ValueError("control %s is inert in the probe %s" % (
            switch, unit["probe"]))
    name = records.CONTROLS[records.SWITCHES.index(switch)]
    return dict(unit, name=unit["name"] + "+" + switch,
                env=dict(unit["env"], **{name: "1"}))


def digest(text, root, probe_dir, unit):
    """The table's output digest of a `probe` unit (`Table.probe_digest`):
    the sha256 of the normalized kernel checks of the process
    (records.digest), computed from the output with the snapshot root and
    the probe directory masked (records.mask_text; they differ between the
    sides) after the records were validated as the unit's process (probe,
    kind, parameters, control switches = controls_of(unit)) and found to
    be this unit's (its probe module and T33_KIND). Raises
    ValueError (records.RecordError) for an unreadable, malformed or
    misplaced-path output, and for fewer than `unit["min_checks"]`
    checks."""
    masked = records.mask_text(text, root, probe_dir)
    summary = records.validate(masked, controls=controls_of(unit),
                               root=records.ROOT_MASK)
    want = (records.PROBE_OF_MODULE.get(unit["probe"]),
            (unit.get("env") or {}).get("T33_KIND"))
    if (summary["probe"], summary["kind"]) != want:
        raise ValueError("the records are of %s/%s, the unit is %s/%s" % (
            summary["probe"], summary["kind"], *want))
    found = records.normalized_checks(masked)
    if len(found) < unit.get("min_checks", 0):
        raise ValueError("%d check record(s), not %d" % (
            len(found), unit["min_checks"]))
    return records.digest(masked)


STATE0 = "bin/hol.state0"
STATE = "bin/hol.state"

UNITS = (
    probe("state0-empty", "startup", STATE0, "", 0, 0.25),
    probe("state-empty", "startup", STATE, "", 0, 0.3),
    probe("load-simpLib", "load", STATE0, "simpLib", 1, 0.6),
    probe("load-congLib", "load", STATE0, "congLib", 1, 0.7),
    probe("first-use", "use", STATE, "", 4, 0.5),
)
NAMES = tuple(u["name"] for u in UNITS)
BY_NAME = {u["name"]: u for u in UNITS}
# The unit of the live negative control.
CONTROL_UNIT = "load-simpLib"
HEAPS = tuple(sorted({u["heap"] for u in UNITS}))
# hol.state is built on hol.state0.
HEAP_PARENTS = {STATE: STATE0}
PROBES = tuple(sorted({u["probe"] for u in UNITS}))
