"""Exact executed stage/proof observations; baseline is the contract.

Reviewed expectations are diagnostic reds, never compatibility passes. A repair
must select --candidate-behavior baseline, not regenerate either expectation.
"""
import json
import shutil

SCENARIOS = (
    "empty", "unmarked", "req0", "reqD", "req0_reqD", "reqD_req0",
    "req0_failure", "reqD_failure", "both_failure", "reqD_then_plain",
    "plain_then_reqD", "req0_then_reqD", "reqD_then_req0", "req0_then_plain",
    "bound0", "bound1", "bound2", "bound1_two_redex", "bound2_two_redex",
    "req0_bound1_two_redex", "installed_bound1", "reqD_bound1", "bound1_reqD",
    "malformed_bound", "reqD_malformed_bound", "ordered_subgoals", "hyp_rule",
    "closed", "grammar_context", "throw_construct", "throw_after",
    "throw_second", "throw_discarded", "late_fragment", "replaced_fragment",
    "rewound_fragment", "missing_fragment", "late_label", "label_order",
    "label_reference_order", "late_abbr", "reqD_then_abbr", "reqD_after_abbr")
CONTROLS = ("wrong conclusion", "foreign hypothesis", "oracle")


def shape(events):
    """Require every stage and real reconstruction, not just a final count.

    Term/type encodings preserve constants, variable names/types, hypotheses,
    assumption lists and subgoal order. Exact comparison is in runner.validate.
    """
    pending = iter(events)
    count = 0

    def take(kind, key):
        event = next(pending, None)
        if not (isinstance(event, list) and len(event) == 3 and
                event[:2] == [kind, key] and isinstance(event[2], str)):
            raise ValueError("missing/unordered stage: " + key)
        return event[2]

    def metric(key):
        value = take("observation", key)
        if not value.isdecimal() or str(int(value)) != value:
            raise ValueError("invalid inference/validation count: " + key)
        return int(value)

    def stage(key):
        metric(key + ".prims")
        take("observation", key + ".callbacks")
        return take("observation", key + ".outcome")

    for name in SCENARIOS:
        result = stage(name + ".construct")
        if result != "returned":
            if take("observation", name + ".uses") != "unavailable":
                raise ValueError("uses after failed construction")
        else:
            for use in ("first", "second"):
                key = name + "." + use
                if stage(key) == "returned":
                    take("observation", key + ".goals")
                    metric(key + ".proof.prims")
                    take("observation", key + ".proof.callbacks")
                    if take("check", key + " proof") != "pass":
                        raise ValueError("invalid reconstructed proof")
                    take("observation", key + ".theorem")
                    oracles = take("observation", key + ".oracles")
                    if oracles not in ("", "DISK_THM"):
                        raise ValueError("oracle in reconstructed proof")
                    count += 1
        if name == "reqD_malformed_bound":
            result = stage("negative_bound.argument")
            if result != "HOL_ERR(BoundedRewrites.MK_BOUNDED:negative bound)":
                raise ValueError("wrong argument-construction exception")
    for name in CONTROLS:
        if take("check", "validator " + name + " control") != "pass":
            raise ValueError("invalid validator control")
    if metric("validations.executed") != count:
        raise ValueError("reconstructions not executed")
    if next(pending, None) is not None:
        raise ValueError("unexpected staged observation")
    return count


def references(here, require, fingerprint):
    refs = json.loads((here / "staging/references.json").read_text())
    for name, spec in refs["inputs"].items():
        require(fingerprint(here / "staging" / name) == spec,
                "frozen staged contract changed: " + name)
    for flavor in ("baseline", "reviewed"):
        shape(json.loads((here / "staging" / (flavor + ".json")).read_text()))
    return refs


def install(here, dst):
    shutil.copyfile(here / "staging/Staging.sml", dst / "Staging.sml")
    with (dst / "Holmakefile").open("a") as out:
        out.write("\npaired.exe: Staging.uo\n")


def expectation(here, flavor):
    observations = json.loads((here / "staging" / (flavor + ".json")).read_text())
    shape(observations)
    return {"target": "Staging", "red": False, "warning": False,
            "expected_red": flavor != "baseline", "signatures": [],
            "modules": ["Traverse", "simpLib"],
            "observations": observations}
