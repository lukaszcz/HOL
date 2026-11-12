"""Complete focused-suite observations, not just successful .uo production."""
import prior_contracts as prior
from run_paired import require

# Source-tied check counters emitted by the maintained SML launchers. These
# are supplementary suites, not replacements for the 2,153 frozen ledger IDs.
SUITES = {
    "traverse-ext": (131, ["TraverseExt focused checks: 131"]),
    "cond-rewr-ext": (105, ["Cond_rewrExt focused checks: 105"]),
    "congruence-ext": (61, ["Ordinary congruence focused checks: 4",
                           "Congruence extension focused checks: 57"]),
    "simp-ext": (2813, ["simpExtLib focused checks: 92",
        "TRACKED_COMPILER_CHECKS=174",
        "TASK19_EXTENSION_EXCLUSIONS_OK checks=159",
        "simpExtLib strategy checks: 186; executed validations: 63",
        "TASK20_EXTENSION_TACTICS_OK checks=88 validations=18",
        "SOURCE_VIEW_BUNDLE_CHECKS=407", "DERIVATION_CHECKS=1392",
        "TraverseExt lifetime checks: 315"]),
    "standard-recipes": (118, ["STANDARD_RECIPE_CHECKS=118"]),
    "split-lifecycle": (2197, ["OBS repair=pass"]),
}


def validate(name, text):
    expected, footers = SUITES[name]
    require(text.endswith("\n"), "truncated focused output: " + name)
    stream = prior.semantic_stream(text)
    count = sum(s.endswith(" ... OK") and not s.startswith("OBS ")
                for s in stream)
    require(count == expected, "incomplete focused checks: " + name)
    for footer in footers:
        require(text.splitlines().count(footer) == 1,
                "missing/duplicated focused completion: " + footer)
    if name == "split-lifecycle":
        for observation, count in (("OBS result=pass", 22),
                                   ("OBS heap=saved", 1),
                                   ("OBS heap=reloaded", 1)):
            require(text.splitlines().count(observation) == count,
                    "missing lifecycle scenario: " + observation)
    require("FAILED!" not in text, "focused assertion failed: " + name)
    return {"checks": expected, "completions": footers}
