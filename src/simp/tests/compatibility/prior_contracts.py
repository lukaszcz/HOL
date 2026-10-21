"""Prior assertion inputs, not expected-failure normalization.

Only process-ending driver calls are adapted to the paired completion protocol.
Every original assertion and observation remains byte-for-byte in its input.
"""
import gzip
import re
from pathlib import Path

COUNTS = {"PriorOriginal": 73, "PriorTraversal": 47,
          "PriorExclusion": 929, "PriorNative": 630}
LIMIT_CHECKS = [
    "zero limit returns reflexivity",
    "one limit retains root after failed solver",
    "one limit exact failed-attempt callbacks",
    "solver failure rolls back spent traversal allowance",
    "two limit exact callback order",
    "failed condition restores enclosing sibling allowance"]
FIXTURES = ("PriorOriginal", "PriorTraversal", "PriorExclusion", "PriorLimits")
ANSI = re.compile(r"\x1b\[[0-9;]*m")


def semantic_stream(text):
    """Ordered checks, observations and warning text; retain duplicate cases.

    Strip terminal presentation and testutils CPU/GC displays ONLY on OK lines.
    Compiler diagnostics and theory build timing are retained in raw receipts,
    not classified as simplifier observations. No warning/OBS text is edited.
    """
    result = []
    pending = None
    for raw in text.splitlines():
        line = ANSI.sub("", raw)
        if line.startswith("OBS ") or line.startswith("<<HOL warning:"):
            result.append(line)
        # Monitoring may interrupt tprint/OK with one or several trace lines.
        # Keep the label until its actual OK, not merely the label's presence.
        if " ..." in line and not line.startswith(("OBS ", "@@PAIR")):
            pending = re.sub(r" +", " ", line.split(" ...", 1)[0])
        if line.endswith("OK") and pending is not None:
            result.append(pending + " ... OK")
            pending = None
    return result


def historical(here, fixture):
    names = {"PriorOriginal": "develop-legacy.log",
             "PriorTraversal": "develop-traversal.log.gz",
             "PriorExclusion": "develop-exclusion.log.gz",
             "PriorNative": "native-selftest.log.gz"}
    p = here.parent / "performance/review-20261021" / names[fixture]
    data = p.read_bytes()
    return semantic_stream((gzip.decompress(data) if p.suffix == ".gz"
                            else data).decode())


def inputs(here, repo):
    return [Path(__file__), here / "test_prior.py", here / "coverage_ledger.py",
            here / "coverage-ledger.json.gz",
            here / "inputs/develop/selftest.sml",
            *sorted((here.parent / "contracts").glob("*.sml")),
            repo / "src/simp/src/selftest.sml",
            *sorted((here.parent / "performance/review-20261021").glob(
                "*legacy.log")),
            *[here.parent / "performance/review-20261021" / n for n in
              ("develop-traversal.log.gz", "develop-exclusion.log.gz",
               "native-selftest.log.gz")]]


def install(here, repo, dst, require):
    for p in (here.parent / "contracts").glob("*.sml"):
        (dst / p.name).write_bytes(p.read_bytes())
    original = (here / "inputs/develop/selftest.sml").read_text()
    sources = {"PriorOriginal": original,
               "PriorTraversal": (dst / "RunTraversalContracts.sml").read_text(),
               "PriorExclusion": (dst / "RunExclusionContracts.sml").read_text()}
    for name, text in sources.items():
        ending = ("val _ = LegacyFailures.finish ();" if name == "PriorExclusion"
                  else "val _ = OS.Process.exit OS.Process.success"
                  if name == "PriorTraversal"
                  else "val _ = exit_count0 failcount")
        require(text.count(ending) == 1 and text.rstrip().endswith(ending),
                "unexpected prior driver ending: " + name)
        # Only the final process exit becomes a counted completion assertion.
        completion = ('val _ = Paired.check "' + name + ' completed" ' +
                      ('(!failcount = 0)' if name in
                       ("PriorOriginal", "PriorNative") else 'true') + '\n')
        if name == "PriorExclusion":
            completion = ('val _ = LegacyFailures.observe '
                          '"assertion.result" "pass";\n' + completion)
        (dst / (name + ".sml")).write_text(
            text[:text.index(ending)] + completion)
    with (dst / "Holmakefile").open("a") as out:
        out.write("\npaired.exe: PriorLimits.uo " +
                  " ".join(n + ".uo" for n in sources) + "\n")


def expectation(fixture):
    return {"target": fixture, "modules": ("Traverse", "simpLib"),
            "signatures": [], "red": False,
            "observations": ([["check", s, "pass"] for s in LIMIT_CHECKS]
                             if fixture == "PriorLimits" else
                             [["check", fixture + " completed", "pass"]])}


def validate(here, fixture, text, require):
    stream = semantic_stream(text)
    if fixture == "PriorLimits":
        require(stream == [s + " ... OK" for s in LIMIT_CHECKS],
                "changed supplementary limit contracts")
        return {"checks": len(LIMIT_CHECKS), "observations": 0,
                "stream": stream, "outcome": "legacy-equal-supplement"}
    # Completion protocol check is additional to the prior checks, not a case.
    footer = fixture + " completed ... OK"
    require(stream and stream[-1] == footer, "missing prior completion check")
    stream = stream[:-1]
    expected = historical(here, fixture)
    require(sum(s.endswith("OK") and not s.startswith("OBS ")
                for s in stream) == COUNTS[fixture], "wrong prior case count")
    require(stream == expected, "changed ordered prior contracts: " + fixture)
    require("FAILED!" not in text, "prior assertion failed")
    return {"checks": COUNTS[fixture],
            "observations": sum(s.startswith("OBS ") for s in stream),
            "stream": stream, "outcome": "legacy-equal" if
            fixture != "PriorNative" else "branch-only-native"}
