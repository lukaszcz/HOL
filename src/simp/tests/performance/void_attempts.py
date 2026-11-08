"""The no-redraw rule for the attempts of a judged timing table, shared by
the TASK30 and TASK31 dispositions.

A table is measured once: every attempt of it in the ledger is either
judged (the `attempt` of the output a disposition is given, or of that
stage's first stage) or void, and a void attempt admitted no measurement in
any cell. An attempt that measured, or may have (left open, resumed, closed
more than once or otherwise), is refused: it needs a new policy decision, and
the settings are not drawn again beside it. `attempts_of` applies the rule
to the ledger of an engine (`timing_grid.Grid`) and returns the attempts;
`void_failure` and `runner_failure` say why an attempt is not void. Both
dispositions seal this module in their `CODE` (PROTOCOL.md, "Seal histories").
"""
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import timing_grid as tg


def runner_failure(folder, name):
    """None when the unpacked archive `folder` of the cell `name` shows no
    measurement, else the text of the condition it fails: acceptance's own
    `success` is false; no command it recorded timed out, and each left a
    runner manifest in the folder of its `--output` (one killed while
    measuring leaves none, but receipts); and no runner manifest, of a
    command or not, records an admitted run (`runs` empty, `success`
    false)."""
    report = a.load(folder / "acceptance.json")
    if report.get("success") is not False:
        return "the acceptance of %s did not fail (success %r)" % (
            name, report.get("success"))
    commands = report.get("commands")
    if not isinstance(commands, list):
        return "the acceptance of %s records no list of commands" % name
    for command in commands:
        if not isinstance(command, dict) or \
                command.get("timed_out") is not False:
            return ("a command of %s timed out, or its receipt does not "
                    "say it did not: its runner may have measured" % name)
        argv = command.get("argv")
        if not isinstance(argv, list) or "--output" not in argv[:-1]:
            return "a command of %s names no --output" % name
        where = Path(argv[argv.index("--output") + 1]).name
        if not (folder / where / "manifest.json").is_file():
            return ("the archive of %s has no runner manifest in %s (a "
                    "runner killed while measuring leaves none)" % (
                        name, where))
    for manifest in sorted(folder.rglob("manifest.json")):
        found = a.load(manifest)
        if found.get("runs") != [] or found.get("success") is not False:
            return ("the archive of %s holds a runner manifest that "
                    "records an admitted run (%s)" % (
                        name, manifest.relative_to(folder)))
    return None


def void_failure(new, key, output, row=None):
    """None when the attempt `key` (id, stage), whose ledger output is `output`
    and whose ledger row (`Ledger.attempts`) is `row`, is void, else the
    text of the condition it fails. Void: the output directory exists
    and holds the inventory of that attempt, which has a row for every
    cell it measures (those of the table for a first stage, those of its
    own plan for a second); every row is a protocol failure (`protocol` present
    and false) whose archive exists and is the sealed one and shows no
    measurement (`runner_failure`); and the ledger has no resume line for
    the attempt (a resumed attempt may have drawn samples in a cell it
    cleared) and exactly one close line, whose status is `inconclusive`,
    the status of a grid in which every cell is a protocol failure
    (`timing_grid` summary: no cell passes or fails). A second stage closes
    with the combined status of both stages, so a void second stage is
    accepted only when its first stage has no fail; a fail there is final
    and the later stage blocks anyway. An attempt left open, resumed, closed
    more than once or closed otherwise may have measured."""
    if output is None or not Path(output).is_dir():
        return "its output directory is missing"
    output = Path(output)
    if not (output / "inventory.json").is_file():
        return "its output has no inventory.json"
    inventory = a.load(output / "inventory.json")
    if inventory.get("attempt") != key[0]:
        return "the output holds attempt %s" % inventory.get("attempt")
    runs = inventory.get("runs")
    if not isinstance(runs, list) or not all(
            isinstance(r, dict) for r in runs):
        return "its inventory has no list of runs"
    cells = [(r.get("case"), r.get("size")) for r in runs]
    if key[1] == "second":
        plan = inventory.get("plan")
        if not isinstance(plan, list) or not all(
                isinstance(p, list) and len(p) > 1 for p in plan):
            return "its inventory has no plan"
        want, what = {(p[0], p[1]) for p in plan}, "its plan names"
    else:
        want, what = set(new.t.keys()), "the table measures"
    if set(cells) != want or len(cells) != len(want):
        return ("its inventory has rows for %d cell(s), not each of the "
                "%d %s" % (len(set(cells)), len(want), what))
    for r in runs:
        if r.get("protocol") is not False:
            return ("the row of %s-%d is not a protocol failure (protocol "
                    "%r)" % (r["case"], r["size"], r.get("protocol")))
    for r in runs:
        name = "%s-%d" % (r["case"], r["size"])
        try:
            archive = a.safe_child(output, r.get("archive"))
        except (ValueError, OSError):
            return "the archive of %s is missing" % name
        if a.seal(archive) != r.get("seal"):
            return "the archive of %s is not the sealed one" % name
        with tempfile.TemporaryDirectory(prefix="void-attempt-") as scratch:
            folder = Path(scratch) / "unpacked"
            tg.bundle.unpack(archive, folder)
            failed = runner_failure(folder, name)
            if failed is not None:
                return failed
    status = row["status"] if row else None
    if status is None or status == "interrupted":
        return "its ledger has no close (it was left open)"
    if row["resumed"]:
        return ("it was resumed: a resumed attempt may have drawn samples "
                "in the cell it cleared")
    if row["statuses"] != ["inconclusive"]:
        if len(row["statuses"]) > 1:
            return ("it closed more than once, as %s: a repeated "
                    "attempt may have measured" % ", ".join(
                        row["statuses"]))
        if status == "fail" and key[1] == "second":
            return ("its ledger closes it fail: a second stage closes "
                    "with the combined status of both stages, so a fail "
                    "in its first stage is final and blocks the "
                    "table's later stage, whatever this stage measured")
        return ("its ledger closes it %s, not inconclusive, the status of "
                "a grid whose every cell is a protocol failure" % status)
    return None


def attempts_of(args, new, judged):
    """Every attempt of the table `new` in the ledger: the judged ones
    (`judged`: {attempt id: output directory} of the follow-up's final
    stage and, where it is a second stage, of its first) and the others,
    which must be void (`void_failure`): no cell of them admitted a
    measurement, so they are no outcome and the settings may be run again as
    a new attempt. An attempt id is of one output (every output its open,
    resume and close lines name), and a judged one is of the output named
    for it. A void attempt has no resume line and one close line,
    `inconclusive`; a second stage closes with the combined status of both
    stages, so a void one is accepted only when its first stage has no
    fail (a fail there blocks the later stage anyway). Any other attempt, an
    interrupted or resumed one included, may have measured, and is
    refused: it needs a new policy decision, or the option that names
    the grid names the wrong stage (name the final one). [{attempt,
    status, output, judged, void}], in the order the ledger names them."""
    path = new.attempts_file(args, False)
    a.require(path is not None and Path(path).is_file(),
              "no attempts ledger: %s" % path)
    state = tg.Ledger(path)
    table, family = new.t.name, new.t.family
    where = {}
    for record in state.records:
        key = (record.get("attempt"), record.get("stage"))
        if record["event"] in ("open", "resume", "close") and \
                record.get("table", family) == table:
            outputs = where.setdefault(key, [])
            if record.get("output") not in outputs:
                outputs.append(record.get("output"))
    found = []
    for key, row in state.attempts(table, family).items():
        outputs = where.get(key, [])
        a.require(len(outputs) == 1,
                  "attempt %s of table %s ran in %s output: %s; one "
                  "attempt is of one output, and a copy of a grid resumed "
                  "is a second draw beside it" % (
                      key[0], table, "more than one" if outputs else "no",
                      ", ".join(map(str, outputs))))
        output = outputs[0]
        entry = dict(attempt=key[0], status=row["status"], output=output,
                     judged=key[0] in judged, void=False)
        if entry["judged"]:
            a.require(output is not None and
                      Path(output).resolve() == judged[key[0]],
                      "attempt %s of table %s is judged, from %s, but "
                      "the ledger has it in %s" % (
                          key[0], table, judged[key[0]], output))
        else:
            failed = void_failure(new, key, output, row)
            a.require(
                failed is None,
                "attempt %s of table %s (status %s, output %s) is not "
                "void: "
                "%s; only a void attempt (no admitted measurement in any "
                "cell) may stand beside the judged one; anything else "
                "needs a new policy decision, or the option that names "
                "the grid does not name the table's final stage (name "
                "the final stage; a first stage named while its second "
                "stage exists leaves the second unjudged)" % (
                    key[0], table, row["status"], output, failed))
            entry["void"] = True
        found.append(entry)
    return found
