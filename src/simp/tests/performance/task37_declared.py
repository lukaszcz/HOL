#!/usr/bin/env python3
"""TASK37 re-declaration of TASK33's reviewed data for the final candidate.

`task37_declared.json` (schema `task33-declared-v4`, the same shape as
`task33_declared.json`) declares the final candidate. TASK33's file stays
unchanged for the kept r4 records; the TASK33 drivers take the TASK37 one
through `--declared` (`task33_storage.py`, `task33_offline.py`). Everything
but the S2 closure-total change is reviewed data, derived from git (blobs)
and the TASK36 `bin/build -t -F` logs (`log_counts`). The S2 change is
measured live, so the file carries a placeholder
(`s2.total_delta[0].pending`, `value` and `observed` null) until it is
filled; every gate refuses a placeholder (`task33_offline.shape_problems`,
`task33_rules.total_deltas`).

  check    the problems of a declaration (`--final`: exit 1 unless there
           are none, i.e. the placeholder is filled)
  observe  the S2 observation of finished TASK33 storage stages (a smoke
           run is enough: one process per side and kind; give two smoke
           runs for the TASK33 k = 2): per side the closure total U, D and
           every exclusive part of the registry units of the entry's heap
           and kinds, each constant over the repeats, the processes and
           both kinds. The stages must all be of one base, one candidate
           and one snapshot manifest, which the observation records.
           Written as JSON; refuses a value that varies or an exclusive
           part that grows, and a `--declared` that is not the one the
           `task37-t33` table fixes (the pre-fill file of the recipe below
           differs from it in the S2 closure total alone)
  fill     writes the observation into the placeholder, and refuses unless
           the observation's base is the declaration's, its candidate the
           declared one or one with the same tree outside the performance
           area, and the declaration is valid afterwards. The
           declaration's `cand` stays
           task37_cases.COMPILED_REF: the stages are measured at the stream
           clone's head, whose tree outside the performance area is the
           declared candidate's, which the storage driver accepts for the
           TASK37 table (`task33_storage.check_declared`)

How the value is measured and committed (TASK37 recipe, before the pilot):

  1. on the TASK37 snapshots, run a throwaway storage `smoke` twice under
     `--declared task37_declared.json` (placeholder): the registry units
     compute U on bin/hol.state without a declared value, as information;
  2. `task37_declared.py observe --declared ... --manifest M RUN1 RUN2
     --out observation.json` (it replays each run first);
  3. `task37_declared.py fill --declared ... --observation
     observation.json`, review the diff;
  4. commit task37_declared.json ALONE. The declaration is sealed by the
     pilot, the controls and the counts (`task33_storage.py predeclare`);
     those and the decision runs come after this commit, and the throwaway
     smokes are information runs of the ledger (listed by dispose).

After the fill the declaration's seal has changed, so the throwaway smokes
(made under the placeholder) no longer replay: `predeclare` needs a new
smoke, and a pilot and controls, made under the filled declaration. To
derive the observation again later, give `observe` the pre-fill file
(`git show COMMIT~1:src/simp/tests/performance/task37_declared.json` into
a file, as `--declared`), because the throwaway smokes are sealed with it.

An observed total change that is not a positive integer, an exclusive part
that grows, or a value that differs between processes is a finding about
the candidate, not something to declare: the tool refuses.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import task33_offline as offline
import task33_records as records

DECLARED = HERE / "task37_declared.json"
SCHEMA = "task37-s2-observation-v2"
TABLE = "task37-t33"  # the table whose stages are observed


class Refusal(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise Refusal(message)


def problems(declared):
    """What the gates would refuse in the declaration (the shape, and the
    counts), as texts."""
    return offline.shape_problems(declared) + \
        offline.count_problems(declared)


def entry_of(declared, heap=None):
    entries = declared["s2"]["total_delta"]
    found = [e for e in entries if heap is None or e["heap"] == heap]
    require(len(found) == 1, "%d total_delta entries for %s, not one" % (
        len(found), heap))
    return found[0]


def observation(groups, heap, kinds, pins=None):
    """The S2 observation of the registry units of `kinds`.
    `groups`: {kind: {"base": [process summary], "cand": [...]}}, a
    process summary carrying `anchored` (task33_records.check_anchored).
    `pins`: {base, cand, manifest} the stages measured, recorded. Returns
    {heap, kinds, value, observed, base, cand, manifest}."""
    require(sorted(groups) == sorted(kinds), "registry kinds %s observed, "
            "%s wanted" % (sorted(groups), sorted(kinds)))
    seen = {"base": [], "cand": []}
    count = None
    for kind in kinds:
        for side in seen:
            procs = groups[kind].get(side, [])
            require(procs, "no %s process of %s" % (side, kind))
            if count is not None:
                require(len(procs) == count, "the number of processes "
                        "differs between sides or kinds")
            count = len(procs)
            for p in procs:
                x = p["anchored"]
                require(x["total"] is not None and x["d"] is not None and
                        x["repeat_ok"], "%s %s: U is not computed or its "
                        "repeats disagree" % (kind, side))
                seen[side].append(dict(
                    total=x["total"][0], d=x["d"][0],
                    rows={n: v[0] for n, v in x["rows"].items()}))
    out = {}
    for side, procs in seen.items():
        for key in ("total", "d", "rows"):
            values = [json.dumps(p[key], sort_keys=True) for p in procs]
            require(len(set(values)) == 1, "%s: %s differs between the "
                    "processes or the kinds: %s" % (side, key,
                                                    sorted(set(values))))
        out[side] = procs[0]
    base, cand = out["base"], out["cand"]
    require(sorted(base["rows"]) == sorted(cand["rows"]),
            "the exclusive parts are not the same structures")
    grown = sorted(n for n in base["rows"]
                   if cand["rows"][n] > base["rows"][n])
    require(not grown, "an exclusive part grows (a finding, not a "
            "declaration): " + ", ".join(grown))
    value = cand["total"] - base["total"]
    require(value > 0, "the closure total does not grow (%d): nothing to "
            "declare, and a zero or negative change is not a valid "
            "total_delta" % value)
    return dict(schema=SCHEMA, heap=heap, kinds=list(kinds), value=value,
                **(pins or {}), observed=dict(
                    base=base["total"], cand=cand["total"],
                    d_base=base["d"], d_cand=cand["d"],
                    exclusive={n: [base["rows"][n], cand["rows"][n]]
                               for n in base["rows"]},
                    processes_per_side_per_kind=count,
                    repeats_per_process=records.REPEATS))


def same_tree_outside(repo, one, other):
    """Whether the revisions `one` and `other` have the same tree outside
    the performance area, in `repo`."""
    tg = offline.d.tg
    try:
        return tg.git_tree_outside(repo, one) == \
            tg.git_tree_outside(repo, other)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise Refusal("cannot compare the candidates %s and %s in %s: %s"
                      % (one, other, repo, error))


def fill(declared, obs, repo=None):
    """The declaration with the placeholder filled (a new dict; its `cand`
    is unchanged); refuses an observation of another base or of another
    candidate (the declared one, or one with the same tree outside the
    performance area, judged in `repo`, default the checkout of this
    code), and a declaration that is not valid afterwards."""
    require(obs.get("schema") == SCHEMA, "not an S2 observation")
    require(obs.get("base") == declared["base"], "the observation is of "
            "base %s, the declaration's is %s" % (
                obs.get("base"), declared["base"]))
    a.exact_pin(obs.get("cand"))
    require(obs["cand"] == declared["cand"] or same_tree_outside(
        Path(repo) if repo else HERE.parents[3], declared["cand"],
        obs["cand"]), "the observation is of candidate %s, whose tree "
            "outside the performance area is not that of the declared "
            "candidate %s" % (obs["cand"], declared["cand"]))
    new = json.loads(json.dumps(declared))
    entry = entry_of(new, obs["heap"])
    require(entry["kinds"] == obs["kinds"], "the observation is of kinds "
            "%s, the entry's are %s" % (obs["kinds"], entry["kinds"]))
    require(entry.get("pending"), "the entry is not a placeholder")
    entry.pop("pending")
    entry["value"] = obs["value"]
    entry["observed"] = obs["observed"]
    entry["mechanism"] = [
        "Measured live (task37_declared.py observe): the closure total U",
        "of bin/hol.state (state-empty and first-use) changes by",
        "+%d words, from %d to %d, with D (ThmAttribute and Cond_rewr," % (
            obs["value"], obs["observed"]["base"], obs["observed"]["cand"]),
        "structure and signature) %d to %d, and no exclusive part grows."
        % (obs["observed"]["d_base"], obs["observed"]["d_cand"]),
        "Only D's own code and type structure grow: no state, nothing per",
        "object."]
    bad = problems(offline.join_text(new))
    require(not bad, "the filled declaration is not valid: " +
            "; ".join(bad))
    return new


def write(path, data):
    path = Path(path)
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n")
    tmp.replace(path)


# What `fill` writes into an S2 total_delta entry (the rest is declared).
FILLED_KEYS = ("value", "observed", "pending", "mechanism")


def check_selected(path):
    """`observe` judges by the declaration the `task37-t33` table fixes: a
    contradicting `--declared` is refused, but for what `fill` writes into
    the S2 closure total entries (`FILLED_KEYS`: the declaration lacks them
    before `fill`; the throwaway smokes are sealed with the pre-fill file,
    which must be given to replay them)."""
    import task32_downstream as d
    fixed = Path(d.TABLES[TABLE].declared).resolve()
    if Path(path).resolve() == fixed:
        return

    def without_total(file):
        # only what `fill` writes is blanked, per entry of total_delta:
        # `value`, `observed`, `pending` and `mechanism`; the rule, heap,
        # kinds, unit and paths of an entry stay compared
        data = json.loads(Path(file).read_text())
        data["s2"] = dict(data["s2"], total_delta=[
            {k: v for k, v in entry.items() if k not in FILLED_KEYS}
            for entry in data["s2"]["total_delta"]])
        return data
    try:
        same = without_total(path) == without_total(fixed)
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        same = False
    require(same, "--declared %s contradicts table %s, which fixes %s (the "
            "filled S2 closure total alone may differ)" % (path, TABLE, fixed))


def observe_folders(folders, manifest, declared, heap=None):
    """The observation of the finished storage stages in `folders`
    (replayed first), which must all be of one base, one candidate and one
    snapshot manifest (recorded in the observation). Needs the snapshots'
    manifest only where a stage moved from it. The TASK37 storage table
    (`TABLE`) is the active one of both drivers meanwhile, and both are
    restored."""
    import task32_downstream as d
    import task33_storage as storage
    previous = d.ACTIVE.name
    previous_storage = storage.use_storage_table(TABLE)
    d.use_table(TABLE)
    try:
        return observe_stages(storage, folders, manifest, declared, heap)
    finally:
        d.use_table(previous)
        storage.use_storage_table(previous_storage)


def observe_stages(storage, folders, manifest, declared, heap):
    """`observe_folders`, with the storage module `storage`."""
    entry = entry_of(declared, heap)
    groups = {k: {"base": [], "cand": []} for k in entry["kinds"]}
    pinned = set()
    for folder in folders:
        folder = Path(folder).resolve(strict=True)
        storage.replay_one(folder, manifest=manifest)
        report = a.load(folder / "downstream.json")
        pinned.add((report["base"], report["cand"],
                    json.dumps(report["manifest"], sort_keys=True)))
        plan = storage.check_plan(report)
        receipts = {e["receipt"]: storage.check_run(folder, report, e)
                    for e in report["runs"]}
        loaded = storage.check_redraws(report, plan, receipts)
        for name, sides in storage.grouped(report, loaded).items():
            kind = name[len("registry-"):] if name.startswith(
                "registry-") else None
            if kind in groups and report["units"][name]["heap"] == \
                    entry["heap"]:
                for side, procs in sides.items():
                    groups[kind][side] += procs
    require(len(pinned) == 1, "the stages are not of one base, one "
            "candidate and one snapshot manifest: %d combinations" %
            len(pinned))
    base, cand, manifest_seal = next(iter(pinned))
    return observation(groups, entry["heap"], entry["kinds"], dict(
        base=base, cand=cand, manifest=json.loads(manifest_seal)))


def build_parser():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="command", required=True)
    for name in ("check", "observe", "fill"):
        s = sub.add_parser(name)
        s.add_argument("--declared", type=Path, default=DECLARED)
    sub.choices["check"].add_argument("--final", action="store_true")
    o = sub.choices["observe"]
    o.add_argument("--manifest", type=Path)
    o.add_argument("--out", type=Path, required=True)
    o.add_argument("folders", type=Path, nargs="+")
    f = sub.choices["fill"]
    f.add_argument("--observation", type=Path, required=True)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        declared = offline.load_declared(args.declared)
        if args.command == "check":
            bad = problems(declared)
            for line in bad:
                print(line)
            print("%s: %d problem(s)" % (args.declared, len(bad)))
            return 1 if bad and args.final else 0
        if args.command == "observe":
            check_selected(args.declared)
            with offline.using_declared(args.declared):
                obs = observe_folders(args.folders, args.manifest, declared)
            with args.out.open("x") as stream:
                stream.write(json.dumps(obs, indent=2) + "\n")
            print("S2 total change %+d words: %s" % (obs["value"], args.out))
            return 0
        obs = json.loads(args.observation.read_text())
        write(args.declared, fill(
            json.loads(args.declared.read_text()), obs))
        print("filled %s: commit it alone" % args.declared)
        return 0
    except (Refusal, ValueError, OSError) as error:
        print("REFUSED: %s" % error, file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
