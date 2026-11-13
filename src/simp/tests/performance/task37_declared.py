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
           both kinds. Written as JSON; refuses a value that varies or an
           exclusive part that grows
  fill     writes the observation into the placeholder (and, with --cand,
           the candidate pin), and refuses unless the declaration is valid
           afterwards

How the value is measured and committed (TASK37 recipe, before the pilot):

  1. on the TASK37 snapshots, run a throwaway storage `smoke` twice under
     `--declared task37_declared.json` (placeholder): the registry units
     compute U on bin/hol.state without a declared value, as information;
  2. `task37_declared.py observe --declared ... --manifest M RUN1 RUN2
     --out observation.json` (it replays each run first);
  3. `task37_declared.py fill --declared ... --observation observation.json
     [--cand PIN]`, review the diff;
  4. commit task37_declared.json ALONE. The declaration is sealed by the
     pilot, the controls and the counts (`task33_storage.py predeclare`);
     those and the decision runs come after this commit, and the throwaway
     smokes are information runs of the ledger (listed by dispose).

An observed total change that is not a positive integer, an exclusive part
that grows, or a value that differs between processes is a finding about
the candidate, not something to declare: the tool refuses.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import task33_offline as offline
import task33_records as records

DECLARED = HERE / "task37_declared.json"
SCHEMA = "task37-s2-observation-v1"


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


def observation(groups, heap, kinds):
    """The S2 observation of the registry units of `kinds`.
    `groups`: {kind: {"base": [process summary], "cand": [...]}}, a
    process summary carrying `anchored` (task33_records.check_anchored).
    Returns {heap, kinds, value, observed}."""
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
                observed=dict(
                    base=base["total"], cand=cand["total"],
                    d_base=base["d"], d_cand=cand["d"],
                    exclusive={n: [base["rows"][n], cand["rows"][n]]
                               for n in base["rows"]},
                    processes_per_side_per_kind=count,
                    repeats_per_process=records.REPEATS))


def fill(declared, obs, cand=None):
    """The declaration with the placeholder filled (a new dict); refuses
    one that is not valid afterwards."""
    require(obs.get("schema") == SCHEMA, "not an S2 observation")
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
    if cand is not None:
        a.exact_pin(cand)
        new["cand"] = cand
    bad = problems(offline.join_text(new))
    require(not bad, "the filled declaration is not valid: " +
            "; ".join(bad))
    return new


def write(path, data):
    path = Path(path)
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(data, indent=2) + "\n")
    tmp.replace(path)


def observe_folders(folders, manifest, declared, heap=None):
    """The observation of the finished storage stages in `folders`
    (replayed first). Needs the snapshots' manifest only where a stage
    moved from it."""
    import task32_downstream as d
    import task33_storage as storage
    d.use_table(storage.TABLE)
    entry = entry_of(declared, heap)
    groups = {k: {"base": [], "cand": []} for k in entry["kinds"]}
    for folder in folders:
        folder = Path(folder).resolve(strict=True)
        storage.replay_one(folder, manifest=manifest)
        report = a.load(folder / "downstream.json")
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
    return observation(groups, entry["heap"], entry["kinds"])


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
    f.add_argument("--cand")
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
            offline.use_declared(args.declared)
            obs = observe_folders(args.folders, args.manifest, declared)
            with args.out.open("x") as stream:
                stream.write(json.dumps(obs, indent=2) + "\n")
            print("S2 total change %+d words: %s" % (obs["value"], args.out))
            return 0
        obs = json.loads(args.observation.read_text())
        write(args.declared, fill(
            json.loads(args.declared.read_text()), obs, args.cand))
        print("filled %s: commit it alone" % args.declared)
        return 0
    except (Refusal, ValueError, OSError) as error:
        print("REFUSED: %s" % error, file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
