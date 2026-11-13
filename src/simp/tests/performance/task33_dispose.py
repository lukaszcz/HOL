"""TASK33's two closing commands (design sections 3 and 5), run through
`task33_storage.py`:

  dispose            one disposition.json: the timing driver's disposition
                     (`task32_downstream.py --table task33 dispose`), the
                     S3 offline reports (audit, harvest, archive; their
                     seals, schemas and code seals verified) and the
                     storage stages' decisions, one decision per case id
                     and kind. Pass only if every gate passes; a row is
                     owed only while its contingency stage (extend, follow-
                     up) may still run, and an inconclusive row with no
                     stage left is blocked; the reported items, the process
                     redraws and the attributions still needed (a handoff
                     duty) are listed. The file is sealed
                     (disposition.json.seal).
  dispose-snapshots  after the last use: verify the snapshots, check that
                     the harvest and the api-audit receipt are sealed under
                     the evidence directory and that a sealed
                     disposition.json owes no stage, write an intent journal
                     (snapshot-disposal.intent.json; a repeated command
                     resumes it), remove exactly the paths the snapshot
                     manifest names (the two roots, their HOMEs, the
                     sequence copy, the scratch directory when no journal
                     is pending, the declared scratch root, the then empty
                     parents) and write snapshot-disposal.json. It never
                     uses `task32_snapshots.py discard` (that rewrites the
                     manifest whose seal the committed TASK32 counts carry)
                     and never deletes anything it was not told to.

Exit status as the drivers': 0 pass, 1 fail, 2 inconclusive or blocked, 3
refused (any inconsistency is a refusal before anything is removed).
"""
import json
import os
from pathlib import Path
import re
import shutil
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task32_downstream as d
import task33_offline as offline
import task33_rules as rules
import task33_storage as storage

SCHEMA = "task33-disposition-v2"
DISPOSAL_SCHEMA = "task33-snapshot-disposal-v1"
INTENT_SCHEMA = "task33-snapshot-disposal-intent-v1"
OFFLINE = storage.OFFLINE_COMMANDS
ATTRIBUTED = ("gc_cpu", "maxrss")  # the timing intervals scanned
LABELS = ("base", "cand")
GATE_ORDER = (rules.FAIL, rules.BLOCKED, rules.INCONCLUSIVE)


def timing_status(status, note):
    """(decision, owed) of a timing row from TASK32's `classify` (status,
    note): the one mapping of its contingencies. A "followup" row is
    inconclusive and owed the follow-up; the blocked row that says the
    second stage is owed (`d.NOTE_SECOND`) is inconclusive and owed
    `second` (the timing `extend` stage) until that stage has run, after
    which `classify` gives another status; every other blocked row is
    blocked and owes nothing."""
    if status == "followup":
        return rules.INCONCLUSIVE, "followup"
    if (status, note) == ("blocked", d.NOTE_SECOND):
        return rules.INCONCLUSIVE, "second"
    return {"pass": rules.PASS, "fail": rules.FAIL,
            "blocked": rules.BLOCKED}[status], None


def overall(decisions):
    """fail over blocked over inconclusive over pass."""
    return rules.worst(list(decisions))


def decision(case, kind, status, source, reason="", **more):
    return dict(case=case, kind=kind, decision=status, source=source,
                reason=reason, **more)


# ----------------------------------------------------------------- inputs

def expected_storage():
    """The (case, kind) a complete storage evidence decides: the keys the
    decision stages produce. S2 may be reported instead (not applicable in
    a heap); the others have no alternative."""
    keys = []
    for u in storage.REGISTRY:
        kind = u[len("registry-"):]
        keys += [("L1", kind), ("L3", kind), ("S2", kind)]
    keys += [("S1", g) for g in rules.GRAPH_GATED] + [("R1", "weak")]
    keys += [("R1", k) for k in rules.ORDINARY_RELEASE]
    keys += [("E1", "ext"), ("E2", "a"), ("E2", "b"), ("E2", "c")]
    keys += [("E1", "api-audit"), ("L3", "api-audit")]
    return keys


def timing_decisions(chain, disp):
    """L4 decisions: one per timing kind, from the disposition's rows
    (`timing_status`: a row owed the follow-up or the second stage is
    inconclusive and owes it; the timing driver classifies it again once
    the stage ran)."""
    out = []
    for unit, row in sorted(disp["workloads"].items()):
        status, owed = timing_status(row["status"], row["note"])
        out.append(decision(
            "L4", unit, status, "timing:" + row["stages"][-1]["stage"],
            row["note"] or "", stages=row["stages"], owed=owed))
    return out


def load_offline(paths):
    """{command: (report, seal)} of the S3 reports, each verified: schema,
    seal file, the code it was made by."""
    found = {}
    for path in paths:
        path = Path(path).resolve(strict=True)
        report = a.load(path)
        d.require(report.get("schema") == offline.SCHEMA,
                  "not an offline report: %s" % path)
        seal = a.seal(path)
        d.require(a.load(Path(str(path) + ".seal")) == seal,
                  "the seal of %s differs" % path)
        try:
            offline.check_code(report["code"])
        except (offline.Refusal, KeyError) as error:
            raise d.Refusal("%s: %s" % (path, error))
        d.require(report["command"] in OFFLINE and
                  report["command"] not in found,
                  "unexpected or repeated %s report" % report["command"])
        found[report["command"]] = (report, dict(path=str(path),
                                                 seal=seal))
    return found


def offline_decisions(found):
    """One decision per (case, check id) of the reports; a case combined
    in one check ("L1/S3") is decided in each of its cases. Missing
    reports and skipped checks are blocked decisions: no stage could
    resolve them."""
    out, attribution = [], []
    for command in OFFLINE:
        if command not in found:
            out.append(decision("offline", command, rules.BLOCKED,
                                "offline:" + command, "no %s report" %
                                command))
            continue
        report, _ = found[command]
        for check in report["checks"]:
            status = {"pass": rules.PASS, "fail": rules.FAIL,
                      "skipped": rules.BLOCKED}[check["status"]]
            for case in check["case"].split("/"):
                out.append(decision(case, check["id"], status,
                                    "offline:" + command, check["reason"]))
        if command == "archive":
            attribution += [x for x in report["data"].get("above", ())
                            if x.get("wholly_above_margin")]
    return out, attribution


def same_gate(chains):
    """Every chain is of one gate: pins, key, manifest."""
    first = chains[0][0]["report"]
    for chain in chains:
        r = chain[0]["report"]
        d.require(all(r[k] == first[k] for k in (
            "base", "cand", "key", "manifest")),
            "the stages are of different gates")


def reported_rows(chains):
    """{key: row} of the reported and unsupported rows (the outcomes'
    `reported` items that are decisions), the last stage's winning."""
    found = {}
    for chain in chains:
        for entry in chain:
            for key, r in entry["report"]["outcome"].get(
                    "reported", {}).items():
                if isinstance(r, dict) and "decision" in r:
                    found[key] = dict(r, stage=entry["stage"],
                                      attempt=entry["report"]["attempt"])
    return found


def storage_decisions(chains):
    """The decision of every (case, kind): the last stage that decided it,
    owed only while its stage may still run (`storage.settled_rows`);
    missing ones are blocked. Also the reported items per stage."""
    rows = {}
    reported = {}
    for chain in chains:
        for key, r in storage.settled_rows(chain).items():
            rows[key] = r
        for entry in chain:
            for k, v in entry["report"]["outcome"].get("reported",
                                                       {}).items():
                reported.setdefault(entry["stage"], {})[k] = v
    side_rows = reported_rows(chains)
    out = []
    for case, kind in expected_storage():
        key = rules.key_of(case, kind)
        r = rows.pop(key, None)
        if r is None:
            r = side_rows.pop(key, None)
            if r is not None:
                out.append(decision(case, kind, r["decision"],
                                    "storage:" + r["stage"], r["reason"],
                                    attempt=r["attempt"]))
                continue
            out.append(decision(case, kind, rules.BLOCKED, "storage",
                                "no evidence: the stage that decided it "
                                "did not run"))
            continue
        out.append(decision(case, kind, r["decision"],
                            "storage:" + r["stage"], r["reason"],
                            owed=r["owed"], attempt=r["attempt"]))
    for key, r in sorted(rows.items()):  # decided, not expected: listed
        out.append(decision(r["case"], r["kind"], r["decision"],
                            "storage:" + r["stage"], r["reason"],
                            owed=r["owed"], attempt=r["attempt"]))
    for key, r in sorted(side_rows.items()):  # reported, unsupported
        out.append(decision(r["case"], r["kind"], r["decision"],
                            "storage:" + r["stage"], r["reason"],
                            attempt=r["attempt"]))
    return out, reported


def process_redraws(chains):
    """Every try superseded in a storage stage: the processes redrawn, why
    (design 8.6), with the stage's attempt."""
    return [dict(attempt=entry["report"]["attempt"], stage=entry["stage"],
                 unit=e["workload"], side=e["side"], pair=e["pair"],
                 selection=e["selection"], redraw=e["redraw"],
                 reason=e["superseded"])
            for chain in chains for entry in chain
            for e in entry["report"]["runs"] if e.get("superseded")]


def timing_attribution(disp):
    """The timing chain's GC CPU and maxrss paired intervals scanned like
    the S3 archive's: the final stage's candidate intervals wholly above
    the policy margin owe an attribution."""
    out = []
    for unit, row in sorted(disp["workloads"].items()):
        last = row["stages"][-1]
        for metric in ATTRIBUTED:
            interval = last["intervals"].get(metric)
            if interval and interval[0] > 1:
                out.append(dict(
                    unit=unit, field=metric, low=interval[0],
                    stage=last["stage"], source="timing",
                    wholly_above_margin=interval[0] > offline.ABOVE))
    return out


def check_offline_identity(found, args):
    """The offline reports given are exactly the ones the storage counts
    were predeclared with, and the audit and the harvest were made against
    the declaration this process judges by (the archive report reads none:
    it is bound to the table, base and candidate the declaration names,
    `task33_storage.check_archive_binding`)."""
    counts = a.load(storage.storage_counts_path(args))
    absent = [c for c in OFFLINE if c not in found]
    d.require(not absent, "no %s report among --offline (the storage "
              "counts bound one of each)" % ", ".join(absent))
    for command in OFFLINE:
        d.require(found[command][1]["seal"] ==
                  counts["offline"][command]["seal"],
                  "the %s report is not the one the storage counts "
                  "bound" % command)
    storage.check_archive_binding(found["archive"][0],
                                  getattr(args, "repo", None))
    own = a.seal(offline.DECLARED)
    for command in ("audit", "harvest"):
        d.require(found[command][0].get("inputs", {}).get("declared") == own,
                  "the %s report was made against another declaration "
                  "than %s" % (command, offline.DECLARED.name))


def check_linear(chains, ledger):
    """The storage chains are linear: each stage names its predecessor
    (`storage.replay_chain` checks it), and no attempt of the gate that
    decided something is outside them (a branch: a second run, or a
    contingency another stage had already taken)."""
    stages = [c[0]["stage"] for c in chains]
    d.require(sorted(stages) in (["run"], ["audit", "run"]),
              "the storage chains are the run's and the audit's, once "
              "each: %s" % stages)
    key = chains[0][0]["report"]["key"]
    _, found = d.read_ledger(ledger, storage.LEDGER_TABLE)
    decided = {(i, st) for (i, st), row in found.items()
               if st in storage.DECISIVE and row["opens"][0]["key"] == key
               and any(c["status"] in d.DECISIONS.values()
                       for c in row["closes"])}
    listed = {(e["report"]["attempt"], e["stage"])
              for chain in chains for e in chain}
    extra = sorted(decided - listed)
    d.require(not extra, "a deciding attempt is outside the chains (a "
              "branch): %s" % ", ".join("%s (%s)" % x for x in extra))


def split_relocated(ledger, relocated):
    """{ledger table: its share of the --relocated entries}; an entry that
    names no information run of either table is a refusal."""
    state = d.tg.Ledger(ledger)
    shares = {}
    for table in (d.TABLE, storage.LEDGER_TABLE):
        names = {r["attempt"] for r in d.table_lines(state, table)
                 if r["event"] == "info"}
        shares[table] = {k: v for k, v in relocated.items() if k in names}
    unknown = sorted(set(relocated) - set().union(*shares.values()))
    d.require(not unknown, "--relocated names no information run of the "
              "ledger: " + ", ".join(unknown))
    return shares


def table_ledger(ledger, table, relocated):
    """R-1 for one ledger table: its attempts, its information runs (the
    reports of the controls read, `relocated` where moved)."""
    state, found = d.read_ledger(ledger, table)
    return dict(attempts=d.attempts_table(found, d.reasons(found)),
                info_runs=d.info_runs(state, relocated, table))


def dispose(args):
    """`task33_storage.py dispose`: the one, sealed, disposition.json."""
    relocated = d.parse_relocated(args.relocated)
    offline_found = load_offline(args.offline)
    check_offline_identity(offline_found, args)
    with d.using_table(storage.TABLE):
        timing_chain = d.replay_chain(
            args.timing_stage, args.ledger, args.timing_counts,
            args.timing_followup_counts, args.repo)
        ledger = args.ledger or d.ledger_path(
            timing_chain[0]["report"]["repo"])
        shares = split_relocated(ledger, relocated)
        timing_disp = d.disposition(
            timing_chain, ledger, args.timing_counts, shares[d.TABLE])
        storage_chains = [storage.replay_chain(
            s, args.ledger, args.repo, args.storage_counts,
            args.storage_followup_counts, args.timing_counts,
            args.manifest) for s in args.stage]
        same_gate([timing_chain] + storage_chains)
        check_linear(storage_chains, ledger)
        loading_ledger = table_ledger(ledger, d.TABLE, shares[d.TABLE])
        storage_ledger = table_ledger(
            ledger, storage.LEDGER_TABLE, shares[storage.LEDGER_TABLE])
    decisions = timing_decisions(timing_chain, timing_disp)
    stored, reported = storage_decisions(storage_chains)
    off, attribution = offline_decisions(offline_found)
    decisions += stored + off
    attribution += [x for x in timing_attribution(timing_disp)
                    if x["wholly_above_margin"]]
    gates = [x["decision"] for x in decisions if x["decision"] in
             rules.GATES]
    status = overall(gates)
    cands = {e["report"]["cand"] for e in timing_chain} | {
        e["report"]["cand"] for c in storage_chains for e in c}
    d.require(len(cands) == 1, "the stages measured different candidates: "
              + ", ".join(sorted(cands)))
    data = dict(
        schema=SCHEMA, status=status, candidate=cands.pop(),
        **d.disposition_table(), decisions=decisions,
        counts={s: sum(1 for x in decisions if x["decision"] == s)
                for s in rules.GATES + (rules.REPORTED, rules.UNSUPPORTED)},
        owed=[x for x in decisions if x.get("owed")],
        reported=reported, attribution_needed=attribution,
        process_redraws=process_redraws(storage_chains),
        timing=timing_disp, ledgers=dict(loading=loading_ledger,
                                         storage=storage_ledger),
        storage_chains=[[dict(stage=e["stage"], run=str(e["folder"]),
                              seal=e["info"]["seal"],
                              attempt=e["report"]["attempt"])
                         for e in chain] for chain in storage_chains],
        offline={c: s for c, (_, s) in offline_found.items()},
        code=d.code_seals())
    with args.out.open("x") as stream:
        stream.write(d.dumps(data))
    with Path(str(args.out) + ".seal").open("x") as stream:
        stream.write(d.dumps(a.seal(args.out)))
    print("TASK33 disposition: %s %s" % (status, json.dumps(data["counts"])))
    return {"pass": 0, "fail": 1}.get(status, 2)


# ------------------------------------------------------ dispose-snapshots

def tree_bytes(path):
    total = 0
    for top, dirs, files in os.walk(path):
        for name in files:
            with_path = os.path.join(top, name)
            if not os.path.islink(with_path):
                total += os.lstat(with_path).st_size
    return total


def sealed_evidence(evidence):
    """The harvest and the api-audit receipt under `evidence`, both
    sealed: {harvest, audit}; refuses when either is absent or changed."""
    evidence = Path(evidence).resolve(strict=True)
    harvests = sorted(evidence.rglob("harvest.json"))
    d.require(len(harvests) == 1, "%d harvest reports under %s, not one" %
              (len(harvests), evidence))
    path = harvests[0]
    report = a.load(path)
    d.require(report.get("schema") == offline.SCHEMA and
              report.get("command") == "harvest" and
              report.get("success") is True,
              "the harvest is not a successful offline report")
    d.require(a.load(Path(str(path) + ".seal")) == a.seal(path),
              "the harvest seal differs")
    audits = []
    for run in sorted(evidence.rglob("downstream.json")):
        data = a.load(run)
        if data.get("schema") == storage.SCHEMA and \
                data.get("mode") == "audit" and data.get("success"):
            audits.append((run, data))
    d.require(len(audits) == 1, "%d successful api-audit stages under %s, "
              "not one" % (len(audits), evidence))
    run, data = audits[0]
    folder = run.parent
    receipt = a.safe_child(folder, data["audit"]["receipt"])
    d.require(a.seal(receipt) == data["audit"]["receipt_seal"],
              "the api-audit receipt is not the sealed one")
    d.require(a.load(receipt).get("pass") is True,
              "the api-audit receipt is not a pass")
    return dict(harvest=dict(path=str(path), seal=a.seal(path)),
                audit=dict(run=str(run), seal=a.seal(run),
                           receipt=str(receipt),
                           receipt_seal=data["audit"]["receipt_seal"]))


def sealed_disposition(evidence):
    """The one disposition.json under `evidence`, sealed, a disposition of
    this schema that owes nothing (no row owed a stage that may still run;
    the attributions it lists are a handoff duty, not a condition):
    {path, seal}."""
    found = sorted(Path(evidence).rglob("disposition.json"))
    d.require(len(found) == 1, "%d disposition.json under %s, not one" %
              (len(found), evidence))
    path = found[0]
    d.require(a.load(Path(str(path) + ".seal")) == a.seal(path),
              "the disposition seal differs")
    data = a.load(path)
    d.require(data.get("schema") == SCHEMA, "not a %s file" % SCHEMA)
    d.require(not data["owed"], "the disposition still owes: %s" % (
        ["%s %s (%s)" % (x["case"], x["kind"], x["owed"])
         for x in data["owed"]],))
    return dict(path=str(path), seal=a.seal(path))


def removal_plan(manifest, repo, scratch_root):
    """The paths to remove, from the manifest and nothing else, each
    checked: ({kind: [(path, how)]}, the parents to remove if empty).
    Refuses a path that is not exactly where the snapshot driver puts it."""
    repo = Path(repo).resolve(strict=True)
    agent = repo / ".agent-files"
    snaps, scratch = set(), set()
    plan = []
    for label in LABELS:
        side = manifest["sides"][label]
        root, home = Path(side["root"]), Path(side["home"])
        d.require(root.name == label and root.parent.name == "task32" and
                  root.parent.parent.name == "snapshots" and
                  root.parent.parent.parent == agent,
                  "the %s root is not below %s/snapshots/task32: %s" % (
                      label, agent, root))
        d.require(re.fullmatch(r"home-%s-a[0-9]+" % label, home.name) and
                  str(home.parent) == side["scratch"] and
                  home.parent == agent / "scratch" / "task32",
                  "the %s HOME is not a task32 scratch home: %s" % (
                      label, home))
        plan += [(root, "tree"), (home, "tree")]
        snaps.add(root.parent)
        scratch.add(home.parent)
        seq = Path(side["sequence"]["path"])
        d.require(re.fullmatch(r"task32-%s\.seq" %
                               side["sequence"]["sha256"], seq.name) and
                  seq.parent == agent / "scratch" / "task32",
                  "the sequence copy is not where the snapshot driver "
                  "puts it: %s" % seq)
        if (seq, "file") not in plan:
            plan.append((seq, "file"))
    for path, _ in plan:
        d.require(not os.path.islink(path), "%s is a symbolic link" % path)
        d.require(os.path.realpath(path) == str(path),
                  "%s is not a canonical path" % path)
    scratch_root = Path(scratch_root)
    d.require(scratch_root == Path(storage.SCRATCH_ROOT) and
              scratch_root == Path(os.path.abspath(scratch_root)) and
              not os.path.islink(scratch_root),
              "the scratch root is not the declared %s: %s" % (
                  storage.SCRATCH_ROOT, scratch_root))
    return plan, scratch_root, sorted(snaps), sorted(scratch)


def pending(repo):
    return d.pending_everywhere(repo)


def remove_path(path, how):
    if not os.path.lexists(path):
        return False
    if how == "file":
        os.unlink(path)
    else:
        shutil.rmtree(path)
    return True


def remove_empty(path, stop):
    """Remove `path` and its parents while they are empty, never `stop` or
    anything above it."""
    gone = []
    path = Path(path)
    while path != stop and stop in path.parents:
        try:
            path.rmdir()
        except OSError:
            break
        gone.append(str(path))
        path = path.parent
    return gone


def intent_of(manifest_path, plan, scratch_root):
    return dict(schema=INTENT_SCHEMA, manifest=a.seal(manifest_path),
                paths=[[str(p), how] for p, how in plan],
                scratch_root=str(scratch_root))


def write_intent(path, data):
    """Atomic and durable, as the run journals are."""
    tmp = Path(str(path) + ".tmp")
    with open(tmp, "w") as stream:
        stream.write(d.dumps(data))
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(tmp, path)


def dispose_snapshots(args):
    """`task33_storage.py dispose-snapshots` (design section 5). The
    intent journal is written before anything is removed; a command that
    finds one (an interrupted disposal of the same plan) resumes it: what
    is already gone is skipped and the verification, which the missing
    paths would fail, is not repeated."""
    repo = Path(args.repo).resolve(strict=True)
    evidence = Path(args.evidence).resolve(strict=True)
    out = evidence / "snapshot-disposal.json"
    intent_path = evidence / "snapshot-disposal.intent.json"
    d.require(not out.exists(), "%s exists: the snapshots were disposed" %
              out)
    manifest_path = Path(args.manifest).resolve(strict=True)
    manifest = a.load(manifest_path)
    d.require(manifest.get("schema") == d.snap.SCHEMA and set(
        manifest.get("sides") or ()) == set(LABELS),
        "not a complete snapshot manifest")
    plan, scratch_root, snaps, scratches = removal_plan(
        manifest, repo, args.scratch_root)
    intent = intent_of(manifest_path, plan, scratch_root)
    resumed = intent_path.exists()
    if resumed:
        d.require(a.load(intent_path) == intent, "the disposal intent "
                  "journal %s is of another plan" % intent_path)
    else:
        for path, how in plan:
            d.require(os.path.lexists(path), "%s is absent: the snapshots "
                      "are not whole (nothing was removed)" % path)
    sealed = sealed_evidence(evidence)
    sealed["disposition"] = sealed_disposition(evidence)
    sides = {s: dict(root=Path(manifest["sides"][s]["root"]),
                     pin=manifest["sides"][s]["pin"],
                     tree=manifest["sides"][s]["tree"]) for s in LABELS}
    verify = args.verify_argv or d.default_verify(
        repo, manifest_path, sides, getattr(args, "compiled_ref", None))
    sizes = {str(p): (tree_bytes(p) if how == "tree" else
                      os.lstat(p).st_size) if os.path.lexists(p) else None
             for p, how in plan}
    with a.serial_lock(repo) as fds:
        d.require(not pending(repo), "a restore journal is pending: "
                  "`recover` first (nothing was removed)")
        final = None if resumed else d.run_verify(verify, repo, fds)
        if not resumed:
            write_intent(intent_path, intent)
        removed = [str(p) for p, how in plan if remove_path(p, how)]
        if scratch_root.exists():
            shutil.rmtree(scratch_root)
            removed.append(str(scratch_root))
        agent = repo / ".agent-files"
        gone = []
        for top in scratches + snaps:
            gone += remove_empty(top, agent)
    data = dict(
        schema=DISPOSAL_SCHEMA, manifest=dict(
            path=str(manifest_path), seal=a.seal(manifest_path)),
        sizes_bytes=sizes, verify=final, resumed=resumed,
        harvest=sealed["harvest"], api_audit=sealed["audit"],
        disposition=sealed["disposition"], removed=removed,
        emptied_parents=gone,
        recreate=[
            "python3 src/simp/tests/performance/task32_snapshots.py build "
            "--side base --pin %s ..." % manifest["sides"]["base"]["pin"],
            "python3 src/simp/tests/performance/task32_snapshots.py build "
            "--side cand --pin %s ..." % manifest["sides"]["cand"]["pin"],
            "python3 src/simp/tests/performance/task32_snapshots.py "
            "verify ...", "python3 src/simp/tests/performance/"
            "task32_snapshots.py compare ..."])
    with out.open("x") as stream:
        stream.write(d.dumps(data))
    intent_path.unlink()
    print("removed %d paths; wrote %s" % (len(removed), out))
    return 0
