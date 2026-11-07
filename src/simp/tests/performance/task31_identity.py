"""TASK31 gate 1: what one cell's two processes loaded, and what they did.

Data in, decision out; no process is started here. `cell` reads the folder of
one runner experiment (one pair: a fresh process for the baseline and one for
the candidate, `--matrix-performance` with `task31_snapshot.py`, which adds
the record of the private trees) and returns the cell's identity row:

- the closure: every source the process elaborated (`use`) or found loaded,
  with its sha256, and the products of each private source (`.uo`, `.ui`)
  as the sha256 of their bytes with the private directory of the side
  replaced by a placeholder, because a product names its directory and two
  sides differ in that alone. A source or product that one side holds and
  the other does not, differs in its bytes, or an elaboration order that
  differs, is listed;
- the work: the ordered checks of the fixture (each proof is compared in the
  process with the independently built expected theorem, and residual goals
  and hypotheses are checked, so a wrong result stops the process), the keys
  and number of the timed observations, the result consumption of an
  iteration and the number of samples. Counts that depend on the host (the
  calibration batches and their times) are not part of it.

The row is `identical` only when both lists of differences are empty.
Everything is re-derived from the archived folder, so `cell` is also the
replay (task31_grid.py `identity-replay`).
"""
import gzip
import hashlib
import json
import re
from pathlib import Path

import acceptance as a
import audit_evidence as ae
from performance_schema import require

SIDES = ("baseline", "candidate")
SNAPSHOT = "private-snapshot.json"
PRIVATE, REPO = "<private>", "<repo>"


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def load_receipt(folder, name):
    return json.loads(gzip.decompress((Path(folder) / name).read_bytes()))


def relative(path, root, what):
    path = Path(path)
    require(path.is_relative_to(root), "%s is outside %s: %s"
            % (what, root, path))
    return path.relative_to(root).as_posix()


def checked(folder, manifest, case, size, baseline, candidate, samples):
    """The runner's own experiment is valid and is the cell's: success, one
    pair, the options, the pins and every process accepted; the two
    performance receipts, in order, pass the offline audits of
    audit_evidence and acceptance."""
    require(manifest.get("success") is True, "failed experiment")
    options = manifest["performance"]
    require(options["suite"] == "matrix" and options["case"] == case and
            options["size"] == size and options["pairs"] == 1 and
            options["samples"] == samples, "wrong matrix/identity options")
    for side, pin in (("baseline", baseline), ("candidate", candidate)):
        require(manifest["selections"][side]["revision"] == pin,
                "wrong selected revision")
    require(manifest.get("inputs") and manifest.get("tools"),
            "missing input/tool hashes")
    require(all(run["accepted"] is True and run["exit"] == 0
                for run in manifest["runs"]), "a process was not accepted")
    receipts = {}
    for run in manifest["runs"]:
        receipt = load_receipt(folder, run["receipt"])
        require(receipt["accepted"] is True and receipt["exit"] == 0,
                "failed process")
        if receipt["fixture"] != "performance":
            continue
        ae.audit(manifest, receipt)
        a.archive_protocol(manifest, receipt)
        require(receipt["selection"] not in receipts and
                receipt["pair"] == 0, "repeated or extra performance process")
        receipts[receipt["selection"]] = receipt
    require(sorted(receipts) == sorted(SIDES) and [
        run["receipt"] for run in manifest["runs"]
        if run["receipt"].startswith("pair-")] ==
        ["pair-00-baseline.json.gz", "pair-00-candidate.json.gz"],
        "the experiment lacks a process of a side, or runs them out of order")
    return receipts


def closure(manifest, receipt, snapshot, side):
    """The closure of one side as a dict of normalized entries. A private
    source is keyed by its name below the private directory, a shared one by
    its path below the repository. The products of a private source take the
    normalized digests of the snapshot, which must agree with the raw hashes
    the runner holds."""
    selected = manifest["selections"][side]
    private = Path(selected["private"])
    repo = Path(manifest["repo"])
    require(side in snapshot and snapshot[side]["root"] == str(private),
            "the snapshot is not of the %s private tree" % side)
    files = snapshot[side]["files"]

    def product(raw):
        name = relative(raw, private, "private product")
        found = files.get(name)
        require(found is not None and len(found) == 3, "the snapshot lacks "
                "the product " + name)
        return name, found

    events = receipt["result"]["events"]
    used = {event[1] for event in events if event[0] == "use"}
    entries = {}
    for logical, info in receipt["result"]["paths"].items():
        physical = Path(info["physical"])
        if physical.is_relative_to(private):
            name = relative(logical, private, "private source")
            made = {}
            for raw, fingerprint in info["related_products"].items():
                key, found = product(raw)
                require(found[1] == fingerprint["sha256"] and
                        found[0] == fingerprint["bytes"],
                        "the snapshot disagrees with the runner about "
                        + key)
                made[key] = found[2]
            source = files.get(relative(physical, private, "source"))
            require(source is not None and
                    source[1] == info["sha256"],
                    "the snapshot disagrees with the runner about " + name)
            entries["private/" + name] = dict(
                source=info["sha256"], bytes=info["bytes"],
                physical=relative(physical, private, "source"),
                products=dict(sorted(made.items())),
                used=logical in used)
        else:
            name = relative(logical, repo, "shared source")
            entries["shared/" + name] = dict(
                source=info["sha256"], bytes=info["bytes"],
                physical=relative(physical, repo, "shared source"),
                products={relative(p, repo, "shared product"): f["sha256"]
                          for p, f in sorted(info["related_products"]
                                             .items())},
                used=logical in used)
    def spelled(raw, what):
        path = Path(raw)
        return (PRIVATE + "/" + relative(path, private, what)
                if path.is_relative_to(private) else
                REPO + "/" + relative(path, repo, what))

    return dict(entries=entries,
                order=[spelled(e[1], "use") for e in events
                       if e[0] == "use"],
                heap=sorted(spelled(e[1], "heapfile") for e in events
                            if e[0] == "heapfile"))


def compare(base, cand):
    """The differences between the closures of the two sides, sorted: a
    list of {kind, name, baseline, candidate}."""
    found = []
    for name in sorted(set(base["entries"]) | set(cand["entries"])):
        one, two = base["entries"].get(name), cand["entries"].get(name)
        if one is None or two is None:
            found.append(dict(kind="only-" + ("candidate" if one is None
                                              else "baseline"), name=name))
            continue
        for field in ("source", "physical"):
            if one.get(field) != two.get(field):
                found.append(dict(kind=field, name=name,
                                  baseline=one.get(field),
                                  candidate=two.get(field)))
        for product in sorted(set(one["products"]) | set(two["products"])):
            if one["products"].get(product) != two["products"].get(product):
                found.append(dict(
                    kind="product", name=name + " " + product,
                    baseline=one["products"].get(product),
                    candidate=two["products"].get(product)))
    if base["order"] != cand["order"]:
        found.append(dict(kind="order", name="elaboration order"))
    if base["heap"] != cand["heap"]:
        found.append(dict(kind="heap", name="initial heap sources",
                          baseline=len(base["heap"]),
                          candidate=len(cand["heap"])))
    return found


def work(receipt):
    """The work row of one process."""
    result, measured = receipt["result"], receipt["measurements"]
    keys = []
    for event in result["observations"]:
        # The calibration batches repeat their key as often as the host's
        # speed asks; the key is the stage.
        if event[0] == "observation" and (not keys or keys[-1] != event[1]):
            keys.append(event[1])
    labels = {}
    for label, found in sorted(measured["workloads"].items()):
        batches = found["batches"]
        require(batches and all(
            b["consumed"] == batches[0]["consumed"] *
            b["iterations"] // batches[0]["iterations"] for b in batches),
            "inconsistent result consumption")
        labels[label] = dict(
            samples=len(batches), schedule=found.get("schedule", "ramp"),
            consumed_per_iteration=batches[0]["consumed"] /
            batches[0]["iterations"])
    return dict(
        checks=[e[1:] for e in result["observations"] if e[0] == "check"],
        keys=keys, expected_test_count=result["expected_test_count"],
        outcome=result["outcome"], workloads=labels,
        storage=measured["storage"],
        storage_graph=receipt["storage_graph"])


def work_differences(base, cand):
    return [dict(kind="work", name=key, baseline=base.get(key),
                 candidate=cand.get(key))
            for key in sorted(set(base) | set(cand))
            if base.get(key) != cand.get(key)]


def cell(folder, case, size, baseline, candidate, samples=3):
    """The identity row of one archived cell, re-derived from its folder."""
    folder = Path(folder)
    manifest = json.loads((folder / "manifest.json").read_text())
    receipts = checked(folder, manifest, case, size, baseline, candidate,
                       samples)
    snapshot = json.loads((folder / SNAPSHOT).read_text())
    closures = {side: closure(manifest, receipts[side], snapshot, side)
                for side in SIDES}
    works = {side: work(receipts[side]) for side in SIDES}
    different = compare(closures["baseline"], closures["candidate"])
    unequal = work_differences(works["baseline"], works["candidate"])
    row = dict(
        case=case, size=size, name="%s-%d" % (case, size),
        status="identical" if not different and not unequal
        else "different",
        closure_differences=different, work_differences=unequal,
        closure={side: dict(
            digest=digest([closures[side]["entries"],
                           closures[side]["order"],
                           closures[side]["heap"]]),
            private=sum(k.startswith("private/")
                        for k in closures[side]["entries"]),
            shared=sum(k.startswith("shared/")
                       for k in closures[side]["entries"]),
            heap=len(closures[side]["heap"])) for side in SIDES},
        work={side: works[side] for side in SIDES},
        repo_files=repo_files(closures["baseline"], closures["candidate"],
                              manifest, folder))
    return row


def tracked(path):
    """The tracked file a shared source is: a generated theory
    `d/[.hol/objs/]XTheory.sig` or `.sml` is `d/XScript.sml`."""
    path = path.replace("/.hol/objs/", "/")
    found = re.fullmatch(r"(.*/)?([^/]+)Theory\.s(?:ig|ml)", path)
    return path if found is None else \
        "%s%sScript.sml" % (found.group(1) or "", found.group(2))


def repo_files(base, cand, manifest, folder):
    """The tracked repository files the two processes elaborated (`use`;
    the heap's are not): shared sources as they are (a generated theory as
    its script), private ones through the physical source they were copied
    from where the manifest names it (a shared dependency), else by their
    name below src/simp/src (the selected simplifier sources)."""
    repo = Path(manifest["repo"])
    out = {}
    for side, found in (("baseline", base), ("candidate", cand)):
        selected = manifest["selections"][side]
        git_paths = {Path(s["git_path"]).name: s["git_path"]
                     for s in selected["sources"]}
        origin = {name: Path(info["source"]).relative_to(repo).as_posix()
                  for name, info in selected["shared_dependencies"][
                      "products"].items() if "source" in info and
                  Path(info["source"]).is_absolute() and
                  Path(info["source"]).is_relative_to(repo)}
        files = set()
        for name, entry in found["entries"].items():
            if not entry["used"]:
                continue
            kind, _, rest = name.partition("/")
            if kind == "shared":
                files.add(tracked(rest))
            elif Path(rest).name in git_paths:
                files.add(git_paths[Path(rest).name])
            elif entry["physical"] in origin:
                files.add(tracked(origin[entry["physical"]]))
            elif rest in origin:
                files.add(tracked(origin[rest]))
        out[side] = sorted(files)
    return out
