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

The row is `identical` when both lists of differences are empty,
`attributed` when every difference of the closure is of a file of the
reviewed table (task31_attribution.py: the same blobs on the two sides as the
table names, the elaboration order and the heap equal, the work equal), and
`different` otherwise. Everything is re-derived from the archived folder, so
`cell` is also the replay (task31_grid.py `identity-replay`).
"""
import gzip
import hashlib
import json
import re
from pathlib import Path

import acceptance as a
import audit_evidence as ae
from performance_schema import require
import task31_snapshot as snap

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
    texts = snapshot[side].get("texts", {})
    names = snapshot[side].get("spellings")
    require(isinstance(names, list) and str(private) in names,
            "the snapshot does not record the spellings of the root")

    def product(raw):
        """The record of a product, its digests derived again from its
        text: the raw one must be the runner's, the normalized one is
        computed here (a file above the snapshot's limit has none to
        compute, and its normalized digest is its raw one)."""
        name = relative(raw, private, "private product")
        found = files.get(name)
        require(found is not None and len(found) == 3, "the snapshot lacks "
                "the product " + name)
        if found[0] > snap.LIMIT:
            require(found[1] == found[2], "the snapshot normalizes a file "
                    "above its limit: " + name)
            return name, found
        require(name in texts, "the snapshot lacks the text of the "
                "product " + name)
        data = texts[name].encode("latin-1")
        require(len(data) == found[0] and
                hashlib.sha256(data).hexdigest() == found[1],
                "the text of the product %s is not its recorded file" % name)
        require(hashlib.sha256(snap.normalize(data, names)).hexdigest() ==
                found[2], "the normalized digest of %s is not that of its "
                "text" % name)
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
        one, two = base["order"], cand["order"]
        index = next((i for i, pair in enumerate(zip(one, two))
                      if pair[0] != pair[1]), min(len(one), len(two)))
        found.append(dict(
            kind="order", name="elaboration order", index=index,
            baseline=one[index] if index < len(one) else None,
            candidate=two[index] if index < len(two) else None))
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


def attribute(different, closures, manifest, entries):
    """Split the differences of a cell into the attributed ones and the
    rest. A difference is attributable only if

    - its kind is `source`, or `product` of the same entry;
    - its entry is a private file (`private/NAME`), which both selections
      take from one git path P;
    - P is an entry of the reviewed table, of kind `source`, whose
      baseline blob is the blob the baseline selection took the file from
      and whose candidate blob is the candidate selection's.

    A shared-file difference cannot occur in this harness (both sides read
    the one checkout), and an `only-*`, `physical`, `order` or `heap`
    difference is never attributable. Returns ({P: record}, the rest)."""
    by_path = {e["path"]: e for e in entries}

    def selected(side, name):
        for found in manifest["selections"][side]["sources"]:
            if Path(found["git_path"]).name == name:
                return found
        return None

    attributed, rest = {}, []
    for found in different:
        entry = found["name"].split(" ")[0]
        kind, _, name = entry.partition("/")
        one = two = None
        if found["kind"] in ("source", "product") and kind == "private":
            one, two = selected("baseline", Path(name).name), \
                selected("candidate", Path(name).name)
        reviewed = None
        if one is not None and two is not None and \
                one["git_path"] == two["git_path"]:
            reviewed = by_path.get(one["git_path"])
        if reviewed is None or reviewed["kind"] != "source" or (
                one["git_blob"], two["git_blob"]) != (
                reviewed["baseline_blob"], reviewed["candidate_blob"]):
            rest.append(found)
            continue
        record = attributed.setdefault(reviewed["path"], dict(
            path=reviewed["path"], entry=entry, kinds=[],
            baseline_blob=one["git_blob"], candidate_blob=two["git_blob"],
            baseline_sha256=closures["baseline"]["entries"][entry]
            ["source"], candidate_sha256=closures["candidate"]["entries"]
            [entry]["source"], reason=reviewed["reason"]))
        if found["kind"] not in record["kinds"]:
            record["kinds"] = sorted(record["kinds"] + [found["kind"]])
    return attributed, rest


def cell(folder, case, size, baseline, candidate, samples=3, entries=()):
    """The identity row of one archived cell, re-derived from its folder.
    `entries` is the reviewed table of attributions (task31_attribution)."""
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
    attributed, rest = attribute(different, closures, manifest, entries)
    row = dict(
        case=case, size=size, name="%s-%d" % (case, size),
        status="different" if rest or unequal else
        "attributed" if attributed else "identical",
        closure_differences=different, unattributed_differences=rest,
        work_differences=unequal,
        attributed=sorted(attributed.values(), key=lambda r: r["path"]),
        attribution_table=digest(list(entries)),
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
        head=manifest.get("head"), dirty=[
            d for d in manifest.get("dirty") or [] if ".agent-files" not in
            str(d)], inputs=digest(manifest["inputs"]),
        tools=digest(manifest["tools"]))
    row.update(files_of(closures, manifest))
    return row


def tracked(path):
    """The tracked file a shared source is: a generated theory
    `d/[.hol/objs/]XTheory.sig` or `.sml` is `d/XScript.sml`."""
    path = path.replace("/.hol/objs/", "/")
    found = re.fullmatch(r"(.*/)?([^/]+)Theory\.s(?:ig|ml)", path)
    return path if found is None else \
        "%s%sScript.sml" % (found.group(1) or "", found.group(2))


def private_file(name, physical, selected, repo):
    """The tracked file a private file of one side is built from, or None
    for an installed fixture. It is a selected simplifier source (by its
    name, the sources are flattened), else the shared source the manifest
    says a relocated dependency was copied from. Any other private file is
    refused: it must be a fixture the runner installed (the manifest's
    `fixture_products`), so that no private file goes unmapped."""
    git_paths = {Path(s["git_path"]).name: s["git_path"]
                 for s in selected["sources"]}
    products = (selected.get("shared_dependencies") or {}).get(
        "products") or {}
    origin = {key: Path(info["source"]).relative_to(repo).as_posix()
              for key, info in products.items() if "source" in info and
              Path(info["source"]).is_absolute() and
              Path(info["source"]).is_relative_to(repo)}
    if Path(name).name in git_paths:
        return git_paths[Path(name).name]
    if physical in origin:
        return tracked(origin[physical])
    if name in origin:
        return tracked(origin[name])
    require(name in (selected.get("fixture_products") or {}),
            "a private file is neither a selected source, a relocated "
            "dependency nor an installed fixture: " + name)
    return None


def files_of(closures, manifest):
    """Per side, the tracked files of the process: `repo_files` (the
    ones it elaborated), `loaded_files` (all it loaded or found loaded,
    elaborated or not) and `heap_files` (the initial heap's)."""
    repo = Path(manifest["repo"])
    used, loaded, heap = {}, {}, {}
    for side in SIDES:
        selected = manifest["selections"][side]
        one, two = set(), set()
        for name, entry in closures[side]["entries"].items():
            kind, _, rest = name.partition("/")
            if kind == "shared":
                found = tracked(rest)
            else:
                found = private_file(rest, entry["physical"], selected,
                                     repo)
            if found is not None:
                two.add(found)
                if entry["used"]:
                    one.add(found)
        three = set()
        for spelled in closures[side]["heap"]:
            kind, _, rest = spelled.partition("/")
            found = tracked(rest) if kind == REPO else \
                private_file(rest, rest, selected, repo)
            if found is not None:
                three.add(found)
        used[side], loaded[side], heap[side] = (
            sorted(one), sorted(two), sorted(three))
    return dict(repo_files=used, loaded_files=loaded, heap_files=heap)


def repo_files(base, cand, manifest, folder=None):
    """The tracked repository files the two processes elaborated (`use`;
    the heap's are not): shared sources as they are (a generated theory as
    its script), private ones through the physical source they were copied
    from where the manifest names it (a shared dependency), else by their
    name below src/simp/src (the selected simplifier sources)."""
    return files_of(dict(baseline=base, candidate=cand), manifest)[
        "repo_files"]
