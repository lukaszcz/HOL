"""Frozen baseline public clients and their explicit initial expectations."""
import json
import re

# Each full ascription checks EVERY original export, including inherited
# Abbrev aliases. Smoke checks are deliberately smaller than semantic suites.
CONTRACTS = {
    "PublicThmAttribute": {
        "reference": "ThmAttribute",
        "checks": ["complete ThmAttribute ascription",
                   "original attribute records and registry",
                   "original attribute callbacks and formatting"],
        "modules": ["ThmAttribute"], "fresh": ["ThmAttribute"]},
    "PublicCond_rewr": {
        "reference": "Cond_rewr",
        "checks": ["complete Cond_rewr ascription",
                   "original conditional rewrite types and execution"],
        "modules": ["Cond_rewr"]},
    "PublicOpening": {
        "reference": "Opening",
        "checks": ["complete Opening ascription",
                   "original congruence procedure record and execution"],
        "modules": ["Opening"]},
    "PublicTravrules": {
        "reference": "Travrules",
        "checks": ["complete Travrules ascription",
                   "original traversal datatypes and type identities"],
        "modules": ["Travrules"]},
    "PublicSimpLib": {
        "reference": "simpLib",
        "checks": ["complete simpLib ascription",
                   "original simplifier records and ordinary execution"],
        "modules": ["Traverse", "simpLib"]},
    "PublicCongLib": {
        "reference": "congLib",
        "checks": ["complete congLib ascription",
                   "original congruence datatype and simpset identity"],
        "modules": ["Traverse", "simpLib", "congLib"]},
    "PublicTraverseAscription": {
        "reference": "Traverse",
        "checks": ["complete Traverse ascription"], "modules": ["Traverse"],
        "exact_datatype": True},
    "PublicTraverseFunctor": {
        "reference": "Traverse",
        "checks": ["complete Traverse functor argument"],
        "modules": ["Traverse"], "exact_datatype": True},
    "PublicTraverseClient": {
        "checks": ["replication and every reducer field",
                   "every traverse_data field",
                   "ordinary reducer/simpset/congset interoperability"],
        "modules": ["Traverse", "simpLib", "congLib"],
        "exhaustive_match": True},
}


def legacy_name(name):
    return "Legacy" + name[0].upper() + name[1:]


def references(here, repo, git, require, fingerprint):
    """Verify exact original bytes against both maintained hashes and Git."""
    refs = json.loads((here / "public/references.json").read_text())
    clients = json.loads((here / "public/clients.json").read_text())["clients"]
    require(set(clients) == {target + ".sml" for target in CONTRACTS},
            "incomplete frozen client inventory")
    for filename, spec in clients.items():
        require(fingerprint(here / "public" / filename) == spec,
                "frozen baseline client changed: " + filename)
    for name, spec in refs.items():
        path = here / "inputs/develop" / (name + ".sig")
        require(fingerprint(path) == {k: spec[k] for k in ("sha256", "bytes")},
                "frozen reference hash changed: " + name)
        original = git(repo, "show", spec["revision"] + ":" + spec["path"])
        require(path.read_bytes() == original,
                "frozen reference differs from baseline: " + name)
    return refs


def inventory(repo, baseline, ref, refs, git, require):
    """Fail on an un-inventoried change to ANY baseline-existing signature."""
    originals = set(git(repo, "ls-tree", "-r", "--name-only", baseline)
                    .decode().splitlines())
    changed = git(repo, "diff", "--name-only", baseline, ref, "--", "*.sig")
    changed = set(changed.decode().splitlines())
    covered = {spec["path"] for spec in refs.values()}
    require(not ((changed & originals) - covered),
            "changed baseline signature without a client: " +
            ", ".join(sorted((changed & originals) - covered)))
    return {"changed_baseline": sorted(changed & originals),
            "branch_only": sorted(changed - originals),
            "unchanged_dependencies": sorted(covered - changed)}


def install(here, dst, refs):
    for name in refs:
        original = (here / "inputs/develop" / (name + ".sig")).read_text()
        # The sole transformation gives the original signature a private name.
        # In particular no constructor, export or dependency is rewritten.
        renamed, n = re.subn(r"\bsignature " + re.escape(name) + r"\s*=",
                             "signature " + legacy_name(name) + " =", original)
        if n != 1:
            raise ValueError("unexpected original signature header: " + name)
        (dst / (legacy_name(name) + ".sig")).write_text(renamed)
        (dst / (legacy_name(name) + ".sml")).write_text(
            "(* Signature-only module for Meta.loadPlan. *)\n")
    for path in sorted((here / "public").glob("*.sml")):
        (dst / path.name).write_bytes(path.read_bytes())
    with (dst / "Holmakefile").open("a") as out:
        for name in refs:
            targets = (["PublicTraverseAscription", "PublicTraverseFunctor"]
                       if name == "Traverse" else
                       ["Public" + name[0].upper() + name[1:]])
            for target in targets:
                # The dependency scanner does not see all names appearing only
                # in structure aliases/ascriptions. Make real elaboration of
                # BOTH the frozen signature and selected module mandatory.
                out.write("\n" + target + ".uo: " + legacy_name(name) +
                          ".uo " + name + ".uo\n")
        out.write("\npaired.exe: " + " ".join(
            target + ".uo" for target in CONTRACTS) + "\n")
        out.write("attribute.exe: runner.uo\n\t$(HOLMOSMLC) -o $@ $<\n")


def expectation(target, mode):
    spec = dict(CONTRACTS[target], target=target)
    spec["red"] = mode == "reject" and spec.get("exact_datatype", False)
    spec["warning"] = mode == "reject" and spec.get("exhaustive_match", False)
    spec["observations"] = [["check", name, "pass"] for name in spec["checks"]]
    spec["signatures"] = ([legacy_name(spec["reference"])]
                          if "reference" in spec else [])
    return spec
