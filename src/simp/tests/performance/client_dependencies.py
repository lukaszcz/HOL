"""Recompile the shared client closure that can load a private simplifier.

This is mixed-source isolation, NOT an independent build: defining sources and
unaffected dependencies come from the same configured baseline for both sides.
No production source or shared build product is modified. Call install after
install_fixtures and before Holmake; add its inputs to the run's input seal and
its products to fixture provenance, never to the selected-source inventory.
"""
import hashlib
from pathlib import Path
import re


class DependencyError(ValueError):
    pass


def _fingerprint(data):
    return {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def _physical(path):
    """Resolve exported symlinks and HOL's generated-source HFS mapping."""
    if not path.exists():
        path = path.parent / ".hol/objs" / path.name
    return path.resolve(strict=True)


def install(repo, dst, private_names):
    """Return {inputs: {absolute_path: fingerprint}, products: {name: info},
    modules: [...], roots: [...]} after installing affected shared sources.

    Product keys are relative private paths (including .hol/objs for theories).
    Info has role='shared-dependency', source=<physical shared path>, and the
    installed bytes' sha256/bytes. Existing private source files are never
    replaced. Private Holmakefile gets explicit frozen-theory loader rules.
    Both .uo and .ui edges matter: shared signatures can also bypass local
    search paths. Roots conservatively include every exported module identifier
    mentioned by installed sources, plus the selected modules' shared metadata.
    Reverse reachability is restricted to the recursive forward root closure.
    The theory of a selected private script is private too: for every
    private name XScript, XTheory is a private name. It is never copied from
    the shared tree (lexical roots and shared_simp must not freeze the shared
    toolchain's XTheory.{sml,sig,dat,uo,ui}); the private directory's own
    Holmake builds it from the private script when anything needs it.
    Generated support sources under src/simp are also relocation seeds: the
    runner forbids *any* shared source from that directory, including theories
    absent from the selected git sources. Their data remains shared-baseline.
    """
    repo, dst = Path(repo).resolve(strict=True), Path(dst).resolve(strict=True)
    private_names = set(private_names)
    private_names |= {name[:-len("Script")] + "Theory"
                      for name in private_names
                      if name.endswith("Script") and name != "Script"}
    inputs = {}

    def read(path):
        physical = _physical(path)
        if not physical.is_relative_to(repo):
            raise DependencyError("dependency outside shared repository: " +
                                  str(physical))
        data = physical.read_bytes()
        stamp = _fingerprint(data)
        # Seal the exported link path too: retargeting sigobj after this graph
        # scan must not evade the seal on its original physical destination.
        aliases = {physical}
        if path.exists():
            aliases.add(path)
        for alias in aliases:
            old = inputs.setdefault(str(alias), stamp)
            if old != stamp:
                raise DependencyError("dependency changed while reading: " +
                                      str(alias))
        return physical, data

    # Seal unaffected metadata too: it determines negative graph decisions.
    graph, sources, metadata = {}, {}, {}
    for product in sorted((repo / "sigobj").iterdir()):
        if product.suffix not in (".uo", ".ui"):
            continue
        name = product.stem
        graph.setdefault(name, set())
        sources.setdefault(name, {})
        physical_product, data = read(product)
        lines = data.decode("utf-8").splitlines()
        metadata.setdefault(name, {})[product.suffix] = (
            physical_product, lines)
        suffix = ".sml" if product.suffix == ".uo" else ".sig"
        defining = []
        for line in lines:
            if not line:
                continue
            expanded = line.replace("$(HOLDIR)", str(repo))
            if "$" in expanded:
                raise DependencyError("unknown dependency variable: " + line)
            path = Path(expanded)
            if not path.is_absolute():
                path = product.parent / path
            if not path.is_relative_to(repo):
                raise DependencyError(
                    "dependency outside shared repository: " + line)
            if path.suffix in (".sml", ".sig"):
                defining.append(path)
            else:
                # Module names may contain dots (e.g. HOLsexp.grm).
                graph[name].add(path.name)
        if not lines and product.suffix == ".ui":
            continue  # Holmake emits an empty .ui for signatureless modules.
        if len(defining) != 1 or defining[0].suffix != suffix:
            raise DependencyError("missing/ambiguous defining source: " +
                                  str(product))
        sources[name][suffix] = defining[0]

    # Overapproximate lexical references rather than maintain a fragile list of
    # downstream roots. This includes open declarations and qualified names.
    tokens = set()
    for source in sorted(dst.iterdir()):
        if source.suffix in (".sml", ".sig"):
            tokens.update(re.findall(r"[A-Za-z][A-Za-z0-9_']*",
                                     source.read_text()))
    roots = (tokens | private_names) & graph.keys()
    closure, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in closure:
            continue
        if name not in graph:
            raise DependencyError(
                "unexported dependency in root closure: " + name)
        closure.add(name)
        pending.extend(graph[name] - closure)

    reverse = {name: set() for name in closure}
    for name in closure:
        for dep in graph[name]:
            reverse[dep].add(name)
    shared_simp = {name for name, defining in sources.items()
                   if any(p.is_relative_to(repo / "src/simp")
                          for p in defining.values())}
    affected, pending = set(), list((private_names | shared_simp) & closure)
    while pending:
        name = pending.pop()
        if name in affected:
            continue
        affected.add(name)
        pending.extend(reverse[name] - affected)
    modules = sorted(affected - private_names)

    # Prepare every copy before writing anything. A collision or missing theory
    # data must fail closed, not leave a partially installed private closure.
    copies = {}
    for name in modules:
        if ".sml" not in sources[name]:
            raise DependencyError("missing shared implementation: " + name)
        for suffix, source in sorted(sources[name].items()):
            physical, data = read(source)
            copies[name + suffix] = (physical, data)
            if suffix == ".sml":
                dat = source.with_suffix(".dat")
                # Generated theories use #(FILE), so relocation requires the
                # corresponding .dat beside the copied logical .sml source.
                needs_data = b"TheoryReader.load_thydata" in data
                try:
                    physical_dat = _physical(dat)
                except FileNotFoundError:
                    if needs_data:
                        raise DependencyError(
                            "missing theory data: " + str(dat))
                else:
                    copies[name + ".dat"] = read(physical_dat)
    # Poly/ML .uo/.ui files are textual source-loader descriptors, NOT compiled
    # code. Holdep recognises a theory only via Script.sml or an existing .ui;
    # its automatic rules also insist on rebuilding from Script.sml. Rebind
    # theory descriptors and freeze the copied theory products with explicit
    # private rules instead. Runtime still elaborates/compiles every copied
    # .sig/.sml against private dependencies, verified by Paired's trace.
    local_names = private_names | set(modules)
    theories = [name for name in modules if name.endswith("Theory")]
    for name in theories:
        for suffix in (".uo", ".ui"):
            product, lines = metadata[name][suffix]
            rebound = []
            for line in lines:
                path = Path(line.replace("$(HOLDIR)", str(repo)))
                if path.suffix in (".sig", ".sml"):
                    line = str(dst / path.name)
                elif path.name in local_names:
                    line = str(dst / path.name)
                rebound.append(line)
            data = ("\n".join(rebound) + "\n").encode()
            copies[name + suffix] = (product, data)

    def destination(name):
        path = Path(name)
        # HOLFileSys always munges theory sources/data, even when a plain file
        # exists. Installing them at dst/name silently falls back to sigobj!
        if path.stem.endswith("Theory") and len(path.stem) > len("Theory"):
            return Path(".hol/objs") / name
        return path

    for name in copies:
        target = dst / destination(name)
        if target.exists() or target.is_symlink() or (dst / name).exists():
            raise DependencyError("private source collision: " + name)
    products = {}
    for name, (source, data) in sorted(copies.items()):
        relative = destination(name)
        target = dst / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        products[str(relative)] = {
            "role": "shared-dependency", "source": str(source),
            **_fingerprint(data)}
    if modules:
        holmakefile = dst / "Holmakefile"
        rules = "\n# Shared-baseline dependencies; private source loaders.\n"
        # Frozen theory descriptors may refer to helpers invisible to lexical
        # Holdep. Compile all relocated implementations before the launcher.
        rules += "paired.exe: " + " ".join(n + ".uo" for n in modules) + "\n"
        for name in theories:
            targets = " ".join(name + suffix for suffix in
                               (".uo", ".ui", ".sml", ".sig", ".dat"))
            rules += targets + ":\n\t@:\n"
        # Preserve explicit dependencies from custom shared build recipes too.
        # NumRelNorms needs the toplevel GenRelNorm functor; lexical Holdep
        # alone cannot recover its RelNorm_Input signature dependency.
        for name in modules:
            if name in theories:
                continue
            for suffix, (_, lines) in sorted(metadata[name].items()):
                deps = set()
                for line in lines:
                    path = Path(line.replace("$(HOLDIR)", str(repo)))
                    if path.suffix in (".sml", ".sig") or path.name == name:
                        continue
                    dep = path.name
                    if dep in local_names:
                        deps.add(dep + ".uo")
                    else:
                        deps.add("$(dprot " + str(repo / "sigobj" / dep) +
                                 ".uo)")
                if deps:
                    rules += (name + suffix + ": " +
                              " ".join(sorted(deps)) + "\n")
        with holmakefile.open("a") as out:
            out.write(rules)
        products["Holmakefile"] = {
            "role": "shared-dependency",
            "source": "generated dependency rules",
            **_fingerprint(holmakefile.read_bytes())}
    return {"inputs": inputs, "products": products, "modules": modules,
            "roots": sorted(roots)}
