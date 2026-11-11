#!/usr/bin/env python3
"""TASK32 independent snapshots: build, verify (v2 manifest) and compare.

  build    one snapshot (`--side base|cand`): `git clone --shared
           --no-checkout` of the repository into ROOT/<label>, detached at the
           pin, the sealed `mktool` fix on the baseline when asked, then
           smart-configure and `bin/build --no-cache -t -jN
           --seq=tools/sequences/upto-parallel`, under an `env -i`
           environment and a fresh HOME that are the same for both sides. The
           record of the side goes into the manifest (SCHEMA).
  verify   fail-closed audit of the manifest against the live trees: pins,
           tree and input hashes, the sealed patch, no stale products, every
           product seal and mtime inside the build interval, no shared
           inodes, identical argv/env, the toolchain, no nested roots.
  compare  the untimed behaviour comparison: every common `*Theory.sig` and
           `*Theory.dat` and the normalized selftest logs of the two trees.
           Any unexplained difference makes the result `blocked`.

The labels `base` and `cand` have the same length so that the HOLDIR strings
embedded in heaps and loaders do too. Nothing here edits the trees after the
build; verify and compare only read them.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import acceptance as a
from performance_schema import require
import startup_gate as sg

SCHEMA = "task32-independent-build-v2"
BEHAVIOR_SCHEMA = "task32-behavior-v1"
LABELS = ("base", "cand")
PATH = "/usr/local/bin:/usr/bin:/bin"
POLY = "/usr/local/bin/poly"
SEQUENCE = "tools/sequences/upto-parallel"
CONFIGURE_INPUT = "tools/smart-configure.sml"
MKTOOL_PATH = sg.MKTOOL[0]
SYSTEML = "tools/Holmake/Systeml.sml"
BIN_PRODUCTS = ("bin/hol", "bin/hol.state0", "bin/hol.state",
                "bin/hol.state.min", "bin/Holmake")
PRODUCT_SUFFIXES = (".uo", ".ui", ".dat")
STALE_NAMES = re.compile(r"(.*\.(uo|ui|dat)|hol\.state.*|\.hol)\Z")
AREAS = ("num", "integer", "real", "boss", "list", "pred_set")
PLACEHOLDER = "$(HOLDIR)"
ENV_KEYS = ("HOME", "LC_ALL", "PATH", "TERM", "TMPDIR", "TZ")
TIMEOUT = 6 * 3600


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def environment(home, tmpdir="/dev/shm/t32/tmp"):
    """The `env -i` environment: the same for both sides but for HOME."""
    return {"PATH": PATH, "HOME": str(home), "LC_ALL": "C", "TZ": "UTC",
            "TERM": "dumb", "TMPDIR": str(tmpdir)}


def git_bytes(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True,
                          stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE).stdout


def input_hash(root):
    """sha256 of `git ls-files -s` and the working-tree patch."""
    return sha256_bytes(git_bytes(root, "ls-files", "-s") +
                        git_bytes(root, "diff"))


def patch_seal(root):
    data = git_bytes(root, "diff")
    return {"sha256": sha256_bytes(data), "bytes": len(data)}


def nested(first, second):
    first, second = Path(os.path.realpath(first)), \
        Path(os.path.realpath(second))
    return first == second or first.is_relative_to(second) or \
        second.is_relative_to(first)


# -- toolchain ---------------------------------------------------------

def _first_line(argv, env):
    try:
        p = subprocess.run(argv, env=env, stdin=subprocess.DEVNULL,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           text=True, timeout=60)
    except OSError as error:
        return "unavailable: %s" % error.strerror
    return p.stdout.strip().splitlines()[0] if p.stdout.strip() else ""


def _libpolyml(poly):
    p = subprocess.run(["ldd", poly], stdout=subprocess.PIPE,
                       stderr=subprocess.DEVNULL, text=True)
    for line in p.stdout.splitlines():
        if "libpolyml" in line and "=>" in line:
            return os.path.realpath(line.split("=>")[1].split()[0])
    return None


def _libpolymain(polyc):
    text = Path(polyc).read_text(errors="replace")
    found = re.search(r'^\s*LIBDIR="?([^"\s]+)', text, re.M)
    candidates = ([Path(found.group(1)) / "libpolymain.a"] if found else [])
    candidates.append(Path(polyc).resolve().parent.parent / "lib" /
                      "libpolymain.a")
    for path in candidates:
        if path.is_file():
            return str(path.resolve())
    return None


def probe_toolchain(poly=POLY, env=None):
    """The toolchain record: versions and file hashes."""
    env = env if env is not None else environment("/nonexistent")
    poly = os.path.realpath(poly)
    polyc = os.path.realpath(str(Path(poly).with_name("polyc")))
    version = subprocess.run([poly, "-v"], env=env, stdin=subprocess.DEVNULL,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, timeout=60).stdout.strip()
    files = {"poly": poly, "polyc": polyc, "libpolyml": _libpolyml(poly),
             "libpolymain.a": _libpolymain(polyc)}
    record = {"poly_v": version, "files": {}}
    for name, path in files.items():
        record["files"][name] = None if path is None else \
            {"path": path, "sha256": sha256_file(path)}
    for tool in ("cc", "ld", "git", "python3"):
        record[tool] = _first_line([tool, "--version"], env)
    return record


def probe_host():
    memory = None
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemTotal:"):
                memory = line.split(":")[1].strip()
    except OSError:
        pass
    return {"uname": list(platform.uname()), "nproc": os.cpu_count(),
            "memory": memory}


def same_toolchain(recorded, live):
    require(a.poly_version_matches(recorded["poly_v"], live["poly_v"]),
            "toolchain: poly -v changed")
    for key in sorted(set(recorded) | set(live)):
        if key != "poly_v":
            require(recorded.get(key) == live.get(key),
                    "toolchain changed: " + key)


# -- running -----------------------------------------------------------

def run_command(argv, cwd, env, stdin, log, fds=()):
    """Run one command with exactly `env`, `stdin` (a path or None for
    /dev/null) and its output in the new file `log`; returns its exit."""
    import signal
    with Path(log).open("x") as out:
        source = open(stdin, "rb") if stdin else subprocess.DEVNULL
        try:
            p = subprocess.Popen(argv, cwd=str(cwd), env=env, stdin=source,
                                 stdout=out, stderr=subprocess.STDOUT,
                                 pass_fds=tuple(fds), start_new_session=True)
            try:
                return p.wait(timeout=TIMEOUT)
            except BaseException:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                raise
        finally:
            if stdin:
                source.close()


def execute(runner, name, argv, cwd, env, stdin, logs, side):
    """One recorded command: the record holds everything the audit needs."""
    log = Path(logs) / ("%s-%s.log" % (side, name))
    start = time.time_ns()
    code = runner(argv, cwd, env, stdin, log)
    end = time.time_ns()
    return {"name": name, "argv": list(argv), "cwd": str(cwd),
            "env": dict(env),
            "stdin_hash": sha256_file(stdin) if stdin else
            sha256_bytes(b""),
            "start_ns": start, "end_ns": end, "exit": code,
            "log": str(log), "log_hash": a.seal(log)}


# -- products ----------------------------------------------------------

def is_product(rel, name):
    return name.endswith(PRODUCT_SUFFIXES) or \
        re.fullmatch(r".*Theory\.sig", name) is not None or \
        ("selftest" in name and name.endswith(".log"))


def scan_products(root):
    """{relative path: seal} of the bin products, every sigobj and object
    file, theory signature and selftest log. A symlink is followed to its
    target, which must lie inside the root."""
    root = Path(root).resolve(strict=True)
    tracked = tracked_paths(root)
    found = {}
    cache = {}

    def seal_of(path):
        target = a.contained(root, str(path))
        if target not in cache:
            st = target.stat()
            cache[target] = {"sha256": sha256_file(target),
                             "bytes": st.st_size, "mtime_ns": st.st_mtime_ns,
                             "dev": st.st_dev, "ino": st.st_ino,
                             "resolved": target.relative_to(root).as_posix()}
        return dict(cache[target])

    for rel in BIN_PRODUCTS:
        require((root / rel).is_file(), "missing product " + rel)
        found[rel] = seal_of(root / rel)
    for folder, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d != ".git"]
        for name in names:
            path = Path(folder) / name
            rel = path.relative_to(root).as_posix()
            if rel not in found and rel not in tracked and \
                    is_product(rel, name):
                found[rel] = seal_of(path)
    return dict(sorted(found.items()))


def stale_products(root, tracked):
    """Untracked paths that look like products of an earlier build."""
    root, found = Path(root), []
    for folder, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d != ".git"]
        for name in list(dirs) + names:
            rel = (Path(folder) / name).relative_to(root).as_posix()
            if STALE_NAMES.match(name) and rel not in tracked:
                found.append(rel)
    return sorted(found)


def tracked_paths(root):
    out = git_bytes(root, "ls-files", "-z").decode()
    return {p for p in out.split("\0") if p}


def status_lines(root, *extra):
    out = git_bytes(root, "status", "--porcelain=v1",
                    "--untracked-files=all", *extra).decode()
    return [line for line in out.splitlines() if line]


# -- build -------------------------------------------------------------

def real_runner(fds):
    return lambda argv, cwd, env, stdin, log: \
        run_command(argv, cwd, env, stdin, log, fds)


def load_manifest(path):
    path = Path(path)
    if path.exists():
        return json.loads(path.read_text())
    return {"schema": SCHEMA, "sides": {}}


def store_manifest(path, manifest):
    path = Path(path)
    with tempfile.NamedTemporaryFile("w", dir=path.parent, delete=False,
                                     prefix=path.name + ".") as stream:
        json.dump(manifest, stream, indent=2, sort_keys=True,
                  allow_nan=False)
        stream.write("\n")
    os.replace(stream.name, path)


def build_side(repo, side, pin, root, manifest_path, logs, scratch, *,
               mktool=False, cand_pin=None, jobs=8, poly=POLY,
               tmpdir="/dev/shm/t32/tmp", runner, probe=probe_toolchain,
               host=probe_host):
    """Build one snapshot and record it. `runner(argv, cwd, env, stdin,
    log)` runs a command and returns its exit (a fake in the tests)."""
    require(side in LABELS, "side must be one of %s" % (LABELS,))
    require(len(LABELS[0]) == len(LABELS[1]), "labels differ in length")
    a.exact_pin(pin)
    repo, root = Path(repo).resolve(strict=True), Path(root)
    target, logs, scratch = root / side, Path(logs), Path(scratch)
    require(not os.path.lexists(target), "target exists: %s" % target)
    other = root / LABELS[1 - LABELS.index(side)]
    for path in (target, other):
        require(not nested(path, repo), "snapshot nested with repository")
    require(not nested(target, other), "nested snapshot roots")
    for folder in (logs, scratch):
        require(not nested(folder, target) and not nested(folder, other),
                "evidence/scratch inside a snapshot root")
    manifest = load_manifest(manifest_path)
    require(manifest.get("schema") == SCHEMA, "manifest schema")
    require(side not in manifest["sides"], "side already recorded")
    if mktool:
        a.exact_pin(cand_pin)
    home = scratch / ("home-" + side)
    require(not home.exists(), "HOME is not fresh: %s" % home)
    home.mkdir(parents=True)
    Path(tmpdir).mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    root.mkdir(parents=True, exist_ok=True)
    env = environment(home, tmpdir)
    record = {"label": side, "root": str(target), "home": str(home),
              "pin": pin, "mktool": mktool, "root_existed_before": False,
              "commands": []}

    def step(name, argv, cwd, stdin=None):
        entry = execute(runner, name, argv, cwd, env, stdin, logs, side)
        record["commands"].append(entry)
        require(entry["exit"] == 0, "%s failed (exit %s)" %
                (name, entry["exit"]))

    try:
        step("clone", ["git", "clone", "--shared", "--no-checkout",
                       str(repo), str(target)], repo)
        step("checkout", ["git", "checkout", "--detach", pin], target)
        record["tree"] = a.git(target, "rev-parse", "HEAD^{tree}")
        if mktool:
            sealed = sg.apply_mktool(target)
            blob = a.git(target, "hash-object", MKTOOL_PATH)
            want = a.git(repo, "rev-parse", "%s:%s" % (cand_pin, MKTOOL_PATH))
            require(blob == want, "patched mktool.ML is not blob-equal to "
                    "the candidate's")
            record["patch"] = dict(sealed, candidate_blob=want)
        else:
            record["patch"] = None
        record["status_before"] = status_lines(target)
        record["ignored_before"] = [
            line for line in status_lines(target, "--ignored=matching")
            if line.startswith("!!")]
        expected = [" M " + MKTOOL_PATH] if mktool else []
        require(record["status_before"] == expected,
                "tree is not clean (or not exactly the sealed patch)")
        require(not record["ignored_before"], "ignored files before build")
        record["stale_before"] = stale_products(target, tracked_paths(target))
        require(not record["stale_before"], "stale products before build")
        record["input_hash"] = input_hash(target)
        step("configure", [poly], target, target / CONFIGURE_INPUT)
        step("build", ["bin/build", "--no-cache", "-t", "-j%d" % jobs,
                       "--seq=" + SEQUENCE], target)
    except BaseException:
        manifest["sides"][side] = dict(record, incomplete=True)
        store_manifest(manifest_path, manifest)
        raise
    record["build_interval_ns"] = [record["commands"][2]["start_ns"],
                                   record["commands"][3]["end_ns"]]
    record["products"] = scan_products(target)
    record["systeml"] = systeml_hashes(target)
    live = probe(poly, env)
    if "toolchain" in manifest:
        same_toolchain(manifest["toolchain"], live)
    manifest.setdefault("toolchain", live)
    manifest.setdefault("host", host())
    manifest["sides"][side] = record
    store_manifest(manifest_path, manifest)
    return record


def systeml_hashes(root):
    data = (Path(root) / SYSTEML).read_bytes()
    return {"raw": sha256_bytes(data),
            "normalized": sha256_bytes(
                data.replace(str(root).encode(), b"<ROOT>"))}


# -- verify ------------------------------------------------------------

def normalized_command(entry, record, pin):
    """A command with the side's own strings replaced, for comparison."""
    text = json.dumps({k: entry[k] for k in
                       ("name", "argv", "cwd", "env", "stdin_hash")},
                      sort_keys=True)
    for value, mark in ((record["root"], "<ROOT>"), (record["home"],
                        "<HOME>"), (pin, "<PIN>")):
        text = text.replace(value, mark)
    return text


def verify_side(record, label, expected_pin):
    require(record.get("label") == label and not record.get("incomplete"),
            "%s: incomplete or mislabelled record" % label)
    root = Path(record["root"])
    require(root.name == label, "%s: root is not named by its label" % label)
    root = root.resolve(strict=True)
    pin = record["pin"]
    a.exact_pin(pin)
    if expected_pin is not None:
        a.exact_pin(expected_pin)
        require(pin == expected_pin, "%s: recorded pin is not the "
                "expected one" % label)
    require(a.git(root, "rev-parse", "--show-toplevel") == str(root),
            "%s: not a worktree root" % label)
    require(a.git(root, "rev-parse", "HEAD") == pin,
            "%s: HEAD is not the pin" % label)
    require(a.git(root, "rev-parse", "HEAD^{tree}") == record["tree"],
            "%s: tree hash changed" % label)
    require(record["root_existed_before"] is False, "%s: root pre-existed"
            % label)
    require(record["stale_before"] == [] and record["ignored_before"] == [],
            "%s: stale or ignored files before the build" % label)
    live = patch_seal(root)
    if record["mktool"]:
        sealed = record["patch"]
        require(sealed is not None and record["status_before"] ==
                [" M " + MKTOOL_PATH], "%s: baseline is not patched" % label)
        require(live["sha256"] == sealed["sha256"] and
                live["bytes"] == sealed["bytes"],
                "%s: working tree differs from the sealed patch" % label)
        names = a.git(root, "diff", "--name-only").splitlines()
        require(names == [MKTOOL_PATH], "%s: patch touches other files"
                % label)
        require(a.git(root, "hash-object", MKTOOL_PATH) ==
                sealed["candidate_blob"], "%s: mktool blob differs from "
                "the candidate's" % label)
    else:
        require(record["patch"] is None and live["bytes"] == 0 and
                record["status_before"] == [],
                "%s: tree is dirty or patched" % label)
    require(not a.git(root, "diff", "--cached"), "%s: staged changes"
            % label)
    require(input_hash(root) == record["input_hash"],
            "%s: input hash changed" % label)
    commands = record["commands"]
    require([c["name"] for c in commands] ==
            ["clone", "checkout", "configure", "build"],
            "%s: unexpected command list" % label)
    for c in commands:
        require(c["exit"] == 0, "%s: %s exited %s" %
                (label, c["name"], c["exit"]))
        require(set(c["env"]) == set(ENV_KEYS), "%s: not an env -i "
                "environment" % label)
        log = Path(c["log"])
        require(not nested(log.parent, root), "%s: log inside the root"
                % label)
        if log.exists():
            require(a.seal(log) == c["log_hash"], "%s: log changed" % label)
    first, last = record["build_interval_ns"]
    require(first == commands[2]["start_ns"] and
            last == commands[3]["end_ns"] and first < last,
            "%s: bad build interval" % label)
    products = scan_products(root)
    require(set(products) == set(record["products"]),
            "%s: product set changed" % label)
    for rel, now in products.items():
        was = record["products"][rel]
        require(now == was, "%s: product changed: %s" % (label, rel))
        require(first <= was["mtime_ns"] <= last,
                "%s: stale product (mtime outside the build): %s"
                % (label, rel))
    for rel in BIN_PRODUCTS:
        require(rel in products, "%s: missing %s" % (label, rel))
    require(any(r.startswith("sigobj/") and r.endswith(".uo")
                for r in products), "%s: no sigobj products" % label)
    require(systeml_hashes(root) == record["systeml"],
            "%s: Systeml.sml changed" % label)
    return products


def verify(manifest, base_pin=None, cand_pin=None, probe=probe_toolchain,
           poly=POLY):
    """Audit a manifest (a dict) against the live trees; raises on any
    failure and returns the summary otherwise."""
    require(manifest.get("schema") == SCHEMA, "wrong manifest schema")
    sides = manifest.get("sides", {})
    require(set(sides) == set(LABELS), "both sides must be recorded")
    base, cand = sides["base"], sides["cand"]
    require(len(Path(base["root"]).name) == len(Path(cand["root"]).name) and
            len(base["root"]) == len(cand["root"]),
            "HOLDIR strings differ in length")
    require(not nested(base["root"], cand["root"]), "nested snapshot roots")
    require(base["mktool"] is True and cand["mktool"] is False,
            "only the baseline carries the mktool patch")
    pins = {"base": base_pin, "cand": cand_pin}
    products = {l: verify_side(sides[l], l, pins[l]) for l in LABELS}
    inodes = [{(p["dev"], p["ino"]) for p in products[l].values()}
              for l in LABELS]
    require(not (inodes[0] & inodes[1]), "snapshots share inodes")
    for label in LABELS:
        require(len(inodes[LABELS.index(label)]) ==
                len({p["resolved"] for p in products[label].values()}),
                "%s: product hard links" % label)
    for x, y in zip(base["commands"], cand["commands"]):
        require(normalized_command(x, base, base["pin"]) ==
                normalized_command(y, cand, cand["pin"]),
                "argv/env differ between sides: " + x["name"])
    require(base["systeml"]["normalized"] == cand["systeml"]["normalized"],
            "configured Systeml.sml differs between sides")
    require(base["build_interval_ns"][1] <= cand["build_interval_ns"][0],
            "builds were not serial")
    for label in LABELS:
        require(nested(sides[label]["home"], sides[label]["root"]) is False,
                "HOME inside the root")
    require(base["home"] != cand["home"], "shared HOME")
    live = probe(poly, environment("/nonexistent"))
    same_toolchain(manifest["toolchain"], live)
    return {"schema": SCHEMA, "base_products": len(products["base"]),
            "cand_products": len(products["cand"]), "status": "pass"}


# -- compare -----------------------------------------------------------

ANSI = re.compile(r"\x1b\[[0-9;?]*[A-Za-z]")
TIMING = re.compile(r"\(\s*\d+(\.\d+)?\s*m?s\s*\)")


def normalize_text(data, root):
    text = data.decode("latin-1")
    for spelling in {str(root), os.path.realpath(root)}:
        text = text.replace(spelling, PLACEHOLDER)
    return text


def normalize_log(data, root):
    text = ANSI.sub("", normalize_text(data, root))
    return TIMING.sub("(<TIME>)", text)


def theory_files(root):
    found = {}
    for folder, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".git", "sigobj")]
        for name in names:
            if re.fullmatch(r".*Theory\.(sig|dat)", name):
                path = Path(folder) / name
                if not path.is_symlink():
                    found[path.relative_to(root).as_posix()] = path
    return dict(sorted(found.items()))


def selftest_logs(root):
    found = {}
    for area in AREAS:
        base = Path(root) / "src" / area
        for folder, dirs, names in os.walk(base):
            for name in names:
                if name.endswith(".log") and (
                        "selftest" in name or
                        Path(folder).parts[-2:] == (".hol", "logs")):
                    path = Path(folder) / name
                    found[path.relative_to(root).as_posix()] = path
    return dict(sorted(found.items()))


def differ(kind, rel, base_path, cand_path, base_root, cand_root,
           normalizer):
    x, y = Path(base_path).read_bytes(), Path(cand_path).read_bytes()
    if kind == "log":
        nx = normalize_log(x, base_root).encode("latin-1")
        ny = normalize_log(y, cand_root).encode("latin-1")
    elif rel.endswith(".sig"):
        nx = normalize_text(x, base_root).encode("latin-1")
        ny = normalize_text(y, cand_root).encode("latin-1")
    else:
        nx = x.replace(str(base_root).encode(), PLACEHOLDER.encode())
        ny = y.replace(str(cand_root).encode(), PLACEHOLDER.encode())
    if nx == ny:
        return None
    if kind == "theory" and rel.endswith(".dat") and normalizer is not None \
            and normalizer(base_path, cand_path):
        return None
    return {"path": rel, "base": sha256_bytes(nx), "cand": sha256_bytes(ny)}


def compare(manifest, dat_normalizer=None):
    """The behaviour record of two verified trees."""
    base, cand = manifest["sides"]["base"], manifest["sides"]["cand"]
    roots = {"base": Path(base["root"]), "cand": Path(cand["root"])}
    blocked = []
    out = {"schema": BEHAVIOR_SCHEMA}
    for kind, key, finder in (("theory", "theories", theory_files),
                              ("log", "logs", selftest_logs)):
        files = {l: finder(roots[l]) for l in LABELS}
        common = sorted(set(files["base"]) & set(files["cand"]))
        differing = [d for d in (
            differ(kind, rel, files["base"][rel], files["cand"][rel],
                   roots["base"], roots["cand"], dat_normalizer)
            for rel in common) if d]
        base_only = sorted(set(files["base"]) - set(files["cand"]))
        out[key] = {
            "common": len(common), "differing": differing,
            "baseline_only": base_only,
            "candidate_only": sorted(set(files["cand"]) -
                                     set(files["base"]))}
        blocked += [kind + " differs: " + d["path"] for d in differing]
        blocked += [kind + " missing on cand: " + p for p in base_only]
        require(common, "no common %ss" % kind)
    for area in AREAS:
        prefix = "src/%s/" % area
        for label in LABELS:
            if not any(p.startswith(prefix)
                       for p in selftest_logs(roots[label])):
                blocked.append("no selftest log under %s on %s" %
                               (prefix, label))
    for label in LABELS:
        build = manifest["sides"][label]["commands"][3]
        if build["exit"] != 0:
            blocked.append("%s build failed" % label)
    out["blocked"] = blocked
    out["status"] = "blocked" if blocked else "pass"
    out["normalization"] = {
        "root": PLACEHOLDER, "logs": "ANSI stripped, (Ns) masked",
        "dat": "byte-equal; no theorytool normalizer unless supplied"
        if dat_normalizer is None else "supplied normalizer"}
    return out


# -- command line ------------------------------------------------------

def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="command", required=True)
    b = sub.add_parser("build")
    b.add_argument("--repo", type=Path, default=HERE.parents[3])
    b.add_argument("--root", type=Path, required=True)
    b.add_argument("--manifest", type=Path, required=True)
    b.add_argument("--evidence", type=Path, required=True)
    b.add_argument("--scratch", type=Path, required=True)
    b.add_argument("--side", choices=LABELS, required=True)
    b.add_argument("--pin", required=True)
    b.add_argument("--mktool", action="store_true")
    b.add_argument("--cand-pin")
    b.add_argument("--jobs", type=int, default=8)
    b.add_argument("--poly", default=POLY)
    b.add_argument("--tmpdir", default="/dev/shm/t32/tmp")
    v = sub.add_parser("verify")
    v.add_argument("--manifest", type=Path, required=True)
    v.add_argument("--base-pin")
    v.add_argument("--cand-pin")
    v.add_argument("--poly", default=POLY)
    c = sub.add_parser("compare")
    c.add_argument("--manifest", type=Path, required=True)
    c.add_argument("--output", type=Path, required=True)
    c.add_argument("--base-pin")
    c.add_argument("--cand-pin")
    c.add_argument("--poly", default=POLY)
    args = p.parse_args(argv)
    if args.command == "build":
        with a.serial_lock(args.repo) as fds:
            build_side(args.repo, args.side, args.pin, args.root,
                       args.manifest, args.evidence, args.scratch,
                       mktool=args.mktool, cand_pin=args.cand_pin,
                       jobs=args.jobs, poly=args.poly, tmpdir=args.tmpdir,
                       runner=real_runner(fds))
        return 0
    manifest = json.loads(args.manifest.read_text())
    summary = verify(manifest, args.base_pin, args.cand_pin, poly=args.poly)
    if args.command == "verify":
        print(json.dumps(summary, indent=2))
        return 0
    result = compare(manifest)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print("compare:", result["status"])
    return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
