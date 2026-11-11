#!/usr/bin/env python3
r"""Reproduce TASK25 using pinned sources and isolated build/test scratch.

Fresh (expensive; bootstrap, routine tests, then consumer tests)::

  python3 -B src/simp/tests/compatibility/run_task25_consumer.py \
    --consumer-patch /path/consumer.patch --output /tmp/task25-output

Reuse explicitly supplied, already configured scratch (not a fresh-build claim)::

  ... --existing-core /tmp/task25-core \
      --existing-consumer /tmp/task25-isolated

Other simplifier revision (TASK32 style; explicit private alias and scratch,
nothing in /tmp)::

  python3 -B src/simp/tests/compatibility/run_task25_consumer.py \
    --consumer-patch src/simp/tests/compatibility/consumer/consumer.patch \
    --simplifier-revision C32 --alias /dev/shm/t32-alias \
    --scratch /dev/shm/t32-consumer --jobs 8 --skip-routine \
    --output .agent-files/evidence/task32/consumer

--simplifier-revision must descend from the TASK25 pin; the core is that
revision plus the consumer's own listScript.sml. --alias (absolute) replaces
the alias derived from the caller's configuration and must equal the HOLDIR
the core is configured with. --scratch must not exist; it is created, never
placed in /tmp, and removed on exit. Inside the caller checkout it is accepted
only when ignored and untracked, and the same holds for --output. The patch
sha256 must equal the pin (--patch-sha256 overrides it for a reviewed
refresh). --jobs N passes -jN to bin/build; --skip-routine omits the
bootstrap's extra -t pass.

--prepare-only checks archives/patch and emits source inventories, without
configuring or building. Task-owned staging is removed even on failure. Output
must be new; patch, logs and compressed inventories survive there. Existing
scratch is source-checked, rebuilt/tested, and NOT removed. Its four translated
Scripts are verified against the canonical sources before being replaced;
theory Script mtimes are advanced to force execution, not merely cache hits.
Requires Linux bwrap, Python >= 3.12, git, Poly/ML (poly + polyc), C++ toolchain.
No changes to production parsers, canonical inputs, caller checkout or its heaps.
"""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time

MAIN = "4a0ad8e9160dd911393385d748b3535fc5ce65ba"
CONSUMER = "442009a1f7f04366573dc2b649d31650ea7b113b"
PATCH_SHA256 = (
    "6a0a8f54dcb1af06a1b824f56453619195a11d321f97851bcc7b61149166ad1a")
BANNED_SCRATCH = (Path("/tmp"), Path("/var/tmp"))
LIST = "src/list/src/listScript.sml"
PARSER = "tools/parsing/HOLSourceParser.sml"
DRIVER = "tools/quote-filter/poly-unquote.ML"
SEQUENCE = "--seq=tools/sequences/upto-parallel"
DIRS = ("rules", "order", "linarith", "classical", "blast", "clasimp",
        "aesop", "linarith/instances", "seeds", "benchmarks", "examples")
THEORIES = ("rules", "linarith", "clasimp", "aesop", "seeds")
NUMERIC = re.compile(rb"\[[^\[\]]*\b[A-Za-z_][A-Za-z_0-9]*\s*=\s*~?\s*[0-9]",
                     re.S)
ANSI = re.compile(r"\x1b\[[0-9;]*m")
ERROR = re.compile(r"(?im)(?:\bStatic (?:Errors?|error)\b|\berror in load\b|"
                   r"\bException- .* raised\b|\bUncaught exception\b|"
                   r"^.*:\d+(?:\.\d+)?: error:|^\s*(?:FAIL<\d+>|FAILED!))")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fingerprint(path):
    # Stream large heaps/executables rather than retaining them in memory.
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    return {"sha256": digest, "bytes": path.stat().st_size}


def inventory(root):
    result = {}
    for path in sorted(root.rglob("*")):
        name = str(path.relative_to(root))
        if path.is_symlink():
            result[name] = {"symlink": os.readlink(path)}
        elif path.is_file():
            result[name] = fingerprint(path)
    return result


def verify(root, expected, exceptions=()):
    for name, info in expected.items():
        path = root / name
        for parent in path.parents:
            require(not parent.is_symlink(),
                    "symlink source directory: " + str(parent))
            if parent == root:
                break
        if name in exceptions:
            require(not path.is_symlink(), "symlink translated input: " + str(path))
            continue
        actual = ({"symlink": os.readlink(path)} if path.is_symlink()
                  else fingerprint(path))
        require(actual == info, "source drift: " + str(path))


def verify_consumer(root, expected, exceptions=()):
    verify(root, expected, exceptions)
    for path in (root / "src/auto").rglob("*"):
        if ".hol" in path.parts:
            continue
        if path.is_symlink():
            require(str(path.relative_to(root)) in expected,
                    "unarchived symlink: " + str(path))
        if path.suffix in (".sml", ".sig", ".ML") or path.name == "Holmakefile":
            require(str(path.relative_to(root)) in expected,
                    "unarchived consumer source: " + str(path))


def git_call(repo, *args):
    # Git binary output is kept separate from stderr/log framing.
    command = ["git", "--no-optional-locks", "-C", str(repo), *args]
    return command, subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        env={k: v for k, v in os.environ.items() if not k.startswith("GIT_")})


def commit_of(repo, revision):
    require(isinstance(revision, str) and revision and
            not revision.startswith("-"), "bad revision: " + repr(revision))
    _, process = git_call(repo, "rev-parse", "--verify", "--quiet",
                          revision + "^{commit}")
    full = process.stdout.decode().strip()
    require(process.returncode == 0 and re.fullmatch(r"[0-9a-f]{40}", full),
            "unknown revision: " + revision)
    return full


def descends_from(repo, ancestor, revision):
    _, process = git_call(repo, "merge-base", "--is-ancestor", ancestor,
                          revision)
    require(process.returncode in (0, 1), "git merge-base failed")
    return process.returncode == 0


def outside_tracked(repo, path, what):
    """Refuse a path in the caller checkout unless ignored and untracked."""
    path = Path(os.path.realpath(path))
    repo = Path(os.path.realpath(repo))
    require(not repo.is_relative_to(path), what + " contains caller checkout")
    if not path.is_relative_to(repo):
        return
    relative = str(path.relative_to(repo))
    existing = path
    while not existing.exists():
        existing = existing.parent
    _, tracked = git_call(repo, "ls-files", "--",
                          str(existing.relative_to(repo)))
    if existing == repo:
        tracked.stdout = b""  # a new top-level name; only ignore status counts
    require(tracked.returncode == 0 and not tracked.stdout.strip(),
            what + " inside a tracked tree: " + str(path))
    _, ignored = git_call(repo, "check-ignore", "-q", "--no-index", "--",
                          relative + "/x")
    require(ignored.returncode == 0,
            what + " inside caller checkout and not ignored: " + str(path))


def plan(args, repo):
    """Validate every option that needs no build; returns resolved values."""
    out = {}
    require(args.consumer_patch.is_file(), "missing consumer patch")
    out["patch_sha256"] = sha(args.consumer_patch.read_bytes())
    expected = args.patch_sha256 or PATCH_SHA256
    require(re.fullmatch(r"[0-9a-f]{64}", expected), "bad --patch-sha256")
    require(out["patch_sha256"] == expected,
            "consumer patch sha256 mismatch: " + out["patch_sha256"])
    out["patch_pin_overridden"] = expected != PATCH_SHA256
    main = commit_of(repo, MAIN)
    require(main == MAIN, "pinned simplifier revision is not " + MAIN)
    simplifier = commit_of(repo, args.simplifier_revision)
    require(descends_from(repo, MAIN, simplifier),
            "simplifier revision does not descend from the pin: " +
            args.simplifier_revision)
    require(commit_of(repo, args.consumer_revision) == CONSUMER,
            "revision is not the pinned prerequisite: " +
            args.consumer_revision)
    out["simplifier"] = simplifier
    require(args.jobs is None or args.jobs >= 1, "--jobs must be positive")
    if args.scratch is not None:
        require(args.scratch.is_absolute(), "--scratch must be absolute")
        scratch = Path(os.path.abspath(args.scratch))
        real = Path(os.path.realpath(scratch))
        require(not any(real.is_relative_to(b) or
                        real.is_relative_to(Path(os.path.realpath(b)))
                        for b in BANNED_SCRATCH),
                "scratch must not be in /tmp")
        outside_tracked(repo, scratch, "scratch")
        require(not os.path.lexists(scratch), "scratch already exists")
        out["scratch"] = scratch
    if args.alias is not None:
        alias = args.alias
        require(alias.is_absolute() and str(alias) == os.path.normpath(alias)
                and alias != Path("/"), "--alias must be a normalized "
                "absolute path")
        out["alias"] = alias
    return out


def build_commands(jobs, skip_routine):
    flag = [] if jobs is None else ["-j" + str(jobs)]
    commands = [("bootstrap", ["bin/build", *flag, SEQUENCE])]
    if not skip_routine:
        commands.append(("routine", ["bin/build", "-t", *flag, SEQUENCE]))
    return commands


def check_configured_alias(core, alias):
    configured = (core / "tools/Holmake/Systeml.sml").read_text()
    require('val HOLDIR = "' + str(alias) + '"' in configured,
            "core is configured with a different alias")


class Runner:
    def __init__(self, repo, output, scratch, alias, core, consumer):
        self.repo, self.output, self.scratch = repo, output, scratch
        self.alias, self.core, self.consumer = alias, core, consumer
        self.alias_mask = alias.parent
        while not self.alias_mask.is_dir() or self.alias_mask.is_symlink():
            self.alias_mask = self.alias_mask.parent
        self.manifest = {"schema": 1, "success": False, "runs": [],
                         "runner": fingerprint(Path(__file__))}

    def dump(self, name, value):
        data = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
        path = self.output / name
        path.write_bytes(gzip.compress(data, mtime=0) if name.endswith(".gz")
                         else data)
        return {"file": name, **fingerprint(path)}

    def run(self, label, command, *, cwd=None, data=None, marker=None,
            timeout=7200, scan=True):
        log = self.output / (f"{len(self.manifest['runs']):03d}-" + label + ".log")
        record = {"label": label, "command": list(map(str, command)),
                  "cwd": str(cwd or self.repo), "log": log.name,
                  "timeout_seconds": timeout}
        if data is not None:
            record["stdin_sha256"] = sha(data)
        self.manifest["runs"].append(record)
        start = time.monotonic()
        try:
            with log.open("wb") as stream:
                process = subprocess.Popen(record["command"], cwd=cwd or self.repo,
                                           stdin=subprocess.PIPE if data is not None
                                           else subprocess.DEVNULL,
                                           stdout=stream, stderr=subprocess.STDOUT,
                                           start_new_session=True,
                                           env={**{k: v for k, v in os.environ.items()
                                                   if not k.startswith("GIT_")},
                                                "LC_ALL": "C",
                                                "GIT_OPTIONAL_LOCKS": "0"})
                try:
                    process.communicate(data, timeout=timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.communicate()
                    record["timed_out"] = True
                except BaseException:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.communicate()
                    record["exit"] = process.returncode
                    raise
                record["exit"] = process.returncode
        finally:
            record["seconds"] = round(time.monotonic() - start, 3)
            record["output"] = fingerprint(log)
        text = ANSI.sub("", log.read_text(errors="replace"))
        record["counts"] = {"lines": len(text.splitlines()),
                            "OK": len(re.findall(r"\bOK\b", text)),
                            "static_errors": len(ERROR.findall(text))}
        require(record.get("exit") == 0, "command failed: " + label)
        require(not scan or not ERROR.search(text),
                "static/runtime error in " + str(log))
        if marker:
            require(marker in text, "missing marker " + marker + ": " + label)
        return text

    def git(self, *args):
        command, process = git_call(self.repo, *args)
        record = {"command": command, "cwd": str(self.repo)}
        self.manifest.setdefault("git", []).append(record)
        record.update(exit=process.returncode, stdout_sha256=sha(process.stdout),
                      stderr=process.stderr.decode(errors="replace"))
        require(process.returncode == 0, "git failed: " + repr(args))
        return process.stdout

    def archive(self, revision, target, paths=()):
        data = self.git("archive", "--format=tar", revision, *paths)
        target.mkdir(parents=True)
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            archive.extractall(target, filter="data")
        return inventory(target)

    def sandbox(self, command, *, folder="", mounted=False, overlays=()):
        alias = str(self.alias)
        # Host (including caller repo and existing scratch) starts read-only.
        # Only task staging and explicit scratch mounts become writable. Hide
        # the original alias, including symlinks, before installing the core.
        cmd = ["bwrap", "--die-with-parent", "--clearenv", "--unshare-pid",
               "--unshare-net", "--ro-bind", "/", "/", "--dev", "/dev",
               "--proc", "/proc", "--tmpfs", "/tmp",
               "--tmpfs", str(self.alias_mask),
               "--ro-bind", str(self.repo), str(self.repo),
               "--ro-bind", str(self.git_common), str(self.git_common),
               # After the read-only repo: scratch may live inside it.
               "--bind", str(self.scratch), str(self.scratch),
               "--bind", str(self.core), alias]
        if mounted:
            cmd += ["--bind", str(self.consumer / "src/auto"), alias + "/src/auto",
                    "--ro-bind", str(self.consumer / "help/Docfiles"),
                    alias + "/help/Docfiles"]
        for source, target in overlays:
            cmd += ["--ro-bind", str(source), str(target)]
        cmd += ["--setenv", "HOLDIR", alias, "--setenv", "PATH",
                alias + "/bin:" + os.environ["PATH"],
                "--setenv", "HOME", str(self.scratch),
                "--setenv", "TMPDIR", "/tmp", "--setenv", "LC_ALL", "C",
                "--setenv", "TERM", "dumb"]
        if mounted:
            cmd += ["--setenv", "HOLSELFTESTLEVEL", "1"]
        cmd += ["--chdir", str(self.alias / folder), "--", *map(str, command)]
        return cmd

    def inside(self, label, command, **kwargs):
        keys = {key: kwargs.pop(key) for key in ("folder", "mounted", "overlays")
                if key in kwargs}
        return self.run(label, self.sandbox(command, **keys), **kwargs)

    def parser(self, canonical):
        driver = (self.core / DRIVER).read_bytes()
        ingredients = [DRIVER] + [os.path.normpath(str(Path(DRIVER).parent /
                                      name.decode())) for name in
                                 re.findall(rb'^use "([^"]+)";', driver, re.M)]
        sources = self.scratch / "parser-sources"
        lock = {}
        for name in ingredients:
            require(not Path(name).is_absolute() and ".." not in Path(name).parts,
                    "unsafe parser ingredient: " + name)
            data = (self.git("show", CONSUMER + ":" + name) if name == PARSER
                    else (self.core / name).read_bytes())
            path = sources / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            lock[name] = {"sha256": sha(data), "bytes": len(data),
                          "origin": CONSUMER if name == PARSER else
                          "configured private core"}
        self.manifest["parser_sources"] = self.dump("parser-sources.json", lock)
        binary = self.scratch / "quote-filter"
        self.inside("parser-build", ["sh", "-c", 'cd "$1"; exec polyc -o "$2" '
                     'poly-unquote.ML', "sh", str(sources / Path(DRIVER).parent),
                     str(binary)])
        self.manifest["quote_filter"] = fingerprint(binary)
        self.libraries("parser-runtime", binary)
        selected = [p for p in sorted((canonical / "src/auto").rglob("*Script.sml"))
                    if NUMERIC.search(p.read_bytes())]
        require(len(selected) == 4, "expected exactly four numeric Scripts")
        expansions = {}
        for index, source in enumerate(selected):
            name = str(source.relative_to(canonical))
            target = self.consumer / name
            generated = self.scratch / (f"expanded-{index}.sml")
            # Use the real build-tree filename for theorem location metadata,
            # but expose the immutable canonical input at that name read-only.
            self.inside("expand-" + source.stem,
                        [str(binary), str(target), str(generated)],
                        overlays=[(source, target)])
            original, expanded = source.read_bytes(), generated.read_bytes()
            require(target.read_bytes() in (original, expanded),
                    "noncanonical numeric Script: " + str(target))
            expansions[name] = {"canonical_sha256": sha(original),
                                "expanded_sha256": sha(expanded),
                                "input_filename": str(target),
                                "previous_sha256": sha(target.read_bytes())}
            target.write_bytes(expanded)
        self.manifest["expansions"] = expansions
        return set(expansions)

    def libraries(self, label, binary):
        text = self.inside(label, ["ldd", str(binary)], scan=False)
        paths = re.findall(r"=> (/\S+)|^\s*(/\S+) \(", text, re.M)
        for pair in paths:
            path = Path(next(p for p in pair if p))
            self.manifest.setdefault("runtime_libraries", {})[str(path)] = (
                fingerprint(path.resolve()))

    def closure(self, roots):
        """Resolve HOLFS .uo/.ui plans, including sigobj's absolute symlinks."""
        records, resolved_modules = {}, {}

        def physical(logical):
            path = Path(str(logical).replace("$(HOLDIR)", str(self.alias)))
            require(path.is_absolute(), "relative dependency: " + str(path))
            if path.is_relative_to(self.alias / "src/auto"):
                return self.consumer / "src/auto" / path.relative_to(
                    self.alias / "src/auto")
            require(path.is_relative_to(self.alias),
                    "dependency outside private core: " + str(path))
            return self.core / path.relative_to(self.alias)

        def locate(logical):
            path = physical(logical)
            for _ in range(40):
                if path.is_symlink():
                    link = Path(os.readlink(path))
                    path = (physical(link) if link.is_absolute()
                            else Path(os.path.normpath(path.parent / link)))
                elif path.is_file():
                    for parent in path.parents:
                        require(not parent.is_symlink(),
                                "symlink closure directory: " + str(parent))
                        if parent in (self.core, self.consumer):
                            break
                    return path
                else:
                    munged = path.parent / ".hol/objs" / path.name
                    if not munged.is_file():
                        # Meta's loaded set is keyed by module NAME, not path.
                        # Some plans retain alternate logical locations for an
                        # already loaded module (notably postkernel/Overlay).
                        key = Path(logical).name
                        require(key in resolved_modules,
                                "missing closure file: " + str(path))
                        return resolved_modules[key]
                    path = munged
            raise RuntimeError("symlink cycle: " + str(logical))

        def visit(logical):
            logical = str(logical).replace("$(HOLDIR)", str(self.alias))
            if logical in records:
                return
            path = locate(logical)
            require(path.is_relative_to(self.core) or
                    path.is_relative_to(self.consumer), "escaped closure")
            records[logical] = {"physical": str(path), **fingerprint(path)}
            if path.suffix in (".uo", ".ui"):
                resolved_modules[Path(logical).name] = path
                lines = path.read_text().splitlines()
                records[logical]["dependencies"] = lines
                for line in lines:
                    if not line:
                        continue
                    if Path(line).suffix in (".sml", ".sig", ".ML"):
                        visit(line)
                    elif Path(line).name != path.stem:
                        # Plans include their own logical stem. Meta.load marks
                        # a module loaded BEFORE reading its .ui/.uo; following
                        # that self-edge invents an alternate .uo (e.g. Tracing
                        # has its implementation under tracing/no).
                        visit(line + ".ui")
                        visit(line + ".uo")
        for root in roots:
            if Path(root).suffix == ".uo":
                visit(Path(root).with_suffix(".ui"))
            visit(root)
        self.manifest["loaded_dependency_closure"] = self.dump(
            "dependency-closure.json.gz", records)
        return records

    def launcher(self, path, module):
        text = path.read_text()
        lines = [line for line in text.splitlines() if line.strip()]
        require(len(lines) == 4 and lines[:2] == ["#!/bin/sh", "set -e"]
                and lines[-1] == "exit 0", "nonstandard launcher: " + str(path))
        # Do not infer source provenance from a launcher running arbitrary code.
        command = shlex.split(lines[2])
        require(command[:3] == [str(self.alias / "bin/hol"), "--gcthreads=1", "run"]
                and len(command) == 5 and command[-1] == module,
                "unexpected launcher command: " + str(path))
        heap = command[3].removeprefix("--holstate=")
        require(command[3].startswith("--holstate=") and heap in
                (str(self.alias / "bin/hol.state"),
                 str(self.alias / "bin/hol.state0")), "unexpected heap")
        folder = path.parent.relative_to(self.consumer / "src/auto")
        self.manifest.setdefault("launchers", {})[str(path)] = {
            "text": text, "command": command, "heap": heap,
            "source_plan": str(self.alias / "src/auto" / folder / (module + ".uo")),
            **fingerprint(path)}

    def consumers(self):
        make = [str(self.alias / "bin/Holmake"), "--no-project", "--no-cache",
                "--rebuild=mtime", "-j1", "HOLSELFTESTLEVEL=1"]
        roots, products = [], {}
        folders = list(DIRS) + [name + "/theory_tests" for name in THEORIES]
        touched = []
        # Force actual Script execution in reuse mode without deleting any
        # caller-owned products, changing proofs, or using cachekey downloads.
        for folder in folders:
            directory = self.consumer / "src/auto" / folder
            require((directory / "Holmakefile").is_file(),
                    "missing consumer directory: " + folder)
            for source in sorted(directory.glob("*Script.sml")):
                os.utime(source, None)
                touched.append(str(source))
        self.manifest["forced_script_mtimes"] = touched
        for folder in folders:
            directory = self.consumer / "src/auto" / folder
            label = folder.replace("/", "-")
            self.inside("build-" + label, make + ["all"],
                        folder="src/auto/" + folder, mounted=True)
            if folder in DIRS and folder != "examples":
                require((directory / "selftest.sml").is_file(),
                        "missing selftest: " + folder)
                require((directory / "selftest.exe").is_file(),
                        "missing launcher: " + folder)
                self.launcher(directory / "selftest.exe", "selftest")
                text = self.inside("level1-" + label, ["./selftest.exe"],
                                   folder="src/auto/" + folder, mounted=True,
                                   marker="OK")
                require(re.search(r"\bOK\b", text), "no passed tests: " + folder)
                products[str(directory / "selftest.exe")] = fingerprint(
                    directory / "selftest.exe")
                roots.append(self.alias / "src/auto" / folder / "selftest.uo")
            scripts = list(directory.glob("*Script.sml"))
            if folder == "examples" or folder.endswith("/theory_tests"):
                require(scripts, "no theories: " + folder)
            for script in sorted(scripts):
                stem = script.name.removesuffix("Script.sml") + "Theory"
                for suffix in (".uo", ".ui", ".sml", ".sig", ".dat"):
                    path = directory / ".hol/objs" / (stem + suffix)
                    require(path.is_file(), "missing theory product: " + str(path))
                    products[str(path)] = fingerprint(path)
                roots.append(self.alias / "src/auto" / folder / (stem + ".uo"))
            for executable in sorted(directory.glob("*.exe")):
                products[str(executable)] = fingerprint(executable)
        self.manifest["products"] = self.dump("products.json.gz", products)
        return roots

    def fixture(self):
        # Independent generated fixture: canonical selftests remain unchanged.
        directory = self.scratch / "path-fixture"
        directory.mkdir()
        modules = ["simpLib", "Traverse", "combinSimpsExt", "trackedSimpDefaults",
                   "clasetLib", "clasimpLib", "trackedAutoDefaults"]
        paths = [str(self.alias / "src/auto" / folder)
                 for folder in ("rules", "clasimp")]
        source = directory / "task25Paths.sml"
        source.write_text(
            "val _ = Meta.loadPath := [" + ",".join(map(json.dumps, paths)) +
            "] @ !Meta.loadPath;\nval _ = List.app Meta.load [" +
            ",".join(map(json.dumps, modules)) + "];\n" +
            'val _ = List.app (fn (f,d) => print ("TASK25_MAP\\t" ^ f ^ '
            '"\\t" ^ d ^ "\\n")) (Binarymap.listItems (Meta.fileDirMap ()));\n' +
            "val _ = List.app (fn m => case Meta.findMod m of NONE => "
            'raise Fail ("missing module " ^ m) | SOME p => '
            'print ("TASK25_MOD\\t" ^ m ^ "\\t" ^ p ^ "\\n")) ["' +
            '\",\"'.join(modules) + '"];\nprint "TASK25_PATHS_OK\\n";\n')
        # The scratch directory is already writable/visible inside bwrap.
        shell = ["sh", "-c", 'cd "$1"; shift; exec "$@"', "sh", str(directory)]
        text = self.inside("paths-run", shell + [str(self.alias / "bin/hol"),
                    "run", "--holstate=" + str(self.alias / "bin/hol.state0"),
                    "task25Paths.sml"], mounted=True,
                    marker="TASK25_PATHS_OK")
        rows = [line.split("\t") for line in text.splitlines()
                if line.startswith(("TASK25_MOD\t", "TASK25_MAP\t"))]
        require(sum(row[0] == "TASK25_MOD" for row in rows) == len(modules),
                "incomplete module path fixture")
        self.manifest["module_paths"] = rows
        self.manifest["path_fixture"] = self.dump("path-fixture.json", {
            "sources": inventory(directory), "source_text": source.read_text(),
            "rows": rows})
        mapped = {row[1]: str(Path(row[2]) / row[1]) for row in rows
                  if row[0] == "TASK25_MAP"}
        require(all(m + ".sml" in mapped for m in modules),
                "key modules absent from Meta.fileDirMap")
        require(all(Path(p).is_relative_to(self.alias) for p in mapped.values()),
                "fileDirMap contains sources outside the private core/consumer")
        # Seal both actual source-load provenance and resolved load plans.
        return ([row[2] for row in rows if row[0] == "TASK25_MOD"] +
                list(mapped.values()))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--consumer-patch", type=Path, required=True)
    ap.add_argument("--patch-sha256")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--consumer-revision", default=CONSUMER)
    ap.add_argument("--simplifier-revision", default=MAIN)
    ap.add_argument("--alias", type=Path)
    ap.add_argument("--scratch", type=Path)
    ap.add_argument("--jobs", type=int)
    ap.add_argument("--skip-routine", action="store_true")
    ap.add_argument("--existing-core", type=Path)
    ap.add_argument("--existing-consumer", type=Path)
    ap.add_argument("--prepare-only", action="store_true")
    args = ap.parse_args()
    repo = Path(__file__).resolve().parents[4]
    output = args.output.resolve()
    if args.scratch is None:
        require(not output.is_relative_to(repo),
                "output must be outside caller checkout")
    else:
        outside_tracked(repo, output, "output")
    require(bool(args.existing_core) == bool(args.existing_consumer),
            "reuse requires both --existing-core and --existing-consumer")
    planned = plan(args, repo)
    config = repo / "sigobj/Systeml.sml"
    if "alias" in planned:
        alias = planned["alias"]
    else:
        match = re.search(r'^val HOLDIR = "([^"]+)"', config.read_text(), re.M)
        require(match is not None, "cannot derive configured Systeml.HOLDIR")
        alias = Path(match[1])  # Do NOT resolve: may be absent or a symlink.
    require(alias.is_absolute() and alias != repo, "need a private configured alias")
    output.mkdir(parents=True, exist_ok=False)
    if "scratch" in planned:
        scratch = planned["scratch"]
        scratch.mkdir(parents=True)
    else:
        scratch = Path(tempfile.mkdtemp(prefix="task25-run-", dir="/tmp"))
    core = args.existing_core.resolve() if args.existing_core else scratch / "core"
    consumer = (args.existing_consumer.resolve() if args.existing_consumer
                else scratch / "consumer")
    runner = Runner(repo, output, scratch, alias, core, consumer)
    m = runner.manifest
    try:
        require(runner.alias_mask != Path("/"), "unsafe configured alias parent")
        require(not alias.is_relative_to(repo) and not repo.is_relative_to(alias),
                "configured alias overlaps caller checkout")
        for path in (core, consumer):
            require(not path.is_relative_to(output) and not output.is_relative_to(path),
                    "output overlaps scratch tree")
            require(not path.is_relative_to(repo) and not repo.is_relative_to(path),
                    "scratch must not overlap caller checkout")
            if (path / ".git").exists():
                require((path / ".task25-scratch").is_file(),
                        "reuse refuses an unmarked checkout")
        require(core != consumer and not core.is_relative_to(consumer) and
                not consumer.is_relative_to(core), "overlapping scratch trees")
        revision = planned["simplifier"]
        runner.git_common = Path(runner.git("rev-parse", "--path-format=absolute",
                                 "--git-common-dir").decode().strip())
        m.update(simplifier_revision=revision, consumer_revision=CONSUMER,
                 simplifier_pin=MAIN, simplifier_is_pin=revision == MAIN,
                 simplifier_requested=args.simplifier_revision,
                 patch_sha256=planned["patch_sha256"],
                 patch_pin=PATCH_SHA256,
                 patch_pin_overridden=planned["patch_pin_overridden"],
                 alias_explicit="alias" in planned,
                 scratch_explicit="scratch" in planned,
                 jobs=args.jobs, skip_routine=args.skip_routine,
                 configured_alias=str(alias), core=str(core), consumer=str(consumer),
                 scope="prepare-only" if args.prepare_only else
                 "reused core; consumer execution" if args.existing_core else
                 "fresh core bootstrap + " +
                 ("" if args.skip_routine else "routine + ") +
                 "consumer execution",
                 python=sys.version,
                 python_executable={"path": sys.executable,
                                    **fingerprint(Path(sys.executable))},
                 alias_configuration=(
                     {"explicit_alias": str(alias)} if "alias" in planned else
                     {"path": str(config), **fingerprint(config)}),
                 platform=os.uname()._asdict()
                 if hasattr(os.uname(), "_asdict") else list(os.uname()))
        patch = output / "consumer.patch"
        patch.write_bytes(args.consumer_patch.read_bytes())
        m["consumer_patch"] = fingerprint(patch)
        canonical_core = scratch / "canonical-core"
        canonical = scratch / "canonical-consumer"
        main_sources = runner.archive(revision, canonical_core)
        list_original = main_sources[LIST]
        list_data = runner.git("show", CONSUMER + ":" + LIST)
        list_blob = runner.git("rev-parse",
                               CONSUMER + ":" + LIST).decode().strip()
        list_original_blob = runner.git("rev-parse",
                                        revision + ":" + LIST).decode().strip()
        (canonical_core / LIST).write_bytes(list_data)
        main_sources[LIST] = fingerprint(canonical_core / LIST)
        m["core_prerequisite"] = {"path": LIST, "revision": CONSUMER,
                                  "blob": list_blob,
                                  "simplifier_blob": list_original_blob,
                                  "main_original": list_original,
                                  **main_sources[LIST]}
        m["core_sources"] = runner.dump("core-sources.json.gz", main_sources)
        before = runner.archive(CONSUMER, canonical, ("src/auto", "help/Docfiles"))
        m["consumer_unpatched"] = runner.dump("consumer-unpatched.json.gz", before)
        # git apply is rooted in an isolated non-repository; --numstat exposes
        # every affected path. Do not permit patches to any other subtree.
        paths = runner.run("patch-paths", ["git", "apply", "--numstat", str(patch)],
                           cwd=canonical, scan=False)
        changed = [line.split("\t")[-1] for line in paths.splitlines()]
        require(changed and all((p.startswith("src/auto/") or
                                p.startswith("help/Docfiles/")) and
                               ".." not in PurePosixPath(p).parts and
                               not p.startswith('"') for p in changed),
                "patch escapes consumer prerequisite")
        runner.run("patch-check", ["git", "apply", "--check", str(patch)],
                   cwd=canonical)
        runner.run("patch-apply", ["git", "apply", str(patch)], cwd=canonical)
        consumer_sources = inventory(canonical)
        require(all("symlink" not in info or before.get(name) == info
                    for name, info in consumer_sources.items()),
                "patch introduces or changes a consumer symlink")
        m["consumer_canonical"] = runner.dump("consumer-canonical.json.gz",
                                               consumer_sources)
        numeric = {str(p.relative_to(canonical)) for p in
                   (canonical / "src/auto").rglob("*Script.sml")
                   if NUMERIC.search(p.read_bytes())}
        require(len(numeric) == 4, "numeric prerequisite is not four Scripts")
        if args.existing_core:
            verify(core, main_sources)
            verify_consumer(consumer, consumer_sources, numeric)
        else:
            canonical_core.rename(core)
            canonical_core = core
            shutil.copytree(canonical, consumer, symlinks=True)
            # Native sanity fixtures inspect Git provenance/baseline blobs.
            # This metadata belongs only to the disposable archive; objects
            # are read-only shared inputs, never caller-owned build products.
            (core / ".task25-scratch").write_text(revision + "\n")
            runner.run("core-git-init", ["git", "init", "-q", str(core)])
            (core / ".git/objects/info/alternates").write_text(
                str(runner.git_common / "objects") + "\n")
            runner.run("core-git-head", ["git", "-C", str(core),
                       "update-ref", "HEAD", revision])
            runner.run("core-git-index", ["git", "-C", str(core),
                       "reset", "--mixed", "-q", "HEAD"])
        if args.prepare_only:
            m["prepared"] = True
        else:
            for tool in ("bwrap", "poly", "polyc", "git", "g++", "ld", "polyimport",
                         "python3"):
                path = shutil.which(tool)
                require(path is not None, "missing tool: " + tool)
                m.setdefault("tools", {})[tool] = {"path": path,
                                                   **fingerprint(Path(path).resolve())}
            runner.inside("poly-version", ["poly", "-v"], scan=False)
            if not args.existing_core:
                runner.inside("configure", ["sh", "-c",
                               "exec poly < tools/smart-configure.sml"])
                check_configured_alias(core, alias)
                for label, command in build_commands(args.jobs,
                                                     args.skip_routine):
                    runner.inside(label, command,
                                  marker="Hol built successfully.")
            else:
                m["core_build_skipped"] = "explicit reuse; no fresh-build claim"
                check_configured_alias(core, alias)
            translated = runner.parser(canonical)
            verify(core, main_sources)
            verify_consumer(consumer, consumer_sources, translated)
            m["consumer_build_sources"] = runner.dump(
                "consumer-build-sources.json.gz",
                inventory_sources(consumer, consumer_sources))
            roots = runner.consumers()
            roots += runner.fixture()
            runner.closure(roots)
            m["core_runtime"] = {name: fingerprint(core / name) for name in
                                 ("bin/hol", "bin/Holmake", "bin/build",
                                  "bin/hol.state0", "bin/hol.state",
                                  "tools/Holmake/Systeml.sml")}
            runner.libraries("core-runtime-libraries", alias / "bin/Holmake")
            runner.libraries("hol-runtime-libraries", alias / "bin/hol")
            library_match = re.search(r'^val POLYMLLIBDIR = "([^"]+)"',
                                     (core / "tools/Holmake/Systeml.sml").read_text(),
                                     re.M)
            require(library_match is not None, "missing Poly/ML library location")
            library = Path(library_match[1]) / "libpolymain.a"
            m["runtime_libraries"][str(library)] = fingerprint(library)
            verify(core, main_sources)
            verify_consumer(consumer, consumer_sources, translated)
            for name, info in m["expansions"].items():
                require(fingerprint(consumer / name)["sha256"] ==
                        info["expanded_sha256"], "expanded source changed: " + name)
        m["success"] = True
    except BaseException as exc:
        m["failure"] = type(exc).__name__ + ": " + str(exc)
    finally:
        try:
            shutil.rmtree(scratch)
        except OSError as exc:
            m["success"] = False
            m["failure"] = "scratch cleanup failed: " + str(exc)
        m["task_scratch_removed"] = not scratch.exists()
        m["existing_scratch_preserved"] = bool(args.existing_core)
        runner.dump("manifest.json", m)
    print(output / "manifest.json")
    if not m["success"]:
        raise SystemExit(m["failure"])


def inventory_sources(root, sources):
    return {name: ({"symlink": os.readlink(root / name)} if (root / name).is_symlink()
                   else fingerprint(root / name)) for name in sources}


if __name__ == "__main__":
    main()
