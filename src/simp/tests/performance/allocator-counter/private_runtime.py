"""Private patched Poly/ML runtime: source seal, build and process binding.

Shared by run_controls.py and the TASK29B matrix driver. Nothing here
installs or replaces a configured runtime; callers own the temporary tree.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import acceptance as a
import loading
import path_schema
from prepare_patch import transformations, sha256
from check_patch import replay, read_patch

# The build sequence of the HOL a toolchain compiles (bootstrap_probe), with
# no selftest level: `!` directories are not built.
HOL_SEQUENCE = "tools/sequences/upto-parallel"
CONFIGURE_ARGUMENTS = ("--without-x", "--disable-compact32bit",
                       "--enable-shared")
# The only tree area a harness commit may change relative to the reference.
PERFORMANCE_DIR = "src/simp/tests/performance/"
# Agent state by repository convention (acceptance.serial_lock keeps its
# lock here): the one top-level directory the cleanliness check ignores.
AGENT_STATE = ".agent-files"
# Files of the performance area (besides this directory) that the launchers
# import; a controls receipt seals them, and so must the matrix check them.
PERFORMANCE_INPUTS = ("acceptance.py", "loading.py", "worker_schema.py",
                      "interpreter_schema.py", "interpreter_branch_schema.py",
                      "failure_schema.py", "path_schema.py")
COUNTER_SYMBOLS = ("PolyManagedAllocSnapshotV1",
                   "PolyManagedInterpreterAllocSnapshotV1",
                   "PolyManagedAllocPathSnapshotV1")
# Exact undefined-import allowlists of the measurement shims, as linked on
# the supported AArch64 Linux host. A shim importing anything else (thread,
# process or other library functions) is rejected, not inspected by name.
SHIM_IMPORTS = frozenset(COUNTER_SYMBOLS) | frozenset({
    "_ITM_deregisterTMCloneTable", "_ITM_registerTMCloneTable",
    "__cxa_finalize", "__gmon_start__", "__stack_chk_fail",
    "__stack_chk_guard", "abort", "dladdr", "fputc", "fputs", "memcmp",
    "memcpy", "memset", "stderr"})
LIMIT_IMPORTS = frozenset({"close", "fwrite", "getrlimit", "open", "read",
                           "setrlimit", "sysconf"})


def harness_inputs():
    """Every harness file a controls receipt seals: all files of this
    directory and the shared modules the launchers import."""
    return sorted(p for p in HERE.iterdir() if p.is_file()) + [
        HERE.parent / name for name in PERFORMANCE_INPUTS]


def runtime_identity(text, library):
    rows = [line.split("\t", 1)[1] for line in text.splitlines()
            if line.startswith("@@TASK29_ALLOC_RUNTIME_V1\t")]
    a.require(len(rows) == 1 and
              Path(rows[0]).resolve(strict=True) ==
              library.resolve(strict=True),
              "snapshot symbol bound to wrong runtime")
    maps = [line.split("\t", 1)[1] for line in text.splitlines()
            if line.startswith("@@TASK29_ALLOC_MAP_V1\t")]
    paths = {line.split(maxsplit=5)[5] for line in maps
             if len(line.split(maxsplit=5)) == 6 and
             "libpolyml" in line.split(maxsplit=5)[5]}
    a.require(paths and all(Path(p).resolve(strict=True) ==
              library.resolve(strict=True) for p in paths),
              "control process has missing/multiple runtime mappings")
    return dict(symbol=rows[0], maps=maps)


def verify_source(source):
    seal = json.loads((HERE / "SOURCE_SHA256.json").read_text())
    entries = list(source.rglob("*"))
    paths = [p for p in entries if p.is_file()]
    a.require(not any(p.is_symlink() for p in entries), "source symlinks")
    a.require({p.relative_to(source).as_posix() for p in paths} ==
              set(seal["files"]), "source inventory mismatch")
    originals = {n: (source / n).read_bytes() for n in seal["files"]}
    a.require(all(sha256(raw) == seal["files"][n]
                  for n, raw in originals.items()), "source hash mismatch")
    canonical = "".join(f"{v}  {n}\n" for n, v in
                        sorted(seal["files"].items())).encode()
    a.require(sha256(canonical) == seal["tree_manifest_sha256"],
              "source manifest mismatch")
    patched = replay(read_patch(), originals)
    a.require(patched == transformations(originals),
              "patch reproduction failed")
    a.require({n: sha256(raw) for n, raw in patched.items()} == json.loads(
        (HERE / "PATCHED_SHA256.json").read_text()), "patched seal mismatch")
    return patched


def tree_outside_performance(repo, rev):
    """sha256 of the committed tree of rev outside the performance area."""
    listing = subprocess.run(
        ["git", "-C", str(repo), "ls-tree", "-r", "-z", rev],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
    entries = [e for e in listing.split(b"\0") if e]
    a.require(entries, "empty tree listing: " + rev)
    kept = []
    for entry in entries:
        meta, name = entry.split(b"\t", 1)
        if not name.decode().startswith(PERFORMANCE_DIR):
            kept.append(meta + b"\t" + name)
    a.require(kept and len(kept) < len(entries),
              "no performance area in the tree of " + rev)
    return hashlib.sha256(b"\0".join(kept)).hexdigest()


def harness_identity(repo, reference):
    """The checkout the controls run from, as a receipt record.

    It must be clean and committed, and differ from the reference revision
    only below the performance area: the HOL source that is built then is
    the reference's, and every harness file is sealed in the receipt. The
    top-level agent-state directory (the lock a fresh clone creates in it
    before this check) is not part of the checkout's content."""
    repo = Path(repo)
    head = a.git(repo, "rev-parse", "HEAD")
    dirty = a.git(repo, "status", "--porcelain", "--untracked-files=all",
                  "--", ":(top)", ":(top,exclude)" + AGENT_STATE)
    a.require(not dirty, "harness checkout is not clean: commit first")
    ref = a.git(repo, "rev-parse", reference + "^{commit}")
    tree = tree_outside_performance(repo, head)
    a.require(tree == tree_outside_performance(repo, ref),
              "harness differs from %s outside the performance area"
              % reference)
    return dict(head=head, dirty=False, reference=reference,
                reference_commit=ref, tree_outside_performance=tree)


# The one PATH of every process a driver starts, not the caller's. Drivers
# make it their own environment on entry (use_fixed_path), so what they run
# directly (git included) and what they pass an explicit environment to
# resolve tools in the same directories, and the sealed tools are the ones
# that ran.
PATH = "/usr/local/bin:/usr/bin:/bin"
BUILD_TOOLS = ("gcc", "g++", "make", "ldd", "nm", "ld", "as", "git")
# Compiler programs the driver runs on the caller's behalf: (driver, name).
COMPILER_PROGRAMS = (("gcc", "cc1"), ("g++", "cc1plus"), ("gcc", "collect2"))


def use_fixed_path():
    """First act of a driver entry point: from here on every subprocess,
    whether or not it is given an explicit environment, resolves its
    program on PATH."""
    os.environ["PATH"] = PATH


def seal_tools(env, run):
    """Seals of the build tools env["PATH"] resolves to, and of the compiler
    programs behind the drivers; run is the caller's recorded runner."""
    seals = {}
    for tool in BUILD_TOOLS:
        path = shutil.which(tool, path=env["PATH"])
        a.require(path is not None, "missing tool: " + tool)
        seals[path] = a.seal(path)
        run([path, "--version"])
    for compiler, program in COMPILER_PROGRAMS:
        path = run([compiler, "-print-prog-name=" + program])[
            "stdout"].strip()
        a.require(Path(path).is_file(), "compiler internal missing")
        seals[path] = a.seal(path)
    return seals


def counter_exports(symbols):
    """The runtime must export every counter snapshot function (text)."""
    a.require(isinstance(symbols, str), "malformed nm output")
    a.require(all(" T %s\n" % name in symbols for name in COUNTER_SYMBOLS),
              "counter symbols not exported")


def shim_imports(undefined, extended):
    """Undefined symbols of a shim (nm -D --undefined-only text), checked
    against the exact allowlist. Returns the sorted names."""
    a.require(isinstance(undefined, str), "malformed nm output")
    names = set()
    for line in undefined.splitlines():
        fields = line.split()
        if fields:
            a.require(len(fields) == 2 and fields[0] in ("U", "w", "v"),
                      "malformed shim import: " + line)
            names.add(fields[1].split("@")[0])
    allowed = SHIM_IMPORTS | (LIMIT_IMPORTS if extended else frozenset())
    a.require(set(COUNTER_SYMBOLS) <= names,
              "shim does not import the counter snapshots")
    unknown = sorted(names - allowed)
    a.require(not unknown,
              "shim imports outside the allowlist: " + " ".join(unknown))
    return sorted(names)


def check_transient(seals, scratch):
    """Seals of files below scratch: only valid while scratch exists."""
    scratch = Path(scratch)
    a.require(scratch.is_dir(), "temporary tree already deleted")
    transient = {k: v for k, v in seals.items()
                 if Path(k).is_relative_to(scratch)}
    loading.check_seals(transient)
    return transient


def check_persistent(seals, scratch):
    """Seals of every other input, rechecked AFTER scratch is deleted."""
    scratch = Path(scratch)
    a.require(not scratch.exists(), "temporary tree not deleted")
    loading.check_seals({k: v for k, v in seals.items()
                         if not Path(k).is_relative_to(scratch)})


def reject_compact32(config):
    """Snapshot words are eight bytes; compact32 is refused, never measured."""
    a.require("#define HOSTARCHITECTURE_AARCH64 1" in config, "wrong backend")
    path_schema.reject_compact32(config, CONFIGURE_ARGUMENTS)


def build_runtime(pristine, dst, run, report, patched):
    """Patched shared runtime built from a sealed copy of the pristine source.

    Returns (library, source tree, seals of the whole built tree)."""
    source = dst / "source"
    shutil.copytree(pristine, source)
    # Recheck the actual copy, not just the caller's inputs.
    a.require(verify_source(source) == patched, "copy changed")
    for name, raw in patched.items():
        (source / name).write_bytes(raw)
    source_seals = {str(p): a.seal(p) for p in source.rglob("*")
                    if p.is_file()}
    run([str(source / "configure"), *CONFIGURE_ARGUMENTS], source)
    report["config_log"] = (source / "config.log").read_text()
    report["configuration"] = (source / "config.h").read_text()
    reject_compact32(report["configuration"])
    report["build_inputs"] = {str(p.relative_to(source)):
        a.seal(p) for p in source.rglob("*") if p.is_file()}
    run(["make", "-C", "libpolyml", "-j2", "libpolyml.la"], source)
    lib = source / "libpolyml/.libs/libpolyml.so.16.0.0"
    report["runtime"] = a.seal(lib)
    counter_exports(run(["nm", "-D", str(lib)])["stdout"])
    return lib, source, source_seals


def bind_runtime(run, hol, lib, run_env, report):
    """ldd with the private DSO first: `hol` must resolve exactly that one."""
    libraries = loading.library_inputs(run(
        ["ldd", str(hol / "bin/hol")], runtime_env=run_env))
    matches = [(p, v) for p, v in libraries.items()
               if Path(p).name.startswith("libpolyml.so")]
    a.require(len(matches) == 1 and
              matches[0][1]["sha256"] == report["runtime"]["sha256"]
              and Path(matches[0][1]["resolved"]) == lib,
              "HOL not linked to private counter runtime")
    report["instrumented_libraries"] = libraries
    return libraries


def build_shim(env, run, fixture, lib, run_env, report, extended=False):
    """bracket.so linked against the very runtime HOL loads (no second DSO).

    extended adds failure_limit.c (the OS address-space limit). Whichever
    sources are used, the shim's undefined symbols must be exactly within
    the allowlist and it must link to the counter runtime."""
    sources = ["bracket.c"] + (["failure_limit.c"] if extended else [])
    for name in (*sources, "managed_alloc_counter.h"):
        shutil.copyfile(HERE / name, fixture / name)
    shim = fixture / "bracket.so"
    run([env["CC"], "-std=c11", "-shared", "-fPIC", "-O2", "-Wall",
         "-Wextra", "-Wl,-z,defs", *(str(fixture / n) for n in sources),
         str(lib), "-ldl", "-o", str(shim)])
    undefined = run(["nm", "-D", "--undefined-only", str(shim)])["stdout"]
    report["shim_undefined_symbols"] = undefined
    shim_imports(undefined, extended)
    libs = loading.library_inputs(run(["ldd", str(shim)],
                                      runtime_env=run_env))
    a.require(any(info["sha256"] == report["runtime"]["sha256"]
                  for info in libs.values()),
              "shim not linked to counter runtime")
    return shim, libs
