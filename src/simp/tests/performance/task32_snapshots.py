#!/usr/bin/env python3
"""TASK32 independent snapshots: build, discard, verify and compare (v3).

  build    one snapshot (`--side base|cand`): `git clone --shared
           --no-checkout` of the repository into ROOT/<label>, detached at the
           pin, the sealed `mktool` fix on the baseline when asked, then
           smart-configure and `bin/build --no-cache -t -jN
           --seq=<task32.seq>`, under an `env -i`
           environment and a fresh HOME that are the same for both sides. The
           record of the side goes into the manifest (SCHEMA). A failed,
           interrupted (SIGTERM/SIGHUP) or otherwise incomplete build leaves
           an `incomplete` record that only `discard` removes.
  discard  moves a side's record into the manifest's `attempts` list and
           deletes its tree and HOME, so the side can be built again.
  verify   fail-closed audit of the manifest against the live trees: both
           pins, tree and input hashes, the sealed patch (blob-equal to the
           candidate's mktool.ML), the build sequence (same immutable file
           and digest on both sides, as built), the required workload
           products (REQUIRED_PRODUCTS), the compiled-source equality of the
           candidate with C31 (`--compiled-ref REV` names another
           revision, e.g. TASK37's final candidate), no stale products,
           every product seal and mtime inside the build interval, no
           shared inodes, identical argv/env, the toolchain (or only
           reported, `--toolchain report`), no nested roots.
  compare  the untimed behaviour comparison: every common untracked
           `*Theory.sig` and `*Theory.dat` and the normalized selftest logs
           of the two trees. Any unexplained difference makes the result
           `blocked`. A `.dat` whose bytes differ is compared by its
           canonical form (task32_dat.py: every table index resolved, every
           field kept); the only masked field is a parent's hash, and only
           for a parent theory that itself compared equal. A parse failure
           blocks.

Product set. After a build the products are every file `git status
--porcelain --ignored=matching --untracked-files=all` lists (directories
followed, so each file is sealed on its own), except what a Holmake run
rewrites without changing meaning: `.hol/locks` (process ids),
`.hol/build-logs` and the non-selftest `.hol/logs`. Everything else a theory
target writes is a product, and `theory_target_files(directory, name)`
lists those files: a timing driver that reruns a theory target imports it to
back them up before the run and to restore their bytes and mtimes
afterwards, after which `verify` passes again.
A seal is sha256, size and mtime (a symlink: its text and own mtime); the
inode is deliberately not recorded, so that a driver may restore a product by
copying its bytes and mtime back. Inodes are read live, only to show that no
file is shared between the sides or linked twice within one.

`clone --shared` borrows objects from the source repository through
alternates; they are recorded, and verify fails closed when one is gone.

The labels `base` and `cand` have the same length so that the HOLDIR strings
embedded in heaps and loaders do too. Nothing here edits the trees after the
build; verify and compare only read them. Audit commands run in a fixed
environment (no user git configuration).
"""
import argparse
from contextlib import contextmanager
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import acceptance as a
from performance_schema import require
import startup_gate as sg
import task32_cases as cases
import task32_dat as dat

SCHEMA = "task32-independent-build-v4"
BEHAVIOR_SCHEMA = "task32-behavior-v3"
LABELS = ("base", "cand")
PATH = "/usr/local/bin:/usr/bin:/bin"
POLY = "/usr/local/bin/poly"
# upto-parallel stops before src/parallel_builds/core, which builds integer,
# rational and real; task32.seq adds just those (and what they need), so
# that -t also runs their selftests. The file is passed by absolute path,
# the same for both sides, and its digest is recorded and verified.
# The harness copies the committed file once to an immutable
# <scratch>/task32-<sha256>.seq and builds with that path.
HARNESS_ROOT = HERE.parents[3]
SEQUENCE_REL = "src/simp/tests/performance/task32.seq"
SEQUENCE = str(HERE / "task32.seq")
CONFIGURE_INPUT = "tools/smart-configure.sml"
MKTOOL_PATH = sg.MKTOOL[0]
SYSTEML = "tools/Holmake/Systeml.sml"
C31 = "bdc4dac42d"
# Test-only paths: directories named `tests` under src/ are not uploaded to
# sigobj and lie in no heap or library closure.  Library Holmakefiles drive
# some of them through `-C tests/...`, but only as selftests under
# HOLSELFTESTLEVEL, so a change there cannot move the TASK31 measurements.
# Toolchain `tests` directories (tools/, tools-poly/) stay compared: TASK31's
# validity rule treats toolchain inputs as decisive.
TEST_ONLY = (":(exclude,glob)src/**/tests/**",)
BIN_PRODUCTS = ("bin/hol", "bin/hol.state0", "bin/hol.state",
                "bin/hol.state.min", "bin/Holmake")
STALE_NAMES = re.compile(r"(.*\.(uo|ui|dat)|hol\.state.*|\.hol)\Z")
AREAS = ("num", "integer", "rational", "real", "boss", "list", "pred_set")
# What the TASK32 workloads need from a build (design section 3); verify and
# compare require each one, so that a sequence that stops short cannot pass.
# S2's task32_cases must stay consistent with this list. ("theory", dir,
# name): <name>Theory's .dat among theory_target_files(dir, name); ("file",
# dir, name); ("log", dir, name): <dir>/.hol/logs/<name>, named by the
# `<x>-selftest.log` rule of the Holmakefile (`$(tee ./selftest.exe 2>&1,
# $@)`; observed for num/arith/reduce/boss, taken from the Holmakefiles for
# integer/testing, real and real/analysis).
REQUIRED_PRODUCTS = (
    ("theory", "src/rational", "rat"),
    ("theory", "src/integer", "integer"),
    ("theory", "src/integer", "integer_word"),
    ("theory", "src/real", "real"),
    ("theory", "src/real", "real_sigma"),
    ("theory", "src/real/analysis", "lim"),
    ("file", "src/real/analysis", "realheap"),
    ("theory", "src/num/theories", "arithmetic"),
    ("theory", "src/num/extra_theories", "logroot"),
    ("theory", "src/list/src", "rich_list"),
    ("theory", "src/pred_set/src", "pred_set"),
    ("log", "src/integer/testing", "integer2-selftest.log"),
    ("log", "src/real", "real-selftest.log"),
    ("log", "src/real/analysis", "real-selftest2.log"),
    ("log", "src/num/arith/src", "arith-selftest.log"),
    ("log", "src/num/reduce/src", "reduce-selftest.log"),
    ("log", "src/boss", "boss-selftest.log"))

PLACEHOLDER = "$(HOLDIR)"
ENV_KEYS = ("HOME", "LC_ALL", "PATH", "TERM", "TMPDIR", "TZ")
# After the build, each theory unit's own downstream command runs once in
# its directory (`prime`): see `check_prime`.
PRIME = "prime-"
# and once more (`reprime`): the second pass must change nothing, proving
# that the snapshot is a fixed point of those commands.
REPRIME = "reprime-"
COMMANDS = ["clone", "checkout", "configure", "build"] + [
    PRIME + u["name"] for u in cases.THEORY_UNITS] + [
    REPRIME + u["name"] for u in cases.THEORY_UNITS]
TIMEOUT = 6 * 3600
# Run-dependent text of the selftest and check logs (surveyed over the
# num, integer, real, boss, list and pred_set logs of a built tree):
# testutils.timed prints `[GC = 0.015] ` and `(0.003s)`; Holmake logs
# `Theory "x" took 1.4s to build`; cv_compute prints `runtime: ...s,
# gctime: ...s, systime: ...s.`; the banner holds the build date. Paths of
# the root are replaced by PLACEHOLDER first. Applied in this order (the
# tuple; NORMALIZERS keeps it). testutils right-aligns the status: it
# prints padding spaces, then as many `\x08` as the tail is long, then the
# tail. The count follows the tail, so a `[GC = ...] ` tag on one side only
# changes it. Pad and backspaces are presentation, replaced by one space
# before `gc-tag` removes the tag; the text left of the pad and the tail
# are still compared. A bare run of backspaces also becomes one space.
LOG_RULES = (
    ("ansi", r"\x1b\[[0-9;?]*[A-Za-z]", ""),
    ("pad-backspace", r" *\x08+", " "),
    ("gc-tag", r"\[GC = [0-9.]+\] ", ""),
    ("timing", r"\(\s*[0-9]+(\.[0-9]+)?\s*m?s\s*\)", "(<TIME>)"),
    ("theory-time", r"took [0-9.]+m?s to build", "took <TIME> to build"),
    ("cpu-times", r"\b(runtime|gctime|systime): +[0-9.]+s",
     r"\1: <TIME>"),
    ("banner-date", r"built [A-Z][a-z]{2} [A-Z][a-z]{2} +[0-9]+ "
     r"[0-9]{2}:[0-9]{2}:[0-9]{2} [0-9]{4}", "built <DATE>"))
assert len({name for name, _, _ in LOG_RULES}) == len(LOG_RULES)
NORMALIZERS = [(name, re.compile(pattern), repl)
               for name, pattern, repl in LOG_RULES]


class Terminated(BaseException):
    """SIGTERM or SIGHUP reached the builder."""


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


# The default TMPDIR of a snapshot build, per table of the timing and storage
# drivers (`build --table`): TASK37's streams run at the same time as the
# C32 gate's tooling, so each has a directory of its own, under the table's
# scratch (`task32_downstream.TABLES[...].scratch`; a test holds them
# equal). The C32 tables keep `/dev/shm/t32/tmp`.
TMPDIR = "/dev/shm/t32/tmp"
TABLE_TMPDIR = {"task32": TMPDIR, "task33": TMPDIR,
                "task37-t32": "/dev/shm/t37-t32/tmp",
                "task37-t33": "/dev/shm/t37-t33/tmp"}


def environment(home, tmpdir=TMPDIR):
    """The `env -i` environment: the same for both sides but for HOME."""
    return {"PATH": PATH, "HOME": str(home), "LC_ALL": "C", "TZ": "UTC",
            "TERM": "dumb", "TMPDIR": str(tmpdir)}


def audit_environment():
    """The environment of every audit command: no user git configuration
    and no inherited GIT_* variable."""
    return {"PATH": PATH, "HOME": "/nonexistent", "LC_ALL": "C",
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null"}


@contextmanager
def audit_process_environment():
    """os.environ replaced by the audit environment (for library code that
    runs git with the inherited one)."""
    saved = dict(os.environ)
    os.environ.clear()
    os.environ.update(audit_environment())
    try:
        yield
    finally:
        os.environ.clear()
        os.environ.update(saved)


def git_run(root, *args, check=True):
    return subprocess.run(["git", "-c", "color.ui=never", "-C", str(root),
                           *args], check=check, env=audit_environment(),
                          stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE)


def git_bytes(root, *args):
    return git_run(root, *args).stdout


def git(root, *args):
    return git_bytes(root, *args).decode().strip()


def input_hash(root):
    """sha256 of `git ls-files -s` and the working-tree patch."""
    return sha256_bytes(git_bytes(root, "ls-files", "-s") +
                        git_bytes(root, "diff", "--no-ext-diff"))


def patch_seal(root):
    data = git_bytes(root, "diff", "--no-ext-diff")
    return {"sha256": sha256_bytes(data), "bytes": len(data)}


def nested(first, second):
    first, second = Path(os.path.realpath(first)), \
        Path(os.path.realpath(second))
    return first == second or first.is_relative_to(second) or \
        second.is_relative_to(first)


def require_location(target, repo):
    """A snapshot may sit inside the repository only where git ignores it
    and tracks nothing; the repository may never sit inside it."""
    target, repo = Path(os.path.realpath(target)), \
        Path(os.path.realpath(repo))
    require(target != repo and not repo.is_relative_to(target),
            "snapshot nested with repository")
    if target.is_relative_to(repo):
        ignored = git_run(repo, "check-ignore", "-q", str(target),
                          check=False).returncode == 0
        tracked = git(repo, "ls-files", "--",
                      target.relative_to(repo).as_posix())
        require(ignored and not tracked, "snapshot nested with repository "
                "outside an ignored, untracked path")


# -- toolchain ---------------------------------------------------------

def _first_line(argv, env):
    try:
        p = subprocess.run(argv, env=env, stdin=subprocess.DEVNULL,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           text=True, timeout=60)
    except OSError as error:
        return "unavailable: %s" % error.strerror
    return p.stdout.strip().splitlines()[0] if p.stdout.strip() else ""


def parse_ldd(text):
    """{soname: resolved real path} of an `ldd` listing."""
    found = {}
    for line in text.splitlines():
        line = line.strip()
        if "=>" in line:
            name, rest = line.split("=>", 1)
            fields = rest.split()
            require(fields and fields[0] != "not", "unresolved library: " +
                    line)
            found[name.strip()] = os.path.realpath(fields[0])
        elif line.startswith("/"):
            path = line.split()[0]
            found[os.path.basename(path)] = os.path.realpath(path)
    return found


def parse_polyc_libdir(text):
    """The LIBDIR of a polyc script, with its ${prefix}-style variables
    expanded."""
    values = {}
    for line in text.splitlines():
        found = re.fullmatch(r'([A-Za-z_]+)="?([^"]*)"?', line.strip())
        if found:
            values.setdefault(found.group(1), found.group(2))
    value = values.get("LIBDIR")
    for _ in range(8):
        if value is None or "${" not in value:
            break
        value = re.sub(r"\$\{([A-Za-z_]+)\}",
                       lambda m: values.get(m.group(1), m.group(0)), value)
    return value if value and "${" not in value else None


def _libpolymain(polyc):
    libdir = parse_polyc_libdir(Path(polyc).read_text(errors="replace"))
    candidates = ([Path(libdir) / "libpolymain.a"] if libdir else [])
    candidates.append(Path(polyc).resolve().parent.parent / "lib" /
                      "libpolymain.a")
    for path in candidates:
        if path.is_file():
            return str(path.resolve())
    return None


def probe_toolchain(poly=POLY, env=None):
    """The toolchain record: versions and file hashes (every library `ldd`
    resolves for poly included)."""
    env = env if env is not None else environment("/nonexistent")
    poly = os.path.realpath(poly)
    polyc = os.path.realpath(str(Path(poly).with_name("polyc")))
    run = dict(env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
               stderr=subprocess.STDOUT, text=True, timeout=60)
    record = {"poly_v": subprocess.run([poly, "-v"], **run).stdout.strip(),
              "files": {}}
    libs = parse_ldd(subprocess.run(["ldd", poly], **run).stdout)
    files = {"poly": poly, "polyc": polyc,
             "libpolymain.a": _libpolymain(polyc)}
    files.update({"lib:" + k: v for k, v in libs.items()})
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


TOOLCHAIN_MODES = ("refuse", "report")


def toolchain_changes(recorded, live):
    """The sorted keys in which `live` differs from `recorded`: `poly_v`
    by `poly_version_matches`, every other key by equality."""
    changed = []
    if not a.poly_version_matches(recorded["poly_v"], live["poly_v"]):
        changed.append("poly_v")
    changed += [key for key in set(recorded) | set(live)
                if key != "poly_v" and recorded.get(key) != live.get(key)]
    return sorted(changed)


def same_toolchain(recorded, live):
    changed = toolchain_changes(recorded, live)
    if changed:
        require(changed[0] != "poly_v", "toolchain: poly -v changed")
        require(False, "toolchain changed: " + changed[0])


# -- running -----------------------------------------------------------

def run_command(argv, cwd, env, stdin, log, fds=()):
    """Run one command with exactly `env`, `stdin` (a path, else
    /dev/null) and its output in the new file `log`; returns its exit. On
    timeout or any interruption its process group is killed."""
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


def execute(runner, name, argv, cwd, env, stdin, logs, side, attempt):
    """One recorded command: the record holds everything the audit needs."""
    log = Path(logs) / ("%s-a%d-%s.log" % (side, attempt, name))
    start = time.time_ns()
    code = runner(argv, cwd, env, stdin, log)
    end = time.time_ns()
    return {"name": name, "argv": list(argv), "cwd": str(cwd),
            "env": dict(env),
            "stdin_hash": sha256_file(stdin) if stdin else
            sha256_bytes(b""),
            "start_ns": start, "end_ns": end, "exit": code,
            "log": str(log), "log_hash": a.seal(log)}


RAISE, DEFER, IGNORE = "raise", "defer", "ignore"


class SignalState:
    """The one signal discipline of the TASK32 tools (the same states as
    S3's compatibility driver). RAISE: a SIGTERM/SIGHUP raises Terminated,
    once (a burst of signals raises at most once). DEFER: it is only
    recorded, to be raised at the next `check` or at the end of the
    deferred block. IGNORE: it is dropped (the result is final).
    CPython runs a handler in the main thread whatever thread was signalled
    and at any bytecode boundary, so work that must complete (a restore, a
    group kill) runs in DEFER mode, with no mask to set or unset."""

    def __init__(self):
        self.mode = RAISE
        self.recorded = []
        self.reported = False  # a recorded signal was raised or noted

    def pending(self):
        return bool(self.recorded) and not self.reported


STATE = SignalState()


def on_signal(number, frame):
    name = signal.Signals(number).name
    if STATE.mode == IGNORE:
        return
    STATE.recorded.append(name)
    if STATE.mode == RAISE and not STATE.reported:
        STATE.mode, STATE.reported = DEFER, True
        raise Terminated(name)


def check():
    """Raise a signal that was only recorded (not yet raised or noted)."""
    if STATE.pending():
        STATE.mode, STATE.reported = DEFER, True
        raise Terminated(STATE.recorded[0])


def hold():
    """Enter DEFER for good (until the guard ends). The last statement of
    a `try` whose `finally` must complete, and of its `except` clauses: a
    signal before it raises inside the `try`, so the `finally` runs; after
    it a signal is only recorded, so none can cut the `finally` short."""
    if STATE.mode == RAISE:
        STATE.mode = DEFER


@contextmanager
def deferred(raise_pending=True):
    """Signals in this block are only recorded. At its end the mode is
    what it was (DEFER if a signal was raised meanwhile) and a recorded
    signal is raised, unless `raise_pending` is false (the caller `check`s
    where raising is safe). A block that ends with an exception keeps it as
    the primary error: a recorded signal is attached to it as a note."""
    previous = STATE.mode
    if previous == RAISE:
        STATE.mode = DEFER
    try:
        yield
    except BaseException as error:
        STATE.mode = DEFER if STATE.reported else previous
        if STATE.pending() and not isinstance(error, Terminated):
            error.add_note("also received %s while finishing" %
                           STATE.recorded[0])
            STATE.reported = True
        raise
    STATE.mode = DEFER if STATE.reported else previous
    if raise_pending:
        check()


@contextmanager
def raising():
    """The one place a blocking wait may be interrupted: a signal recorded
    so far is raised at entry, one that arrives inside raises. The mode
    after is DEFER if a signal was raised, else what it was."""
    previous = STATE.mode
    check()
    if previous == DEFER:
        STATE.mode = RAISE
    try:
        yield
    finally:
        STATE.mode = DEFER if STATE.reported else previous


@contextmanager
def terminating(mode=RAISE):
    """SIGTERM and SIGHUP are routed through STATE (unless ignored), so
    that the cleanup paths run and a running child's group is killed. A
    signal that was only recorded is raised when the block ends without an
    exception."""
    saved, outer = {}, (STATE.mode, STATE.recorded, STATE.reported)
    STATE.mode, STATE.recorded, STATE.reported = mode, [], False
    if threading.current_thread() is threading.main_thread():
        for number in (signal.SIGTERM, signal.SIGHUP):
            old = signal.getsignal(number)
            if old != signal.SIG_IGN:
                saved[number] = old
                signal.signal(number, on_signal)
    late = None
    try:
        yield
        if STATE.pending():
            late = STATE.recorded[0]
    finally:
        for number, old in saved.items():
            signal.signal(number, old)
        STATE.mode, STATE.recorded, STATE.reported = outer
    if late:
        raise Terminated(late)


# -- products ----------------------------------------------------------

def stale_products(root, tracked):
    """Untracked paths that look like products of an earlier build (this
    also finds the empty `.hol` directories git does not list)."""
    root, found = Path(root), []
    for folder, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d != ".git"]
        for name in list(dirs) + names:
            rel = (Path(folder) / name).relative_to(root).as_posix()
            if STALE_NAMES.match(name) and rel not in tracked:
                found.append(rel)
    return sorted(found)


def tracked_paths(root):
    out = git_bytes(root, "ls-files", "-z").decode(errors="surrogateescape")
    return {p for p in out.split("\0") if p}


def status_lines(root, *extra):
    out = git_bytes(root, "status", "--porcelain=v1",
                    "--untracked-files=all", *extra).decode()
    return [line for line in out.splitlines() if line]


def excluded(rel):
    """The `.hol` entries a Holmake run rewrites without a change of
    meaning: lock files (process ids), build logs and the logs that are not
    selftest logs."""
    parts = rel.split("/")
    for i, part in enumerate(parts[:-1]):
        if part != ".hol":
            continue
        if parts[i + 1] in ("locks", "build-logs"):
            return True
        if parts[i + 1] == "logs" and "selftest" not in parts[-1]:
            return True
    return False


def is_holmake_cache(rel):
    """True for a rel path that is Holmake's dependency cache: a file named
    `*.d` directly in a `.hol/make-deps` directory (the callers also
    require a regular file). On a second Holmake run
    in an already built directory Holmake writes such a file for the
    generated files of every theory there (`<X>Theory.sig.d`,
    `<X>Theory.sml.d`), which `bin/build` did not write consistently. They
    are derived from the sources and the sigobj. Only the path is judged
    here; the callers apply it to new regular files only, so a changed or
    vanished existing file is never a cache."""
    parts = rel.split("/")
    return parts[-1].endswith(".d") and parts[-3:-1] == [".hol",
                                                         "make-deps"]


THEORY_TARGET_TEMPLATES = (
    ".hol/objs/{n}Theory.sig", ".hol/objs/{n}Theory.sml",
    ".hol/objs/{n}Theory.dat", ".hol/objs/{n}Theory.ui",
    ".hol/objs/{n}Theory.uo", ".hol/objs/{n}Theory.cachekey",
    ".hol/docs/{n}Theory.html", ".hol/docs/{n}Script.html",
    ".hol/make-deps/{n}Theory.sig.d", ".hol/make-deps/{n}Theory.sml.d",
    ".hol/make-deps/{n}Script.sml.d")


def theory_target_files(directory, name):
    """The existing files (paths relative to `directory`) that building
    the theory target `<name>Theory` in `directory` writes. These are
    products: a driver backs them up and restores their bytes and mtimes.
    The lock and log files of the run are not products (see `excluded`)."""
    return [rel for rel in (t.format(n=name)
                            for t in THEORY_TARGET_TEMPLATES)
            if (Path(directory) / rel).exists()]


def listed_files(root):
    """Every untracked or ignored file git lists, directories followed."""
    out = git_bytes(root, "status", "--porcelain=v1", "-z",
                    "--untracked-files=all", "--ignored=matching")
    found = set()
    for entry in out.decode(errors="surrogateescape").split("\0"):
        if entry[:2] not in ("??", "!!"):
            continue
        path = entry[3:]
        if path.endswith("/"):
            for folder, _, names in os.walk(Path(root) / path):
                for name in names:
                    found.add((Path(folder) / name).relative_to(root)
                              .as_posix())
        else:
            found.add(path)
    return sorted(p for p in found if not excluded(p))


def seal_product(root, rel):
    path = Path(root) / rel
    st = path.lstat()
    if stat.S_ISLNK(st.st_mode):
        real = Path(os.path.realpath(path))
        require(real.is_relative_to(root), "product link leaves the root: "
                + rel)
        return {"kind": "link", "link": os.readlink(path),
                "mtime_ns": st.st_mtime_ns}
    require(stat.S_ISREG(st.st_mode), "product is not a file: " + rel)
    return {"kind": "file", "sha256": sha256_file(path),
            "bytes": st.st_size, "mtime_ns": st.st_mtime_ns}


def scan_products(root):
    """{relative path: seal} of every product (see the module docstring)."""
    root = Path(root).resolve(strict=True)
    found = {rel: seal_product(root, rel) for rel in listed_files(root)}
    for rel in BIN_PRODUCTS:
        require(rel in found, "missing product " + rel)
    return dict(sorted(found.items()))


def check_prime(before, after, label="prime"):
    """The prime commands changed no product: every product of `before` is
    sealed the same in `after`, and what is new is only Holmake's
    dependency cache (`is_holmake_cache`), which they exist to write: a
    second Holmake run in a built directory writes the `.d` files of the
    generated theory files, and `bin/build` did not write them
    consistently, so without priming every process of a unit would pay a
    dependency scan that the other arm's processes may not (the driver
    deletes the caches after each process). Returns the new rel paths."""
    changed = [r for r in before if after.get(r) != before[r]]
    stray = [r for r in after if r not in before and not (
        is_holmake_cache(r) and after[r]["kind"] == "file")]
    require(not changed and not stray,
            "the %s commands changed products: %s" % (label, ", ".join(
                (changed + stray)[:5])))
    return sorted(r for r in after if r not in before)


def inodes(root, products):
    """{path: (dev, ino)} of the regular-file products, read live."""
    result = {}
    for rel, seal in products.items():
        if seal["kind"] == "file":
            st = (Path(root) / rel).lstat()
            result[rel] = (st.st_dev, st.st_ino)
    return result


# -- build -------------------------------------------------------------

def real_runner(fds):
    return lambda argv, cwd, env, stdin, log: \
        run_command(argv, cwd, env, stdin, log, fds)


def require_schema(manifest):
    require(manifest.get("schema") == SCHEMA,
            "manifest schema is %r, not %s: an older manifest is "
            "superseded evidence and must be moved aside; use "
            "a fresh manifest and a fresh evidence directory"
            % (manifest.get("schema"), SCHEMA))


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


def systeml_hashes(root):
    data = (Path(root) / SYSTEML).read_bytes()
    return {"raw": sha256_bytes(data),
            "normalized": sha256_bytes(
                data.replace(str(root).encode(), b"<ROOT>"))}


def alternates(root):
    path = Path(root) / ".git/objects/info/alternates"
    return path.read_text().split() if path.exists() else []


def absolute(path):
    """`path` made absolute against the current directory (not resolving
    symlinks)."""
    return Path(os.path.abspath(path))


def build_side(repo, side, pin, root, manifest_path, logs, scratch, *,
               mktool=False, cand_pin=None, jobs=8, poly=POLY,
               tmpdir=TMPDIR, runner, probe=probe_toolchain,
               host=probe_host, harness=(HARNESS_ROOT, SEQUENCE_REL)):
    """Build one snapshot and record it. `runner(argv, cwd, env, stdin,
    log)` runs a command and returns its exit (a fake in the tests)."""
    require(side in LABELS, "side must be one of %s" % (LABELS,))
    require(len(LABELS[0]) == len(LABELS[1]), "labels differ in length")
    a.exact_pin(pin)
    # relative paths are resolved against the current directory, once: the
    # children run elsewhere (cwd = the root) and the record is absolute
    # root through symlinks too: smart-configure records the realpath HOLDIR
    repo, root = Path(repo).resolve(strict=True), Path(root).resolve()
    poly = os.path.abspath(poly) if os.sep in str(poly) else poly
    logs, scratch, tmpdir = absolute(logs), absolute(scratch), \
        str(absolute(tmpdir))
    manifest_path = absolute(manifest_path)
    target = root / side
    require(not os.path.lexists(target), "target exists (discard it "
            "first?): %s" % target)
    other = root / LABELS[1 - LABELS.index(side)]
    for path in (target, other):
        require_location(path, repo)
    require(not nested(target, other), "nested snapshot roots")
    for folder in (logs, scratch):
        require(not nested(folder, target) and not nested(folder, other),
                "evidence/scratch inside a snapshot root")
    manifest = load_manifest(manifest_path)
    require_schema(manifest)
    require(side not in manifest["sides"], "side already recorded "
            "(discard it first)")
    if mktool:
        a.exact_pin(cand_pin)
    attempt = len([x for x in manifest.get("attempts", [])
                   if x.get("label") == side])
    home = scratch / ("home-%s-a%d" % (side, attempt))
    require(not home.exists(), "HOME is not fresh: %s" % home)
    env = environment(home, tmpdir)
    record = {"label": side, "root": str(target), "home": str(home),
              "scratch": str(scratch), "repo": str(repo),
              "pin": pin, "mktool": mktool, "attempt": attempt,
              "cand_pin": cand_pin if mktool else None, "commands": []}

    def step(name, argv, cwd, stdin=None):
        entry = execute(runner, name, argv, cwd, env, stdin, logs, side,
                        attempt)
        record["commands"].append(entry)
        require(entry["exit"] == 0, "%s failed (exit %s)" %
                (name, entry["exit"]))

    with terminating():
        try:
            home.mkdir(parents=True)
            Path(tmpdir).mkdir(parents=True, exist_ok=True)
            logs.mkdir(parents=True, exist_ok=True)
            root.mkdir(parents=True, exist_ok=True)
            record["sequence"] = sequence_record(scratch, harness)
            step("clone", ["git", "clone", "--shared", "--no-checkout",
                           str(repo), str(target)], repo)
            record["alternates"] = alternates(target)
            step("checkout", ["git", "checkout", "--detach", pin], target)
            record["tree"] = git(target, "rev-parse", "HEAD^{tree}")
            record["patch"] = None
            if mktool:
                with audit_process_environment():
                    sealed = sg.apply_mktool(target)
                require(sealed["sha256"] == patch_seal(target)["sha256"],
                        "patch seal differs from the audit's")
                blob = git(target, "hash-object", MKTOOL_PATH)
                want = git(repo, "rev-parse",
                           "%s:%s" % (cand_pin, MKTOOL_PATH))
                require(blob == want, "patched mktool.ML is not "
                        "blob-equal to the candidate's")
                record["patch"] = dict(sealed, candidate_blob=want)
            record["status_before"] = status_lines(target)
            record["ignored_before"] = [
                line for line in status_lines(target, "--ignored=matching")
                if line.startswith("!!")]
            expected = [" M " + MKTOOL_PATH] if mktool else []
            require(record["status_before"] == expected,
                    "tree is not clean (or not exactly the sealed patch)")
            require(not record["ignored_before"],
                    "ignored files before build")
            record["stale_before"] = stale_products(target,
                                                    tracked_paths(target))
            require(not record["stale_before"],
                    "stale products before build")
            record["input_hash"] = input_hash(target)
            step("configure", [poly], target, target / CONFIGURE_INPUT)
            step("build", ["bin/build", "--no-cache", "-t", "-j%d" % jobs,
                           "--seq=" + record["sequence"]["path"]], target)
            built = scan_products(target)
            for unit in cases.THEORY_UNITS:
                step(PRIME + unit["name"],
                     cases.theory_argv(target, unit["theory"]),
                     target / unit["dir"])
            primed = scan_products(target)
            record["primed"] = check_prime(built, primed)
            for unit in cases.THEORY_UNITS:
                step(REPRIME + unit["name"],
                     cases.theory_argv(target, unit["theory"]),
                     target / unit["dir"])
            record["products"] = scan_products(target)
            require(check_prime(primed, record["products"], "reprime") == [],
                    "the snapshot is not a fixed point of the prime "
                    "commands: a second pass wrote files")
            record["build_interval_ns"] = [
                record["commands"][2]["start_ns"],
                record["commands"][-1]["end_ns"]]
            record["systeml"] = systeml_hashes(target)
            live = probe(poly, env)
            if "toolchain" in manifest:
                same_toolchain(manifest["toolchain"], live)
        except BaseException:
            manifest["sides"][side] = dict(record, incomplete=True)
            store_manifest(manifest_path, manifest)
            raise
    manifest.setdefault("toolchain", live)
    manifest.setdefault("host", host())
    manifest["sides"][side] = record
    store_manifest(manifest_path, manifest)
    return record


def objects_of(repo):
    """The object directory `git clone --shared` borrows from `repo`: that
    of its common git directory (a linked worktree's, too)."""
    common = git(repo, "rev-parse", "--git-common-dir")
    return os.path.realpath(os.path.join(repo, common, "objects"))


def discard_side(manifest_path, side, force=False):
    """Move a side's record into `attempts` and delete its tree and HOME.
    Only an `incomplete` record may be discarded unless `force`; the tree
    must be the clone that was recorded (its alternates equal) and the HOME
    one of the scratch directory's `home-<side>-a<n>`."""
    manifest = load_manifest(manifest_path)
    require(side in manifest["sides"], "no such side recorded")
    record = manifest["sides"][side]
    require(record.get("incomplete") or force, "the record is complete "
            "(use --force to discard it)")
    root, home = Path(record["root"]), Path(record["home"])
    require(root.name == side, "root is not named by its label")
    require(re.fullmatch(r"home-%s-a[0-9]+" % side, home.name) and
            str(home.parent) == record.get("scratch"),
            "HOME is not a scratch home of this side")
    if os.path.lexists(root):
        cloned = [c for c in record["commands"] if c["name"] == "clone"]
        if cloned and cloned[0]["exit"] == 0 and "alternates" in record:
            require((root / ".git").is_dir() and
                    alternates(root) == record["alternates"],
                    "root is not the recorded clone (alternates differ)")
        else:
            # a clone that did not finish: nothing, or a partial clone
            # that borrows objects from the source repository at most
            theirs = alternates(root)
            require(not (root / ".git").exists() or not theirs or
                    (record.get("repo") and all(
                        os.path.realpath(p) == objects_of(record["repo"])
                        for p in theirs)),
                    "root is not a partial clone of the repository")
    del manifest["sides"][side]
    manifest.setdefault("attempts", []).append(record)
    store_manifest(manifest_path, manifest)
    for path in (root, home):
        if os.path.lexists(path):
            shutil.rmtree(path)


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


def sequence_record(scratch, harness=(HARNESS_ROOT, SEQUENCE_REL)):
    """Copy the harness' committed sequence file once to an immutable
    `<scratch>/task32-<sha256>.seq` and describe it. An uncommitted or
    modified file is refused: its blob must be `HEAD:<rel>` of the harness
    repository."""
    repo, rel = Path(harness[0]), harness[1]
    source = repo / rel
    blob = git(repo, "hash-object", str(source))
    require(blob == git(repo, "rev-parse", "HEAD:" + rel),
            "sequence file differs from HEAD (commit it first): %s" % rel)
    data = source.read_bytes()
    digest = sha256_bytes(data)
    copy = Path(scratch).resolve() / ("task32-%s.seq" % digest)
    if copy.exists():
        require(copy.read_bytes() == data, "immutable sequence copy "
                "differs: %s" % copy)
    else:
        copy.write_bytes(data)
        copy.chmod(0o444)
    return {"path": str(copy), "sha256": digest, "content": data.decode(),
            "source": rel, "blob": blob,
            "harness_head": git(repo, "rev-parse", "HEAD")}


def check_sequence(record, label):
    seq = record.get("sequence")
    require(isinstance(seq, dict) and seq.get("path") and
            seq.get("sha256") and isinstance(seq.get("content"), str) and
            seq.get("source") and re.fullmatch("[0-9a-f]{40}",
                                               str(seq.get("blob"))) and
            re.fullmatch("[0-9a-f]{40}", str(seq.get("harness_head"))),
            "%s: no build sequence record" % label)
    require(Path(seq["path"]).is_absolute(),
            "%s: sequence path is not absolute" % label)
    require(sha256_bytes(seq["content"].encode()) == seq["sha256"],
            "%s: sequence content does not match its digest" % label)
    used = [x for x in record["commands"][3]["argv"]
            if x.startswith("--seq=")]
    require(used == ["--seq=" + seq["path"]],
            "%s: build did not use the recorded sequence" % label)
    return seq


def log_seal(path):
    """The seal of a log, kept as it is or compressed (`.gz`: the seal of
    the decompressed bytes)."""
    path = Path(path)
    if path.exists():
        return a.seal(path)
    packed = path.with_name(path.name + ".gz")
    require(packed.exists(), "log missing: %s" % path)
    data = gzip.decompress(packed.read_bytes())
    return {"sha256": sha256_bytes(data), "bytes": len(data)}


def check_primed(record, commands, products, label):
    """`primed` is a sorted, unique list of caches (regular files) among the
    products; every other product was written by the build (its mtime is
    not after the build command's end), every cache by the prime commands
    (not before the first one's start, not after the last one's end)."""
    primed = record["primed"]
    require(isinstance(primed, list) and primed == sorted(set(primed)) and
            set(primed) <= set(products) and
            all(is_holmake_cache(r) and products[r]["kind"] == "file"
                for r in primed), "%s: bad list of primed caches" % label)
    named = {c["name"]: c for c in commands}
    built = named["build"]["end_ns"]
    first = named[PRIME + cases.THEORY_UNITS[0]["name"]]["start_ns"]
    last = named[PRIME + cases.THEORY_UNITS[-1]["name"]]["end_ns"]
    for rel in primed:
        require(first <= products[rel]["mtime_ns"] <= last,
                "%s: primed cache outside the prime commands' window: %s"
                % (label, rel))
    for rel, seal in products.items():
        if rel not in primed:
            require(seal["mtime_ns"] <= built, "%s: product written after "
                    "the build: %s" % (label, rel))


def verify_side(record, label, expected_pin):
    require(record.get("label") == label and not record.get("incomplete"),
            "%s: incomplete or mislabelled record" % label)
    root = Path(record["root"])
    require(root.name == label, "%s: root is not named by its label" % label)
    root = root.resolve(strict=True)
    pin = record["pin"]
    a.exact_pin(pin)
    a.exact_pin(expected_pin)
    require(pin == expected_pin, "%s: recorded pin is not the expected one"
            % label)
    require(git(root, "rev-parse", "--show-toplevel") == str(root),
            "%s: not a worktree root" % label)
    require(git(root, "rev-parse", "HEAD") == pin,
            "%s: HEAD is not the pin" % label)
    require(git(root, "rev-parse", "HEAD^{tree}") == record["tree"],
            "%s: tree hash changed" % label)
    require(record["stale_before"] == [] and record["ignored_before"] == [],
            "%s: stale or ignored files before the build" % label)
    require(alternates(root) == record["alternates"] and
            all(Path(p).is_dir() for p in record["alternates"]),
            "%s: object alternates changed or gone" % label)
    live = patch_seal(root)
    if record["mktool"]:
        sealed = record["patch"]
        require(sealed is not None and record["status_before"] ==
                [" M " + MKTOOL_PATH], "%s: baseline is not patched" % label)
        require(live["sha256"] == sealed["sha256"] and
                live["bytes"] == sealed["bytes"],
                "%s: working tree differs from the sealed patch" % label)
        require(git(root, "diff", "--no-ext-diff", "--name-only") ==
                MKTOOL_PATH, "%s: patch touches other files" % label)
        require(git(root, "hash-object", MKTOOL_PATH) ==
                sealed["candidate_blob"], "%s: mktool blob differs from "
                "the candidate's" % label)
    else:
        require(record["patch"] is None and live["bytes"] == 0 and
                record["status_before"] == [],
                "%s: tree is dirty or patched" % label)
    require(not git(root, "diff", "--cached"), "%s: staged changes" % label)
    require(input_hash(root) == record["input_hash"],
            "%s: input hash changed" % label)
    commands = record["commands"]
    require([c["name"] for c in commands] == COMMANDS,
            "%s: unexpected command list" % label)
    for c in commands:
        require(c["exit"] == 0, "%s: %s exited %s" %
                (label, c["name"], c["exit"]))
        require(set(c["env"]) == set(ENV_KEYS), "%s: not an env -i "
                "environment" % label)
        require(not nested(Path(c["log"]).parent, root),
                "%s: log inside the root" % label)
        require(log_seal(c["log"]) == c["log_hash"], "%s: log changed"
                % label)
    for c, nxt in zip(commands, commands[1:] + [None]):
        require(c["start_ns"] <= c["end_ns"] and (
            nxt is None or c["end_ns"] <= nxt["start_ns"]),
            "%s: commands out of order at %s" % (label, c["name"]))
    first, last = record["build_interval_ns"]
    require(first == commands[2]["start_ns"] and
            last == commands[-1]["end_ns"] and first < last,
            "%s: bad build interval" % label)
    for c, unit in zip(commands[4:], 2 * cases.THEORY_UNITS):
        require(c["argv"] == cases.theory_argv(record["root"],
                                               unit["theory"]) and
                c["cwd"] == str(Path(record["root"]) / unit["dir"]),
                "%s: %s is not the unit's downstream command" %
                (label, c["name"]))
    products = scan_products(root)
    require(set(products) == set(record["products"]),
            "%s: product set changed" % label)
    for rel, now in products.items():
        require(now == record["products"][rel],
                "%s: product changed: %s" % (label, rel))
        require(first <= now["mtime_ns"] <= last,
                "%s: stale product (mtime outside the build): %s"
                % (label, rel))
    check_primed(record, commands, products, label)
    require(any(r.startswith("sigobj/") and r.endswith(".uo")
                for r in products), "%s: no sigobj products" % label)
    require(systeml_hashes(root) == record["systeml"],
            "%s: Systeml.sml changed" % label)
    lacking = missing_products(root)
    require(not lacking, "%s: required products missing: %s"
            % (label, ", ".join(lacking)))
    return products


def verify(manifest, base_pin, cand_pin, c31=C31, probe=probe_toolchain,
           poly=POLY, toolchain="refuse"):
    """Audit a manifest (a dict) against the live trees; raises on any
    failure and returns the summary otherwise. A live toolchain that
    differs from the recorded one is a failure under `toolchain`
    "refuse"; under "report" it is only listed in the summary."""
    require(toolchain in TOOLCHAIN_MODES, "unknown --toolchain mode")
    require_schema(manifest)
    sides = manifest.get("sides", {})
    require(set(sides) == set(LABELS), "both sides must be recorded")
    base, cand = sides["base"], sides["cand"]
    require(len(base["root"]) == len(cand["root"]),
            "HOLDIR strings differ in length")
    require(not nested(base["root"], cand["root"]), "nested snapshot roots")
    require(base["mktool"] is True and cand["mktool"] is False,
            "only the baseline carries the mktool patch")
    require(base.get("cand_pin") == cand["pin"],
            "baseline patch was made for another candidate")
    for label in LABELS:
        require(not nested(sides[label]["home"], sides[label]["root"]),
                "HOME inside the root")
    require(base["home"] != cand["home"], "shared HOME")
    products = {}
    for label, pin in zip(LABELS, (base_pin, cand_pin)):
        products[label] = verify_side(sides[label], label, pin)
    croot = Path(cand["root"])
    require(git(croot, "rev-parse", "HEAD:" + MKTOOL_PATH) ==
            base["patch"]["candidate_blob"],
            "sealed patch is not blob-equal to the candidate's mktool.ML")
    resolved = git_run(croot, "rev-parse", "--verify", c31 + "^{commit}",
                       check=False)
    require(resolved.returncode == 0, "cannot resolve " + c31)
    c31 = resolved.stdout.decode().strip()
    a.exact_pin(c31)
    same = git_run(croot, "diff", "--quiet", c31, cand["pin"], "--", ".",
                   *TEST_ONLY, check=False)
    require(same.returncode in (0, 1), "cannot compare with " + c31)
    require(same.returncode == 0, "candidate's compiled sources differ "
            "from %s" % c31)
    live = [inodes(sides[l]["root"], products[l]) for l in LABELS]
    for numbers in live:
        require(len(set(numbers.values())) == len(numbers),
                "a snapshot links a product twice")
    require(not (set(live[0].values()) & set(live[1].values())),
            "snapshots share inodes")
    bseq = check_sequence(base, "base")
    cseq = check_sequence(cand, "cand")
    same = ("path", "sha256", "content", "source", "blob")
    require([bseq[k] for k in same] == [cseq[k] for k in same],
            "build sequence differs between sides")
    require(Path(bseq["path"]).is_file() and
            sha256_file(bseq["path"]) == bseq["sha256"],
            "immutable sequence file changed or is gone")
    for x, y in zip(base["commands"], cand["commands"]):
        require(normalized_command(x, base, base["pin"]) ==
                normalized_command(y, cand, cand["pin"]),
                "argv/env differ between sides: " + x["name"])
    require(base["systeml"]["normalized"] == cand["systeml"]["normalized"],
            "configured Systeml.sml differs between sides")
    require(base["build_interval_ns"][1] <= cand["build_interval_ns"][0],
            "builds were not serial")
    live_toolchain = probe(poly, environment("/nonexistent"))
    if toolchain == "refuse":
        same_toolchain(manifest["toolchain"], live_toolchain)
        changed = []
    else:
        changed = toolchain_changes(manifest["toolchain"], live_toolchain)
    return {"schema": SCHEMA, "base_pin": base["pin"],
            "cand_pin": cand["pin"], "c31": c31,
            "base_products": len(products["base"]),
            "cand_products": len(products["cand"]), "status": "pass",
            "toolchain": {"status": "changed" if changed else "same",
                          "changed": changed}}


# -- compare -----------------------------------------------------------

def normalize_bytes(data, root):
    """`data` with every spelling of the root replaced by PLACEHOLDER."""
    for spelling in sorted({str(root), os.path.realpath(root)},
                           key=lambda x: (-len(x), x)):
        data = data.replace(spelling.encode(), PLACEHOLDER.encode())
    return data


def normalize_log(data, root):
    text = normalize_bytes(data, root).decode("latin-1")
    for _, pattern, repl in NORMALIZERS:
        text = pattern.sub(repl, text)
    return text


def untracked_files(root, wanted, tracked):
    found = {}
    for folder, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".git", "sigobj")]
        for name in names:
            path = Path(folder) / name
            rel = path.relative_to(root).as_posix()
            if wanted(rel, name) and rel not in tracked and \
                    not path.is_symlink():
                found[rel] = path
    return dict(sorted(found.items()))


def theory_files(root, tracked):
    return untracked_files(
        root, lambda rel, name: re.fullmatch(r".*Theory\.(sig|dat)", name)
        is not None, tracked)


def selftest_logs(root, tracked):
    """The sealed selftest logs of the areas (see `excluded`)."""
    def wanted(rel, name):
        parts = rel.split("/")
        return len(parts) > 2 and parts[0] == "src" and \
            parts[1] in AREAS and name.endswith(".log") and \
            "selftest" in name and not excluded(rel)
    return untracked_files(root, wanted, tracked)


def required_path(root, kind, directory, name):
    """The file a REQUIRED_PRODUCTS entry stands for, or None if absent."""
    folder = Path(root) / directory
    if kind == "theory":
        rel = ".hol/objs/%sTheory.dat" % name
        found = rel in theory_target_files(folder, name)
    else:
        rel = name if kind == "file" else ".hol/logs/" + name
        found = (folder / rel).is_file()
    return (directory + "/" + rel) if found else None


def missing_products(root):
    """The REQUIRED_PRODUCTS (as `kind dir/name`) that `root` lacks."""
    return ["%s %s/%s" % (kind, directory, name)
            for kind, directory, name in REQUIRED_PRODUCTS
            if required_path(root, kind, directory, name) is None]


def differ(kind, rel, paths, roots):
    """None when the (root-masked, for logs also time-masked) contents are
    equal, else the digests that differ."""
    x, y = (Path(p).read_bytes() for p in paths)
    if kind == "log":
        nx = normalize_log(x, roots[0]).encode("latin-1")
        ny = normalize_log(y, roots[1]).encode("latin-1")
    else:
        nx, ny = normalize_bytes(x, roots[0]), normalize_bytes(y, roots[1])
    if nx == ny:
        return None
    return {"path": rel, "base": sha256_bytes(nx), "cand": sha256_bytes(ny)}


def canonical_dats(pending, roots, byte_equal):
    """Compare the `.dat` files whose bytes differ by canonical form.
    `pending` maps a relative path to the two file paths, `byte_equal` is
    the set of relative paths that are equal byte for byte. A parent's hash
    is masked only for a theory (by file stem) all of whose files are
    equal. Returns the list of per-file records (equal or not)."""
    canon, records = {}, {}
    for rel, paths in pending.items():
        record = records[rel] = {"path": rel, "equal": False}
        try:
            canon[rel] = [
                dat.canonical(normalize_bytes(Path(p).read_bytes(), r)
                              .decode("latin-1"))
                for p, r in zip(paths, roots)]
            stem = Path(rel).name[:-len("Theory.dat")]
            if canon[rel][0]["name"] != stem or \
                    canon[rel][1]["name"] != stem:
                raise dat.Failure("theory name differs from its file")
        except dat.Failure as error:
            record["error"] = "parse failure: %s" % error
    stems = {}
    for rel in list(pending) + sorted(byte_equal):
        stems.setdefault(Path(rel).name[:-len("Theory.dat")],
                         []).append(rel)
    resolved = set(byte_equal)
    changed = True
    while changed:
        changed = False
        equal_names = {n for n, rels in stems.items()
                       if all(r in resolved for r in rels)}
        for rel in canon:
            if rel not in resolved:
                x, y = canon[rel]
                if dat.digest(x, equal_names)[0] == \
                        dat.digest(y, equal_names)[0]:
                    resolved.add(rel)
                    changed = True
    equal_names = {n for n, rels in stems.items()
                   if all(r in resolved for r in rels)}
    for rel, (x, y) in canon.items():
        (dx, masked), (dy, _) = (dat.digest(x, equal_names),
                                 dat.digest(y, equal_names))
        records[rel].update(base=dx, cand=dy, masked_parents=masked,
                            equal=rel in resolved,
                            fallback={"base": x["fallback"],
                                      "cand": y["fallback"]})
    return [records[rel] for rel in sorted(records)]


def compare(manifest, pins=None):
    """The behaviour record of two verified trees. `pins` (the summary of
    `verify`) is recorded in it."""
    base, cand = manifest["sides"]["base"], manifest["sides"]["cand"]
    roots = {"base": Path(base["root"]), "cand": Path(cand["root"])}
    tracked = {l: tracked_paths(roots[l]) for l in LABELS}
    blocked = []
    out = {"schema": BEHAVIOR_SCHEMA, "pins": pins}
    pending, byte_equal = {}, set()
    for kind, key, finder in (("theory", "theories", theory_files),
                              ("log", "logs", selftest_logs)):
        files = {l: finder(roots[l], tracked[l]) for l in LABELS}
        common = sorted(set(files["base"]) & set(files["cand"]))
        differing = []
        for rel in common:
            paths = (files["base"][rel], files["cand"][rel])
            found = differ(kind, rel, paths,
                           (roots["base"], roots["cand"]))
            if found is None:
                if rel.endswith(".dat"):
                    byte_equal.add(rel)
            elif kind == "theory" and rel.endswith(".dat"):
                pending[rel] = paths
            else:
                differing.append(found)
        base_only = sorted(set(files["base"]) - set(files["cand"]))
        out[key] = {
            "common": len(common), "differing": differing,
            "baseline_only": base_only,
            "candidate_only": sorted(set(files["cand"]) -
                                     set(files["base"]))}
        require(common, "no common %ss" % kind)
        if kind == "theory":
            records = canonical_dats(pending, (roots["base"],
                                               roots["cand"]), byte_equal)
            out["dat_canonical"] = {
                "module_sha256": sha256_file(Path(dat.__file__)),
                "mask": "a parent's hash, only for an equal parent theory",
                "files": records}
            differing += [{"path": r["path"], "base": r.get("base"),
                           "cand": r.get("cand"), "error": r.get("error")}
                          for r in records if not r["equal"]]
        blocked += [kind + " differs: " + d["path"] for d in differing]
        blocked += [kind + " missing on cand: " + p for p in base_only]
        if kind == "log":
            for area in AREAS:
                for label in LABELS:
                    if not any(p.startswith("src/%s/" % area)
                               for p in files[label]):
                        blocked.append("no selftest log under src/%s/ on %s"
                                       % (area, label))
    for label in LABELS:
        blocked += ["missing required product on %s: %s" % (label, m)
                    for m in missing_products(roots[label])]
        if manifest["sides"][label]["commands"][3]["exit"] != 0:
            blocked.append("%s build failed" % label)
    out["blocked"] = blocked
    out["status"] = "blocked" if blocked else "pass"
    out["normalization"] = {
        "root": PLACEHOLDER,
        "logs": [[n, p, r] for n, p, r in LOG_RULES],
        "dat": "byte-equal after root masking, else canonical form"}
    return out


# -- command line ------------------------------------------------------

def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="command", required=True)

    def common(parser):
        parser.add_argument("--repo", type=Path, default=HERE.parents[3])
        parser.add_argument("--manifest", type=Path, required=True)

    def pins(parser):
        parser.add_argument("--base-pin", required=True)
        parser.add_argument("--cand-pin", required=True)
        # the revision the candidate's compiled sources equal: C31 for
        # TASK32 and TASK33, the final candidate for TASK37
        parser.add_argument("--c31", "--compiled-ref", dest="c31",
                            default=C31)
        parser.add_argument("--poly", default=POLY)

    b = sub.add_parser("build")
    common(b)
    b.add_argument("--root", type=Path, required=True)
    b.add_argument("--evidence", type=Path, required=True)
    b.add_argument("--scratch", type=Path, required=True)
    b.add_argument("--side", choices=LABELS, required=True)
    b.add_argument("--pin", required=True)
    b.add_argument("--mktool", action="store_true")
    b.add_argument("--cand-pin")
    b.add_argument("--jobs", type=int, default=8)
    b.add_argument("--poly", default=POLY)
    b.add_argument("--table", choices=sorted(TABLE_TMPDIR),
                   default="task32", help="the table the snapshot is for: "
                   "the default --tmpdir is its own (TABLE_TMPDIR)")
    b.add_argument("--tmpdir", help="TMPDIR of the build (default: the "
                   "table's, /dev/shm/t32/tmp for task32)")
    d = sub.add_parser("discard")
    common(d)
    d.add_argument("--side", choices=LABELS, required=True)
    d.add_argument("--force", action="store_true")
    v = sub.add_parser("verify")
    common(v)
    pins(v)
    v.add_argument("--toolchain", choices=TOOLCHAIN_MODES,
                   default="refuse", help="a live toolchain that differs "
                   "from the recorded one is refused (default) or only "
                   "reported in the summary")
    c = sub.add_parser("compare")
    common(c)
    pins(c)
    c.add_argument("--output", type=Path, required=True)
    c.set_defaults(toolchain="refuse")
    args = p.parse_args(argv)
    with a.serial_lock(args.repo) as fds:
        if args.command == "build":
            build_side(args.repo, args.side, args.pin, args.root,
                       args.manifest, args.evidence, args.scratch,
                       mktool=args.mktool, cand_pin=args.cand_pin,
                       jobs=args.jobs, poly=args.poly,
                       tmpdir=args.tmpdir or TABLE_TMPDIR[args.table],
                       runner=real_runner(fds))
            return 0
        if args.command == "discard":
            discard_side(args.manifest, args.side, args.force)
            return 0
        manifest = json.loads(args.manifest.read_text())
        summary = verify(manifest, args.base_pin, args.cand_pin, args.c31,
                         probe=probe_toolchain, poly=args.poly,
                         toolchain=args.toolchain)
        if args.command == "verify":
            print(json.dumps(summary, indent=2))
            return 0
        result = compare(manifest, summary)
        with args.output.open("x") as stream:
            json.dump(result, stream, indent=2, sort_keys=True)
            stream.write("\n")
        print("compare:", result["status"])
        return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
