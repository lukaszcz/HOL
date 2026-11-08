#!/usr/bin/env python3
"""Who pays the compile-time words of a changed simpLib closure.

Counts, by static analysis of a built HOL tree, the executables of a build
sequence that run over hol.state0 and whose load closure contains simpLib
or congLib: such a process compiles the simplifier from source, so it pays
the load-simpLib delta of the startup gate once.  Counted per build mode:

  plain build   theory scripts and the `selftest.exe` that `all` links in
                every non-`!` directory, plus src/simp/src's own selftest
                and the numheap builds;
  added by -t   the same in the selftest-only (`!`) directories.

The closure is the real dependency closure: `holdeptool` on the source,
then the `.uo` dependency lists in sigobj, and for modules that live in
the directory itself (not in sigobj) `holdeptool` on their source.  A
module that cannot be resolved, or a `.uo` that is not readable (a
dangling link), is an error: the exit status is 2 and the modules are
listed on stderr.  Usage: who_pays.py HOLDIR [SEQUENCE]; one JSON line per
directory, then `SUMMARY` lines, on stdout."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

WATCHED = ("simpLib", "congLib")
FIRST = "src/simp/src"
LAST = "src/boss"


# Names that `holdeptool` reports but that are no module of sigobj: the
# Standard ML basis and compiler structures, and qualified names that are
# not build products (found by running the analysis on a built tree; every
# other unknown name is an error).
NOT_MODULES = frozenset("""
    Array Bool Char CharVector CompilerSpecific Definition General Int List
    ListPair OS Option PP Process String StringCvt TextIO UChar Unicode mg
    Word Word8 Vector Real Substring Time Timer Date IO Text
    """.split())


class Unresolved(Exception):
    pass


def expand(hol, name):
    out = []
    for line in (hol / "tools/sequences" / name).read_text().splitlines():
        line = line.strip()
        if line.startswith("#include"):
            out += expand(hol, line.split("/")[1].strip())
        elif line and not line.startswith("#"):
            out.append(line)
    return out


def directories(hol, sequence):
    """(directory, selftest-only) of the poly build, in order."""
    out = []
    for line in expand(hol, sequence):
        if (line.startswith("[mosml]") or "**" in line or
                any(k in line for k in ("(otknl)", "(expk)", "(trknl)"))):
            continue
        line = re.sub(r"^\[poly\]|^\(stdknl\)", "", line)
        bang = line.startswith("!")
        out.append((line.lstrip("!"), bang))
    return out


def heap_of(d):
    hm = d / "Holmakefile"
    if hm.exists():
        found = re.findall(r"^\s*HOLHEAP\s*=\s*(\S+)", hm.read_text(), re.M)
        if found:
            return found[-1]
    return None


class Closure:
    def __init__(self, hol):
        self.hol = hol
        self.cache = {}
        self.problems = []

    def holdep(self, d, fname):
        r = subprocess.run([str(self.hol / "bin/holdeptool.exe"), fname],
                           cwd=d, capture_output=True, text=True,
                           stdin=subprocess.DEVNULL)
        if r.returncode != 0:
            raise Unresolved("holdeptool failed on %s/%s" % (d, fname))
        return [x for x in r.stdout.split() if x]

    def sigobj_deps(self, mod):
        """Direct dependencies of a module of sigobj, None when it has no
        .uo/.ui there; an error when the link is dangling."""
        for ext in (".uo", ".ui"):
            f = self.hol / "sigobj" / (mod + ext)
            if f.is_symlink() and not f.exists():
                raise Unresolved("dangling sigobj link %s" % f)
            if f.exists():
                if ext == ".ui":
                    return []
                return [os.path.basename(l.strip())
                        for l in f.read_text().splitlines()
                        if l.strip() and not l.strip().endswith(
                            (".sml", ".sig"))]
        return None

    @staticmethod
    def local_source(d, mod):
        for name in (mod + ".sml", mod + ".sig"):
            if (d / name).exists():
                return name
        if mod.endswith("Theory") and (d / (mod[:-6] + "Script.sml")).exists():
            return mod[:-6] + "Script.sml"
        return None

    def of(self, d, fname):
        """The set of module names a source file depends on."""
        seen, stack = set(), self.holdep(d, fname)
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            if m in NOT_MODULES and self.sigobj_deps(m) is None:
                continue
            try:
                deps = self.sigobj_deps(m)
                if deps is None:
                    src = self.local_source(d, m)
                    if src is None:
                        raise Unresolved("module %s (needed from %s/%s) is "
                                         "neither in sigobj nor local" % (
                                             m, d, fname))
                    deps = self.holdep(d, src)
                stack += deps
            except Unresolved as e:
                self.problems.append(str(e))
        return seen


def analyse(hol, sequence="upto-parallel"):
    """(per-directory entries, summary, problems)."""
    hol = Path(hol)
    closure = Closure(hol)
    entries, started = [], False
    for rel, bang in directories(hol, sequence):
        if rel == FIRST:
            started = True
        if not started:
            continue
        d = hol / rel
        heap = heap_of(d)
        hm = d / "Holmakefile"
        ent = dict(dir=rel, bang=bang, heap=heap,
                   builds_heap=hm.exists() and "buildheap" in hm.read_text(),
                   scripts=[], selftest=False,
                   simpLib=[], congLib=[])
        files = sorted(d.glob("*Script.sml")) + sorted(
            d.glob("selftest.sml"))
        if rel == FIRST:
            files = [f for f in files if f.name == "selftest.sml"]
        for f in files:
            name = f.name[:-4]
            mods = closure.of(d, f.name)
            if name == "selftest":
                ent["selftest"] = True
            else:
                ent["scripts"].append(name)
            for w in WATCHED:
                if w in mods:
                    ent[w].append(name)
        entries.append(ent)
        if rel == LAST:
            break
    return entries, summary(entries), sorted(set(closure.problems))


def summary(entries):
    """Counts of processes over hol.state0 whose closure holds simpLib."""
    s = dict(plain_scripts=0, plain_selftest_links=0, simp_src_selftest=0,
             numheap_builds=0, tflag_scripts=0, tflag_selftest_links=0,
             congLib_payers=0, unpinned_payers=[])
    for e in entries:
        if e["heap"] == "numheap" and e["builds_heap"]:
            s["numheap_builds"] += 1
        pays = e["heap"] is not None and e["heap"].endswith("hol.state0")
        if e["simpLib"] and e["heap"] is None and e["dir"] != FIRST:
            s["unpinned_payers"].append(e["dir"])
        if not pays:
            continue
        scripts = [n for n in e["simpLib"] if n != "selftest"]
        link = "selftest" in e["simpLib"]
        if e["congLib"]:
            s["congLib_payers"] += len(e["congLib"])
        if e["dir"] == FIRST:
            s["simp_src_selftest"] += int(link)
        elif e["bang"]:
            s["tflag_scripts"] += len(scripts)
            s["tflag_selftest_links"] += int(link)
        else:
            s["plain_scripts"] += len(scripts)
            s["plain_selftest_links"] += int(link)
    s["plain_total"] = (s["plain_scripts"] + s["plain_selftest_links"] +
                        s["simp_src_selftest"] + s["numheap_builds"])
    s["with_t_total"] = (s["plain_total"] + s["tflag_scripts"] +
                         s["tflag_selftest_links"])
    return s


def main(argv):
    hol = Path(argv[1])
    entries, s, problems = analyse(hol, argv[2] if len(argv) > 2 else
                                   "upto-parallel")
    for e in entries:
        print(json.dumps(e))
    for k, v in s.items():
        print("SUMMARY\t%s\t%s" % (k, v))
    print("SUMMARY\tnote\tnumheap builds are counted, not traced; the "
          "candidate's own test executables in src/simp/src are not counted")
    for p in problems:
        print("UNRESOLVED " + p, file=sys.stderr)
    return 2 if problems or s["unpinned_payers"] else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
