#!/usr/bin/env python3
"""Offline TASK_13 structural correspondence; no HOL builds or timings."""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SRC = "src/simp/src/"
BASE = "cccaa27d7099cbadc886983020cbe745db7793f3"
START = "efae77781e40a0bd98775ae3d2bd670eaefdb7c0"
ORDINARY = ("Opening", "Travrules", "Traverse", "congLib")
PINNED = tuple(SRC + n + s for n in ORDINARY for s in (".sig", ".sml"))
EXTENSIONS = tuple(SRC + n + s for n in ("OpeningExt", "TravrulesExt")
                   for s in (".sig", ".sml"))
CALLERS = (SRC + "congExtLib.sml", SRC + "simpExtLib.sml",
           SRC + "simpLib.sml")
# Reviewed subsequent compiler/caller changes. Exact seals keep every mutation
# outside that reviewed delta fail-closed; historical TASK_13 evidence is not
# regenerated. TASK14.md describes the compiler and explicit getter migration.
TASK14_REVIEWED = {
    SRC + "simpExtLib.sml": {
        "bytes": 129620,
        "sha256": "b6dccd4025c0be1f2d380010ba9a5361c89348b9c39e49d9abcc1d62314ce0af"},
    SRC + "selftest.sml": {
        "bytes": 277199,
        "sha256": "ed0d9aecf994bcf8a66ac2b81fb078bce16edb27e1894df7409692f7e00fd103"},
}
OPENING_HEADER = """\
(* Explicit threaded congruence construction. The ordinary implementation in
   Opening is pinned develop. Shared relation helpers, Trace and HOL exception
   identities remain there/in the existing kernel; no registry is duplicated. *)
structure OpeningExt :> OpeningExt =
struct
open HolKernel boolLib liteLib Trace Opening;
type congproc = Opening.congproc

"""
OPENING_SIG = """\
(* Explicit opt-in to intermediate result discovery and rebuilt-RHS beta
   reduction. The continuation/type and exception identities are Opening's. *)
signature OpeningExt =
sig
  type congproc = Opening.congproc
  val THREADED_CONGPROC :
    ({Rinst : Term.term, arg : Term.term} -> Thm.thm) -> Thm.thm -> congproc
end
"""
TRAVRULES_SIG = """\
signature TravrulesExt =
sig
  type preorder = Travrules.preorder
  type travrules = Travrules.travrules
  val mk_threaded_travrules : preorder list -> Thm.thm list -> travrules
end
"""
TRAVRULES_BODY = """\
(* Threaded construction uses the original structural traversal/preorder
   types, relation lookup and eager map order; no second registry or control. *)
structure TravrulesExt :> TravrulesExt =
struct
  type preorder = Travrules.preorder
  type travrules = Travrules.travrules

  fun mk_threaded_travrules relns congs =
    let
      fun threaded_cong2proc th =
        let
          val r = Opening.rel_of_congrule th
          val Travrules.PREORDER(_,_,refl) = Travrules.find_relation r relns
        in
          OpeningExt.THREADED_CONGPROC refl th
        end
    in
      Travrules.TRAVRULES {relations=relns,
                          congprocs=map threaded_cong2proc congs,
                          weakenprocs=[]}
    end
end
"""
CONG_HEADER_OLD = """\
(* Typed configured caller closure extracted in TASK_10. Ordinary congLib
   restoration remains TASK_11. TASK_13 separates the shared congruence
   primitives; no preorder/exception/control identities are duplicated.
   Existing congLib diagnostic origins are intentionally preserved. *)"""
CONG_HEADER_NEW = """\
(* Explicit configured congruences use threaded OpeningExt construction.
   Ordinary congLib and its primitives remain pinned develop. Shared preorder,
   exception and control identities are not duplicated; existing congLib
   diagnostic origins are intentionally preserved. *)"""


def require(ok, message):
    if not ok:
        raise ValueError(message)


@lru_cache(maxsize=None)
def git_source(revision, path):
    return subprocess.check_output(
        ["git", "-C", str(REPO), "show", revision + ":" + path]).decode()


def between(text, start, stop):
    require(text.count(start) == 1 and text.count(stop) == 1,
            "missing/ambiguous source anchors: " + start)
    a, b = text.index(start), text.index(stop)
    require(a < b, "reversed source anchors")
    return text[a:b]


def replace_once(text, old, new):
    require(text.count(old) == 1, "missing/ambiguous replacement: " + old)
    return text.replace(old, new, 1)


def threaded_core():
    """Specialize the entire task-start mixed core, not selected tokens.

    Only the two constant-true branches, their boundary indentation, the
    constructor name, scan comment and beta guard change. All work stays.
    """
    old = git_source(START, SRC + "Opening.sml")
    core = between(old, "fun strip_n_imp", "\nval CONGPROC = gen_CONGPROC")
    changes = (
        ("fun gen_CONGPROC {threaded : bool}", "fun THREADED_CONGPROC"),
        ("Do not scan the rule at all for\n      ordinary congruences.",
         "This scan belongs only to explicit\n      threaded construction."),
        ("       if threaded then\n         let\n", "       let\n"),
        ("         end\n       else K false", "       end"),
        ("        if threaded then\n          let\n", "        let\n"),
        ("          end\n"
         "        (* Develop's result test: no whole-conclusion scan. *)\n"
         "        else fn v => op_mem aconv v rhs_genvars", "        end"),
        ("if threaded andalso may_leave_redex", "if may_leave_redex"))
    for before, after in changes:
        core = replace_once(core, before, after)
    require(not re.search(r"\bthreaded\b", core.replace(
        "threaded construction", "")), "unspecialized threaded switch")
    return core


@lru_cache(maxsize=1)
def native_paths():
    # Freeze the existing native suites and every pre-existing selftest.
    # New extension tests are deliberately not part of this historical set.
    paths = subprocess.check_output(
        ["git", "-C", str(REPO), "ls-tree", "-r", "--name-only", START,
         "--", "src/simp/src", "src/simp/tests"]).decode().splitlines()
    suites = ("contracts", "fresh-load", "markers", "replay-order",
              "split-persistence", "split-registration")
    return tuple(p for p in paths if p.endswith("/selftest.sml") or
                 (any(p.startswith("src/simp/tests/" + s + "/")
                      for s in suites) and
                  (p.endswith(".sml") or p.endswith("/Holmakefile"))))


def read_sources():
    return {p: (REPO / p).read_bytes().decode()
            for p in (*PINNED, *EXTENSIONS, *CALLERS, *native_paths())}


def seal(text):
    data = text.encode()
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def structural(sources=None):
    if sources is None:
        sources = read_sources()
    required = set((*PINNED, *EXTENSIONS, *CALLERS, *native_paths()))
    require(required <= sources.keys(), "missing audited sources")
    for path in PINNED:
        require(sources[path] == git_source(BASE, path),
                "pinned develop source changed: " + path)
        require(not re.search(r"\b\w*Ext\w*\b", sources[path]),
                "ordinary extension dependency: " + path)
    for path in native_paths():
        require(sources[path] == git_source(START, path) or
                seal(sources[path]) == TASK14_REVIEWED.get(path),
                "native/selftest changed outside reviewed delta: " + path)

    original = git_source(BASE, SRC + "Opening.sml")
    helper = between(original, "fun dest_binop", "\nfun is_congruence")
    expected = OPENING_HEADER + helper + "\n" + threaded_core() + "\nend\n"
    require(sources[SRC + "OpeningExt.sml"] == expected,
            "OpeningExt core/prefix differs from exact threaded extraction")
    require(sources[SRC + "OpeningExt.sig"] == OPENING_SIG,
            "OpeningExt signature/shared congproc identity changed")
    require(sources[SRC + "TravrulesExt.sml"] == TRAVRULES_BODY,
            "TravrulesExt aliases/lookup/map/threaded routing changed")
    require(sources[SRC + "TravrulesExt.sig"] == TRAVRULES_SIG,
            "TravrulesExt signature/shared type identities changed")
    # Exact prefixes/bodies above preclude shadow exceptions, controls,
    # registries or relation helpers. The sole ref is the original lazy
    # per-invocation conclusion-genvar cache in the extracted core.

    path = SRC + "congExtLib.sml"
    expected = replace_once(git_source(START, path),
                            CONG_HEADER_OLD, CONG_HEADER_NEW)
    for old in ("map (CONGPROC gen_refl) congs",
                "(CONGPROC (fn {Rinst,arg} => REFL arg)) thm"):
        expected = replace_once(expected, old, old.replace(
            "CONGPROC", "OpeningExt.THREADED_CONGPROC"))
    require(sources[path] == expected,
            "congExtLib must retain work/identities and two explicit "
            "threaded constructors")

    path = SRC + "simpExtLib.sml"
    expected = replace_once(
        git_source(START, path),
        "   Travrules.mk_threaded_travrules -> TravrulesExt in TASK_13.",
        "   Threaded construction uses TravrulesExt; structural types "
        "stay shared.")
    expected = replace_once(
        expected,
        "else mk_threaded_travrules relations threaded_congs::reltravs))",
        "else TravrulesExt.mk_threaded_travrules relations\n"
        "                                            "
        "threaded_congs::reltravs))")
    require(sources[path] == expected or
            seal(sources[path]) == TASK14_REVIEWED[path],
            "simpExtLib work/shared identities/explicit threaded call changed")
    # TASK_14 does not change the threaded factory/merge schedule itself.
    start = '     val rewrite_sources =\n       List.mapPartial'
    stop = '     SS {mk_rewrs = mk_rewrs, history = history'
    require(between(sources[path], start, stop) ==
            between(expected, start, stop),
            "TASK_14 changed threaded merge/factory schedule")
    # M3 is the one explicit temporary cooperation edge, owned by TASK_16.
    # Retargeting it must not change any ordinary mixed compiler work.
    path = SRC + "simpLib.sml"
    expected = replace_once(
        git_source(START, path),
        "else mk_threaded_travrules relations threaded_congs::reltravs))",
        "else TravrulesExt.mk_threaded_travrules relations\n"
        "                                            "
        "threaded_congs::reltravs))")
    require(sources[path] == expected,
            "simpLib temporary M3 route/work changed")
    return {p: seal(sources[p]) for p in sorted(required)}


def audit():
    return dict(structural="pass", baseline=BASE, task_start=START,
                sources=structural(),
                scope="source correspondence only; no build/timing claims")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    try:
        print(json.dumps(audit(), indent=2))
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as e:
        parser.exit(1, "TASK_13 audit failed: " + str(e) + "\n")


if __name__ == "__main__":
    main()
