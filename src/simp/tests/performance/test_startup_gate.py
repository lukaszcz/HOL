#!/usr/bin/env python3
"""TASK31 startup gate: protocol, decision rule and build recipe.

Synthetic fixtures only: no runtime, toolchain or HOL tree is needed. Every
guard of the decision rule is killed by a case below.
"""
import hashlib
import json
import os
from unittest import mock
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import allocation_schema as sc
import startup_gate as g

HERE = Path(__file__).resolve().parent
LIB = "/synthetic/libpolyml.so.16"
HOLDIR = "/synthetic/b1/hol-source"
MODULES = ["Array", "bossLib", "boolLib"]
FILES = ["bossLib.sml", "boolLib.sml"]
STRUCTS = ["bossLib", "boolLib", "simpLib"]


def snap(total=100, native=90, rts=8, interp=0, code=2, abi=1, over=0):
    return [abi, 8, over, total, native, rts, interp, code]


def stdout(kind="hol-startup", brackets=None, loaded=MODULES, files=FILES,
           structs=STRUCTS, holdir=HOLDIR, foreign="0,0", result="none",
           end=True, lib=LIB, live="auto"):
    brackets = brackets or [("startup", snap(), snap()),
                            ("empty", snap(), snap(104, 94))]
    lines = []
    for name, s, e in brackets:
        lines.append("\t".join(["@@GATE", kind, "alloc", name,
                                ",".join(map(str, s)) + ";" +
                                ",".join(map(str, e))]))
    rows = [("holdir", "path", holdir), ("foreign", "path", foreign),
            ("result", "none" if result == "none" else "ok",
             "-" if result == "none" else result),
            ("loaded", "count", str(len(loaded))),
            ("loaded", "modules", ",".join(loaded)),
            ("files", "count", str(len(files))),
            ("files", "names", ",".join(files)),
            ("structures", "count", str(len(structs))),
            ("structures", "names", ",".join(structs))]
    if live == "auto":
        live = ("3145728,2071000,1048576,1048576"
                if kind.startswith("load-") else None)
    if live:
        rows.append(("live", "heap", live))
    for event, name, payload in rows:
        lines.append("\t".join(["@@GATE", kind, event, name, payload]))
    lines.append("@@TASK29_ALLOC_RUNTIME_V1\t" + lib)
    lines.append("@@TASK29_ALLOC_MAP_V1\t0-1 r-xp 0 00:00 1 " + lib)
    if end:
        lines.append("@@GATE\tend")
    return "\n".join(lines) + "\n"


def parse(**kw):
    kind = kw.get("kind", "hol-startup")
    return g.parse_process(stdout(**kw), kind, HOLDIR, LIB, ())


class LiveReadingTest(unittest.TestCase):
    def test_load_kinds_carry_the_reading_in_words(self):
        rec = parse(kind="load-simpLib")
        self.assertEqual(rec["live"], dict(
            size_heap=3145728, free_last_gc=2071000, alloc_area=1048576,
            words=(3145728 - 2071000 - 1048576) // 8))

    def test_missing_unexpected_or_odd_readings_are_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "live heap"):
            parse(kind="load-simpLib", live=None)
        with self.assertRaisesRegex(sc.InvalidAllocation, "live heap"):
            parse(kind="hol-startup", live="3145728,2071000,1048576,1048576")
        for bad in ("3145728,2071000,1048577,1048577",
                    "100,2071000,1048576,1048576",
                    "3145728,2071000,0,0",
                    # a surviving allocation space: its free part is
                    # smaller than the whole
                    "3145728,2071000,1048576,524288",
                    "3145728,2071000,1048576,2097152"):
            with self.assertRaisesRegex(sc.InvalidAllocation, "live heap"):
                parse(kind="load-simpLib", live=bad)

    def test_a_reading_without_the_free_allocation_figure_is_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "malformed"):
            parse(kind="load-simpLib", live="3145728,2071000,1048576")

    def test_report_is_candidate_minus_baseline_per_image(self):
        def rec(image, variant, words, area=1048576):
            return dict(kind="load-simpLib", image=image, variant=variant,
                        live=dict(words=words, alloc_area=area))
        records = [rec("b1", "base", 1000), rec("b1", "base", 1010),
                   rec("b1", "candidate", 1100), rec("b1", "candidate", 1100),
                   rec("s1", "base", 2000), rec("s1", "candidate", 2090,
                                                2097152)]
        got = g.live_report(records)["load-simpLib"]
        self.assertEqual(got["b1"], dict(
            base=[1000, 1010], candidate=[1100], alloc_area=[1048576],
            comparable=True, runs=[2, 2], delta_min=100, delta_max=90))
        self.assertEqual(got["s1"]["alloc_area"], [1048576, 2097152])
        self.assertFalse(got["s1"]["comparable"])
        self.assertEqual(got["s1"]["delta_min"], 90)
        one = g.live_report([rec("b1", "base", 1000),
                             rec("b1", "base", 1000, 2097152),
                             rec("b1", "candidate", 1100)])["load-simpLib"]
        self.assertFalse(one["b1"]["comparable"])   # one variant, two sizes
        self.assertEqual(g.live_report([dict(kind="hol-startup")]), {})

    def test_results_show_the_figure_and_its_units(self):
        records, _ = attributed_world()
        report = run(records)
        report["live"] = {"load-simpLib": {"b1": dict(delta_min=5)}}
        text = g.render(report, {})
        self.assertIn("load-simpLib b1", text)
        self.assertIn("/ 8", text)
        self.assertIn("bytes", text)
        self.assertIn("exclude compiled code", text)


class ParseTest(unittest.TestCase):
    def test_valid(self):
        record = parse()
        self.assertEqual(record["loaded"], MODULES)
        self.assertEqual(g.bracket_fields(record["brackets"][0])["total"],
                         100)
        self.assertEqual(g.bracket_fields(record["brackets"][1])["total"], 4)

    def rejects(self, message, **kw):
        with self.assertRaisesRegex(sc.InvalidAllocation, message):
            parse(**kw)

    def test_guards(self):
        self.rejects("did not finish", end=False)
        self.rejects("wrong HOLDIR", holdir="/other/hol-source")
        self.rejects("foreign-thread", foreign="1,0")
        self.rejects("ABI", brackets=[
            ("startup", snap(abi=2), snap()), ("empty", snap(), snap())])
        self.rejects("overflow", brackets=[
            ("startup", snap(), snap()), ("empty", snap(), snap(over=1))])
        self.rejects("first brackets", brackets=[
            ("empty", snap(), snap()), ("startup", snap(), snap())])
        self.rejects("wrong runtime|snapshot symbol", lib="/other/lib.so")
        self.rejects("malformed counter", brackets=[
            ("startup", snap(), snap()), ("empty", [1, 2], snap())])

    def test_count_mismatch(self):
        text = stdout().replace("\tloaded\tcount\t3", "\tloaded\tcount\t4")
        with self.assertRaisesRegex(sc.InvalidAllocation, "count mismatch"):
            g.parse_process(text, "hol-startup", HOLDIR, LIB, ())


PATHS = {n: "src/simp/src/%s" % n for n in (
    "A.sml", "Cond_rewr.sig", "Cond_rewr.sml", "simpLib.sml", "congLib.sml",
    "Other.sml", "Trace.sml")}
BR = {n: "$(HOLDIR)/" + p for n, p in PATHS.items()}
BLOB = {"Cond_rewr.sig": ("1" * 40, "2" * 40),
        "Cond_rewr.sml": ("3" * 40,) * 2,
        "simpLib.sml": ("4" * 40,) * 2, "congLib.sml": ("5" * 40,) * 2,
        "Trace.sml": ("6" * 40,) * 2}
SOURCES = {"base": {PATHS[n]: b[0] for n, b in BLOB.items()},
           "candidate": {PATHS[n]: b[1] for n, b in BLOB.items()}}
# Words of each source file with the baseline sources.
FILE_WORDS = {"A.sml": 400, "Cond_rewr.sig": 5, "Cond_rewr.sml": 60,
              "simpLib.sml": 90, "Other.sml": 6, "Trace.sml": 3000,
              "congLib.sml": 70}
LOAD_FILES = {"files-simpLib": ("A.sml", "Cond_rewr.sig", "Cond_rewr.sml",
                                "simpLib.sml", "Other.sml", "Trace.sml"),
              "files-congLib": ("A.sml", "Cond_rewr.sig", "Cond_rewr.sml",
                                "simpLib.sml", "Other.sml", "Trace.sml",
                                "congLib.sml")}
GAPS = {"load-simpLib": 11, "load-congLib": 13}
BASE = ("b1", "b2")
CAND = ("s1", "s2")
SIDES = dict(base=list(BASE), candidate=list(CAND))
TEST_PAIRS = 2


def brec(kind, image, variant, pair, words, loaded=MODULES, structs=STRUCTS,
         files=FILES):
    """A process record whose named brackets hold the given words."""
    rows = [("startup", snap(), snap()), ("empty", snap(), snap(104, 94))]
    rows += [(n, words_(0), words_(w)) for n, w in words.items()]
    brackets = [dict(name=n, start=s, end=e) for n, s, e in rows]
    return dict(kind=kind, brackets=brackets, loaded=list(loaded),
                files=list(files) if pair == 0 else None,
                structures=list(structs), result="true" if kind in
                g.USES_SIMP else "none", files_sha=g.sha(list(files)),
                image=image, variant=variant, pair=pair)


def words_(n):
    return snap(n, n, 0, 0, 0)


def world(delta=None, noise=None, gap_delta=None, post=None, startup=None,
          first_use=None, kinds=None, base=BASE, cand=CAND, pairs=TEST_PAIRS,
          extra=None):
    """Records of a whole run. delta: file -> extra words of the candidate
    sources; noise: {image: {file: words}} on every variant of an image;
    gap_delta: {kind: words} loader words of the candidate sources; post:
    words of the post-load SIMP bracket of the candidate; startup /
    first_use: {image: words} on the image kinds; extra: {(kind, image,
    variant): {field: value}} overrides applied to a record."""
    delta, noise = delta or {}, noise or {}
    kinds = kinds or list(g.KINDS)
    out = []
    for kind in kinds:
        for image in base + cand:
            for variant in g.variants_of(kind):
                cand_v = variant == "candidate"
                fw = {}
                for f in LOAD_FILES["files-congLib"]:
                    fw[f] = (FILE_WORDS[f] + noise.get(image, {}).get(f, 0) +
                             (delta.get(f, 0) if cand_v else 0))
                if kind in g.FILES_KINDS:
                    br = {BR[f]: fw[f] for f in LOAD_FILES[kind]}
                elif kind in g.LOADS:
                    fk, lb = g.LOADS[kind]
                    total = sum(fw[f] for f in LOAD_FILES[fk]) + \
                        GAPS[kind] + (gap_delta or {}).get(kind, 0) * cand_v
                    br = {lb[0]: total}
                    for extra_bracket in lb[1:]:
                        br[extra_bracket] = 0
                    if kind == "load-simpLib":
                        br["SIMP_CONV_1"] = 500 + (post or 0) * cand_v
                        br["SIMP_TAC_1"] = 700
                elif kind == "hol-first-use":
                    br = {"SIMP_CONV_1": 500 + (first_use or {}).get(image, 0),
                          "SIMP_TAC_1": 700}
                else:
                    br = {}
                for pair in range(pairs):
                    r = brec(kind, image, variant, pair, br)
                    if kind == "hol-startup":
                        r["brackets"][0]["start"][3] += (startup or {}).get(
                            image, 0)
                    for field, value in (extra or {}).get(
                            (kind, image, variant), {}).items():
                        r[field] = value
                    out.append(r)
    return out


def bump(records, kind, image, variant, name, words=1):
    """Add words to one named bracket of every process of a cell."""
    hit = 0
    for r in records:
        if (r["kind"], r["image"], r["variant"]) == (kind, image, variant):
            for b in r["brackets"]:
                if b["name"] == name:
                    b["end"][3] += words
                    hit += 1
    assert hit, (kind, image, variant, name)


def declared_data(entries=None, noise=None, candidate_only=()):
    def entry(n, kinds):
        b, c = BLOB[n]
        return dict(path=PATHS[n], baseline_blob=b, candidate_blob=c,
                    kinds=kinds, reason="r", mechanism="m")
    both = list(g.LOADS)
    if entries is None:
        entries = [entry("Cond_rewr.sig", both), entry("Cond_rewr.sml", both),
                   entry("simpLib.sml", both),
                   entry("congLib.sml", ["load-congLib"])]
    if noise is None:
        noise = [dict(path=PATHS["Trace.sml"], blob=BLOB["Trace.sml"][0],
                      reason="r", mechanism="shown")]
    return g.parse_declared(json.dumps(dict(
        schema=g.DECLARED_SCHEMA, entries=entries, noise=noise,
        candidate_only=list(candidate_only))))


def entry_of(name, kinds=None):
    b, c = BLOB[name]
    return dict(path=PATHS[name], baseline_blob=b, candidate_blob=c,
                kinds=kinds or list(g.LOADS), reason="r", mechanism="m")


# The words the declared set carries in the baseline: sig +4, sml +2, simpLib
# +1, congLib +1 (an arbitrary but fixed vector).
DELTA = {"Cond_rewr.sig": 4, "Cond_rewr.sml": 2, "simpLib.sml": 1,
         "congLib.sml": 1}


RECORD = "7" * 64


def run(records, declared=None, null=False, pairs=TEST_PAIRS, sides=None,
        record=RECORD):
    with mock.patch.object(g, "PAIRS", pairs):
        return g.analyse(records, sides or SIDES, declared or declared_data(),
                         SOURCES, pairs, null, record)


def delta_for(kind, **over):
    d = dict(DELTA, **over)
    if kind == "load-simpLib":
        d.pop("congLib.sml")
    return d


def attributed_world(**kw):
    """A run in which the declared files carry exactly DELTA on every
    image; the load brackets carry the same words."""
    gap = {"load-simpLib": sum(v for k, v in DELTA.items()
                               if k != "congLib.sml"),
           "load-congLib": sum(DELTA.values())}
    # The load kinds add the file words themselves: the loader gap is the
    # difference and so stays 0.
    kw.setdefault("delta", DELTA)
    return world(**kw), gap


class DeclaredTest(unittest.TestCase):
    def test_repository_declaration_is_well_formed(self):
        text, data = g.load_declared()
        self.assertTrue(data["entries"])
        self.assertTrue(text.endswith("\n"))

    def rejects(self, **change):
        data = dict(schema=g.DECLARED_SCHEMA,
                    entries=[entry_of("simpLib.sml")], noise=[],
                    candidate_only=[])
        data.update(change)
        with self.assertRaises(sc.InvalidAllocation):
            g.parse_declared(json.dumps(data))

    def test_entries_are_checked(self):
        self.rejects(schema="old")
        self.rejects(entries=[dict(entry_of("simpLib.sml"), kinds=[])])
        self.rejects(entries=[dict(entry_of("simpLib.sml"),
                                   kinds=["files-simpLib"])])
        self.rejects(entries=[dict(entry_of("simpLib.sml"), mechanism=" ")])
        self.rejects(entries=[dict(entry_of("simpLib.sml"),
                                   candidate_blob="zz")])
        self.rejects(entries=[entry_of("simpLib.sml")] * 2)
        self.rejects(candidate_only=["Foo"])
        self.rejects(noise=[dict(path=PATHS["simpLib.sml"], blob="1" * 40,
                                 reason="r", mechanism=None)])

    def test_stale_blob_is_not_declared(self):
        wrong = dict(entry_of("Cond_rewr.sig"), candidate_blob="9" * 40)
        records, _ = attributed_world()
        report = run(records, declared_data(entries=[wrong]))
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("does not match the sources" in r
                            for r in report["reasons"]))
        self.assertTrue(any("undeclared file" in r
                            for r in report["reasons"]))


class ImageRuleTest(unittest.TestCase):
    """R1: the image content, exact on every image of both sides."""

    def test_identical_images_pass(self):
        report = run(world(), declared_data(entries=[]))
        self.assertEqual(report["decision"], "pass", report["reasons"])

    def test_startup_word_on_one_candidate_image_fails(self):
        report = run(world(startup={"s2": 1}))
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any(r.startswith("R1 hol-startup")
                            for r in report["reasons"]))

    def test_startup_word_on_a_baseline_image_fails(self):
        self.assertEqual(run(world(startup={"b2": 3}))["decision"], "fail")

    def test_first_use_word_fails(self):
        report = run(world(first_use={"s1": 7}))
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any(r.startswith("R1 hol-first-use")
                            for r in report["reasons"]))

    def test_hol_state0_startup_bracket_fails(self):
        records = world()
        for r in records:
            if r["kind"] == "load-simpLib" and r["image"] == "s2":
                r["brackets"][1]["end"][3] += 1
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("R1 load-simpLib" in r for r in report["reasons"]))

    def test_nondeterministic_cell_fails(self):
        records = world()
        records[0]["brackets"][0]["start"][3] += 1
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("nondeterministic" in r
                            for r in report["reasons"]))


class SourceRuleTest(unittest.TestCase):
    """R2: sources against sources over one image."""

    def attributed(self, **kw):
        records, _ = attributed_world(**kw)
        return run(records)

    def test_declared_delta_is_attributed(self):
        report = self.attributed()
        self.assertEqual(report["decision"], "attributed", report["reasons"])
        got = report["attributed"]["load-congLib"]
        self.assertEqual(got[BR["Cond_rewr.sig"]]["delta"]["total"], 4)
        self.assertEqual(sorted(report["attributed"]["load-simpLib"]),
                         [BR[n] for n in ("Cond_rewr.sig", "Cond_rewr.sml",
                                          "simpLib.sml")])

    def test_attribution_needs_the_visibility_record(self):
        records, _ = attributed_world()
        report = run(records, record=None)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("not-client-visible" in r
                            for r in report["reasons"]))

    def test_no_change_is_a_pass(self):
        report = run(world(), declared_data(entries=[]))
        self.assertEqual(report["decision"], "pass", report["reasons"])

    def one_sided(self, side, words=7, entry=True, register=False):
        """A file that only `side` compiles, with its whole bracket as the
        delta (and the same words in the load brackets).  With `register`
        the candidate's records also list the file and its module, as a
        real candidate-added file does."""
        name = "$(HOLDIR)/src/simp/src/New.sml"
        records, _ = attributed_world()
        for r in records:
            if register and r["variant"] == "candidate":
                r["loaded"] = list(r["loaded"]) + ["New"]
                if r["files"] is not None:
                    r["files"] = list(r["files"]) + [name]
            if r["variant"] != side:
                continue
            if r["kind"].startswith("files"):
                r["brackets"].append(dict(name=name, start=words_(0),
                                          end=words_(words)))
            else:
                r["brackets"][2]["end"][3] += words
                r["brackets"][2]["end"][4] += words
        entries = [entry_of(n, k) for n, k in (
            ("Cond_rewr.sig", None), ("Cond_rewr.sml", None),
            ("simpLib.sml", None), ("congLib.sml", ["load-congLib"]))]
        new = dict(entry_of("Trace.sml"), path="src/simp/src/New.sml",
                   kinds=list(g.LOADS))
        if side == "candidate":
            new.update(baseline_blob=None, candidate_blob="8" * 40)
        else:
            new.update(baseline_blob="8" * 40, candidate_blob=None)
        if entry:
            entries.append(new)
        sources = {v: dict(m) for v, m in SOURCES.items()}
        sources[side]["src/simp/src/New.sml"] = "8" * 40
        return records, declared_data(entries=entries), sources

    def run_sources(self, records, declared, sources):
        with mock.patch.object(g, "PAIRS", TEST_PAIRS):
            return g.analyse(records, SIDES, declared, sources, TEST_PAIRS,
                             False, RECORD)

    def test_candidate_added_file_is_attributed_when_declared(self):
        records, declared, sources = self.one_sided("candidate")
        report = self.run_sources(records, declared, sources)
        self.assertEqual(report["decision"], "attributed", report["reasons"])
        row = report["attributed"]["load-simpLib"][
            "$(HOLDIR)/src/simp/src/New.sml"]
        self.assertEqual(row["delta"]["total"], 7)

    def test_candidate_added_file_needs_both_declarations(self):
        # An entries item (null baseline blob) pays for the words; the
        # extension rule needs candidate_only for the module and the file.
        records, declared, sources = self.one_sided("candidate",
                                                       register=True)
        report = self.run_sources(records, declared, sources)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("candidate-only" in r and "module New" in r
                            for r in report["reasons"]), report["reasons"])
        self.assertTrue(any("file $(HOLDIR)/src/simp/src/New.sml" in r
                            for r in report["reasons"]), report["reasons"])
        declared["candidate_only"] = [
            "module New", "file $(HOLDIR)/src/simp/src/New.sml"]
        report = self.run_sources(records, declared, sources)
        self.assertEqual(report["decision"], "attributed", report["reasons"])
        # candidate_only alone does not pay for the words.
        records, declared, sources = self.one_sided(
            "candidate", entry=False, register=True)
        declared["candidate_only"] = [
            "module New", "file $(HOLDIR)/src/simp/src/New.sml"]
        report = self.run_sources(records, declared, sources)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("compiled by the candidate sources only and is "
                            "not declared" in r for r in report["reasons"]),
                        report["reasons"])

    def test_candidate_added_file_fails_cleanly_when_undeclared(self):
        records, declared, sources = self.one_sided("candidate",
                                                       entry=False)
        report = self.run_sources(records, declared, sources)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("compiled by the candidate sources only" in r
                            for r in report["reasons"]))

    def test_baseline_only_file_is_a_negative_declared_delta(self):
        records, declared, sources = self.one_sided("base")
        report = self.run_sources(records, declared, sources)
        self.assertEqual(report["decision"], "attributed", report["reasons"])
        row = report["attributed"]["load-congLib"][
            "$(HOLDIR)/src/simp/src/New.sml"]
        self.assertEqual(row["delta"]["total"], -7)
        records, declared, sources = self.one_sided("base", entry=False)
        report = self.run_sources(records, declared, sources)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("compiled by the baseline sources only" in r
                            for r in report["reasons"]))

    def test_mechanism_may_be_a_list_of_lines(self):
        e = dict(entry_of("simpLib.sml"), mechanism=["one ", "two"])
        data = g.parse_declared(json.dumps(dict(
            schema=g.DECLARED_SCHEMA, entries=[e], noise=[],
            candidate_only=[])))
        self.assertEqual(data["entries"][0]["mechanism"], "one two")
        noise = dict(path="src/simp/src/N.sml", blob="a" * 40, reason="r",
                     mechanism=["a", "b"])
        got = g.parse_declared(json.dumps(dict(
            schema=g.DECLARED_SCHEMA, entries=[], noise=[noise],
            candidate_only=[])))
        self.assertEqual(got["noise"][0]["mechanism"], "a b")
        for bad in ([], [1], 5):
            with self.assertRaises(sc.InvalidAllocation):
                g.parse_declared(json.dumps(dict(
                    schema=g.DECLARED_SCHEMA, entries=[], noise=[dict(
                        noise, mechanism=bad)], candidate_only=[])))
        with self.assertRaises(sc.InvalidAllocation):
            g.parse_declared(json.dumps(dict(
                schema=g.DECLARED_SCHEMA, entries=[dict(e, mechanism=[])],
                noise=[], candidate_only=[])))

    def test_one_sided_declaration_needs_one_blob(self):
        both_none = dict(entry_of("simpLib.sml"), baseline_blob=None,
                         candidate_blob=None)
        with self.assertRaises(sc.InvalidAllocation):
            g.parse_declared(json.dumps(dict(
                schema=g.DECLARED_SCHEMA, entries=[both_none], noise=[],
                candidate_only=[])))
        ok = dict(entry_of("simpLib.sml"), baseline_blob=None)
        g.parse_declared(json.dumps(dict(
            schema=g.DECLARED_SCHEMA, entries=[ok], noise=[],
            candidate_only=[])))

    def test_declared_entries_measuring_zero_fail(self):
        report = run(world())
        self.assertEqual(report["decision"], "fail")
        self.assertIn("load-simpLib %s" % BR["Cond_rewr.sig"],
                      report["declared_zero"])

    def test_undeclared_word_fails_under_image_noise(self):
        """The review's counterexample: Trace.sml-like noise on the load
        bracket and +3 on an undeclared file that is stable."""
        noise = {"b1": {"Trace.sml": 0}, "b2": {"Trace.sml": 40},
                 "s1": {"Trace.sml": -12}, "s2": {"Trace.sml": 27}}
        report = run(world(delta=dict(DELTA, **{"Other.sml": 3}),
                           noise=noise))
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("undeclared file" in r and "Other.sml" in r
                            for r in report["reasons"]))

    def test_undeclared_word_without_any_other_change_fails(self):
        for words in (1, 3):
            report = run(world(delta=dict(DELTA, **{"A.sml": words})))
            self.assertEqual(report["decision"], "fail", words)

    def test_one_word_on_a_single_image_fails(self):
        records, _ = attributed_world()
        for kind in ("files-simpLib", "load-simpLib"):
            name = BR["Other.sml"] if kind.startswith("files") else \
                "load_simpLib"
            bump(records, kind, "s2", "candidate", name)
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("undeclared file" in r and "Other.sml" in r
                            for r in report["reasons"]))

    def test_declared_delta_differing_between_images_fails(self):
        records, _ = attributed_world()
        bump(records, "files-simpLib", "b2", "candidate", BR["Cond_rewr.sig"])
        bump(records, "load-simpLib", "b2", "candidate", "load_simpLib")
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("differs between images" in r
                            for r in report["reasons"]))

    def test_loader_gap_must_be_zero(self):
        records, _ = attributed_world(gap_delta={"load-simpLib": 2})
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("loader gap" in r for r in report["reasons"]))

    def test_load_bracket_without_its_files_fails(self):
        report = self.attributed(gap_delta={"load-congLib": -5})
        self.assertEqual(report["decision"], "fail")

    def test_post_load_bracket_must_be_exact(self):
        report = self.attributed(post=1)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("SIMP_CONV_1" in r for r in report["reasons"]))

    def test_missing_bracket_is_a_reason_not_a_crash(self):
        records, _ = attributed_world()
        for r in records:
            if r["kind"] == "load-simpLib" and r["variant"] == "candidate" \
                    and r["image"] == "s1":
                r["brackets"] = r["brackets"][:2]
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("one side only" in r for r in report["reasons"]))

    def test_candidate_file_missing_from_the_load(self):
        records, _ = attributed_world()
        for r in records:
            if r["kind"] == "files-congLib" and r["variant"] == "candidate":
                r["brackets"] = r["brackets"][:-1]
        self.assertEqual(run(records)["decision"], "fail")

    def test_declaration_cannot_excuse_other_kinds(self):
        records, _ = attributed_world(startup={"s1": 2})
        self.assertEqual(run(records)["decision"], "fail")

    def test_declaration_kind_scope(self):
        """congLib.sml is declared for load-congLib only."""
        records, _ = attributed_world()
        for r in records:
            if r["kind"] == "files-simpLib":
                r["brackets"].append(dict(
                    name=BR["congLib.sml"], start=words_(0),
                    end=words_(7 if r["variant"] == "candidate" else 6)))
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("undeclared file" in r and "congLib.sml" in r
                            for r in report["reasons"]))

    def test_null_control_ignores_declarations(self):
        report = run(world(), null=True)
        self.assertEqual(report["decision"], "pass", report["reasons"])
        records, _ = attributed_world()
        self.assertEqual(run(records, null=True)["decision"], "fail")


class NoiseRuleTest(unittest.TestCase):
    """R3: with the sources fixed the images may differ only in the noise
    files, and only with a mechanism."""

    NOISE = {"b1": {"Trace.sml": 0}, "b2": {"Trace.sml": 12},
             "s1": {"Trace.sml": 40}, "s2": {"Trace.sml": -27}}

    def noisy(self, mechanism, noise=None, **kw):
        n = dict(path=PATHS["Trace.sml"], blob=BLOB["Trace.sml"][0],
                 reason="r", mechanism=mechanism)
        records, _ = attributed_world(noise=noise or self.NOISE, **kw)
        return run(records, declared_data(noise=[n]))

    def test_noise_without_a_mechanism_is_a_blocker(self):
        report = self.noisy(None)
        self.assertEqual(report["decision"], "blocked", report["reasons"])
        self.assertTrue(report["blockers"])
        self.assertIn(BR["Trace.sml"], report["noise"])

    def test_noise_with_a_mechanism_is_attributed(self):
        report = self.noisy("shown")
        self.assertEqual(report["decision"], "attributed", report["reasons"])

    def test_asymmetric_noise_is_decided_not_inconclusive(self):
        """Independent noise on the two sides with candidate images outside
        the baseline envelope; the rule does not need an envelope."""
        report = self.noisy("shown", noise={
            "b1": {"Trace.sml": 5}, "b2": {"Trace.sml": 6},
            "s1": {"Trace.sml": 90}, "s2": {"Trace.sml": -90}})
        self.assertEqual(report["decision"], "attributed", report["reasons"])

    def test_noise_cannot_hide_an_undeclared_word(self):
        report = self.noisy("shown", delta=dict(DELTA, **{"Other.sml": 3}))
        self.assertEqual(report["decision"], "fail")

    def test_unexplained_image_difference_in_a_stable_file_fails(self):
        report = self.noisy("shown", noise=dict(
            self.NOISE, s1={"Trace.sml": 40, "Other.sml": 1}))
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any(r.startswith("R3 files-") and "Other.sml" in r
                            for r in report["reasons"]))

    def test_noise_not_in_a_declared_file_fails_even_if_equal_on_sides(self):
        records, _ = attributed_world(noise={
            "b1": {"A.sml": 2}, "b2": {"A.sml": 2}, "s1": {}, "s2": {}})
        report = run(records)
        self.assertEqual(report["decision"], "fail")

    def test_load_noise_not_explained_by_a_noise_file_fails(self):
        records, _ = attributed_world(noise=self.NOISE)
        for r in records:
            if r["kind"] == "load-simpLib" and r["image"] == "s1":
                r["brackets"][2]["end"][3] += 5
        report = run(records, declared_data(noise=[dict(
            path=PATHS["Trace.sml"], blob=BLOB["Trace.sml"][0], reason="r",
            mechanism="shown")]))
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any(r.startswith("R3 load-simpLib")
                            for r in report["reasons"]))

    def test_noise_file_must_not_depend_on_the_change(self):
        records, _ = attributed_world(delta=dict(DELTA, **{"Trace.sml": 1}))
        report = run(records)
        self.assertEqual(report["decision"], "fail")

    def test_noise_file_blob_must_match(self):
        n = dict(path=PATHS["Trace.sml"], blob="9" * 40, reason="r",
                 mechanism="shown")
        records, _ = attributed_world()
        report = run(records, declared_data(noise=[n]))
        self.assertEqual(report["decision"], "fail")

    def test_acceptance_needs_two_images_and_ten_pairs(self):
        records, _ = attributed_world()
        smoke = run(records, pairs=TEST_PAIRS)
        with mock.patch.object(g, "PAIRS", TEST_PAIRS + 1):
            report = g.analyse(records, SIDES, declared_data(), SOURCES,
                               TEST_PAIRS, False, RECORD)
        self.assertEqual(smoke["decision"], "attributed")
        self.assertEqual(report["decision"], "smoke")
        one = world(base=("b1",), cand=("s1",))
        report = run(one, declared_data(entries=[]),
                     sides=dict(base=["b1"], candidate=["s1"]))
        self.assertEqual(report["decision"], "smoke")


class ExtensionTest(unittest.TestCase):
    def test_candidate_only_module_fails(self):
        records, _ = attributed_world(extra={
            ("load-simpLib", "s1", "candidate"): dict(
                loaded=MODULES + ["fooLib"])})
        for r in records:
            if r["kind"] == "load-simpLib" and r["image"] == "s1" and \
                    r["variant"] == "candidate":
                r["loaded"] = MODULES + ["fooLib"]
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("module fooLib" in r for r in report["reasons"]))

    def test_candidate_only_module_can_be_declared(self):
        records, _ = attributed_world()
        for r in records:
            if r["kind"] == "hol-startup" and r["image"] in CAND:
                r["loaded"] = MODULES + ["simpMarkerTheory"]
        self.assertEqual(run(records)["decision"], "fail")
        report = run(records, declared_data(
            candidate_only=["module simpMarkerTheory"]))
        self.assertEqual(report["decision"], "attributed", report["reasons"])

    def test_candidate_only_registered_file_fails_unless_declared(self):
        records, _ = attributed_world()
        for r in records:
            if r["kind"] == "files-simpLib" and r["image"] == "s1" and \
                    r["pair"] == 0:
                r["files"] = FILES + ["New.sml"]
                r["files_sha"] = g.sha(r["files"])
        for r in records:
            if r["kind"] == "files-simpLib" and r["image"] == "s1" and \
                    r["pair"] > 0:
                r["files_sha"] = g.sha(FILES + ["New.sml"])
        report = run(records)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("file New.sml" in r for r in report["reasons"]))
        report = run(records, declared_data(
            candidate_only=["file New.sml"]))
        self.assertEqual(report["decision"], "attributed", report["reasons"])

    def test_candidate_only_structure_fails(self):
        records, _ = attributed_world()
        for r in records:
            if r["kind"] == "hol-first-use" and r["image"] == "s2":
                r["structures"] = STRUCTS + ["Anything"]
        self.assertEqual(run(records)["decision"], "fail")

    def test_baseline_only_module_is_not_an_extension(self):
        records, _ = attributed_world()
        for r in records:
            if r["image"] in BASE:
                r["loaded"] = MODULES + ["onlyBase"]
        self.assertEqual(run(records)["decision"], "attributed")

    def test_wrong_simplifier_result_fails(self):
        records, _ = attributed_world()
        for r in records:
            if r["kind"] == "hol-first-use":
                r["result"] = "false"
        self.assertEqual(run(records)["decision"], "fail")

    def test_names(self):
        for name in ("simpExtLib", "congExtLib", "SimpTracking",
                     "intReduceExt", "Cond_rewrExt", "numSimpsExt"):
            self.assertTrue(g.is_extension(name), name)
        for name in ("simpLib", "congLib", "Cond_rewr", "boolSimps", "Text"):
            self.assertFalse(g.is_extension(name), name)
        self.assertFalse(g.is_extension("SimpTracking", ("SimpTracking",)))


class SetupTest(unittest.TestCase):
    def trees(self):
        def t(label, rev, patch=None):
            return dict(rev=rev, hol="/s/%s/hol-source" % label,
                        hol_patch=patch, hol_build_deterministic=False,
                        hol_build_jobs="2", hol_determinism_diff="",
                        hol_configuration_override="")
        return {"b1": t("b1", "B", {"sha256": "p"}),
                "b2": t("b2", "B", {"sha256": "p"}),
                "s1": t("s1", "C"), "s2": t("s2", "C")}

    def check(self, trees=None, sides=SIDES, null=False):
        return g.check_setup(trees or self.trees(), sides, null)

    def test_valid(self):
        self.assertEqual(self.check()["base"], ("B", "p"))

    def test_guards(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "not distinct"):
            self.check(sides=dict(base=["b1", "b1"], candidate=["s1", "s2"]))
        with self.assertRaisesRegex(sc.InvalidAllocation, "not distinct"):
            self.check(sides=dict(base=["b1", "b2"], candidate=["b2", "s2"]))
        with self.assertRaisesRegex(sc.InvalidAllocation, "no image"):
            self.check(sides=dict(base=[], candidate=["s1"]))
        trees = self.trees()
        trees["s2"]["hol"] = "/s/s2x/hol-source"
        with self.assertRaisesRegex(sc.InvalidAllocation, "HOLDIR lengths"):
            self.check(trees)
        trees = self.trees()
        trees["s2"]["rev"] = "D"
        with self.assertRaisesRegex(sc.InvalidAllocation, "more than one"):
            self.check(trees)
        trees = self.trees()
        trees["b2"]["hol_patch"] = {"sha256": "q"}
        with self.assertRaisesRegex(sc.InvalidAllocation, "more than one"):
            self.check(trees)
        trees = self.trees()
        trees["s1"]["hol_build_deterministic"] = True
        with self.assertRaisesRegex(sc.InvalidAllocation, "build flags"):
            self.check(trees)
        trees = self.trees()
        trees["s1"]["hol_build_jobs"] = "1"
        with self.assertRaisesRegex(sc.InvalidAllocation, "build flags"):
            self.check(trees)

    def test_null_needs_equal_sources_and_real_changes_need_unequal(self):
        trees = self.trees()
        with self.assertRaisesRegex(sc.InvalidAllocation, "null control"):
            self.check(trees, null=True)
        for l in ("s1", "s2"):
            trees[l]["rev"], trees[l]["hol_patch"] = "B", {"sha256": "p"}
        self.check(trees, null=True)
        with self.assertRaisesRegex(sc.InvalidAllocation, "same revision"):
            self.check(trees)


class OverlayTest(unittest.TestCase):
    def tree(self, root, files):
        for rel, data in files.items():
            p = Path(root) / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)

    def test_overlay_exchanges_only_differing_files(self):
        with tempfile.TemporaryDirectory() as raw:
            t = Path(raw)
            common = {"src/simp/src/A.sml": b"a\n",
                      "src/simp/src/.hol/objs/A.uo": b"u\n",
                      "src/simp/src/notes.md": b"n\n"}
            self.tree(t / "b", dict(common, **{
                "src/simp/src/Cond_rewr.sig": b"old\n",
                "src/simp/src/OnlyBase.sml": b"x\n"}))
            self.tree(t / "c", dict(common, **{
                "src/simp/src/Cond_rewr.sig": b"new\n",
                "src/simp/src/notes.md": b"changed\n",
                "src/simp/src/Ext.sml": b"e\n"}))
            ov = g.Overlay(t / "b", t / "c", extra=["src/simp/src/A.sml"])
            self.assertEqual(ov.paths(), [
                "src/simp/src/Cond_rewr.sig", "src/simp/src/Ext.sml",
                "src/simp/src/OnlyBase.sml"])
            self.assertEqual(ov.only, {"base": ["src/simp/src/OnlyBase.sml"],
                                       "candidate": ["src/simp/src/Ext.sml"]})
            self.assertEqual(ov.clock, [])
            self.assertEqual(ov.blobs["base"]["src/simp/src/A.sml"],
                             g.blob_id(b"a\n"))
            self.assertEqual(ov.blobs["candidate"][
                "src/simp/src/Cond_rewr.sig"], g.blob_id(b"new\n"))
            self.assertTrue(ov.check(t / "b", "base"))
            self.assertTrue(ov.check(t / "c", "candidate"))
            self.assertFalse(ov.check(t / "b", "candidate"))
            # The candidate variant: changed file, added file, and the
            # baseline-only file is gone.
            self.assertEqual(ov.apply(t / "b", "candidate"), 3)
            self.assertEqual(
                (t / "b/src/simp/src/Cond_rewr.sig").read_bytes(), b"new\n")
            self.assertEqual((t / "b/src/simp/src/Ext.sml").read_bytes(),
                             b"e\n")
            self.assertFalse((t / "b/src/simp/src/OnlyBase.sml").exists())
            self.assertEqual(ov.apply(t / "b", "candidate"), 0)
            self.assertTrue(ov.check(t / "b", "candidate"))
            self.assertFalse(ov.check(t / "b", "base"))
            self.assertEqual(ov.apply(t / "b", "base"), 3)
            self.assertEqual(
                (t / "b/src/simp/src/Cond_rewr.sig").read_bytes(), b"old\n")
            self.assertEqual((t / "b/src/simp/src/OnlyBase.sml").read_bytes(),
                             b"x\n")
            self.assertFalse((t / "b/src/simp/src/Ext.sml").exists())
            self.assertTrue(ov.check(t / "b", "base"))
            self.assertEqual(ov.blobs["candidate"]["src/simp/src/Ext.sml"],
                             g.blob_id(b"e\n"))
            self.assertNotIn("src/simp/src/Ext.sml", ov.blobs["base"])

    def test_clock_mentions_are_listed(self):
        with tempfile.TemporaryDirectory() as raw:
            t = Path(raw)
            files = {"src/simp/src/Trace.sml": b"val t = hol_clock\n",
                     "src/simp/src/Same.sml": b"Timer.checkCPUTimer x\n",
                     "src/simp/src/Fine.sml": b"fine\n"}
            self.tree(t / "b", dict(files, **{
                "src/simp/src/Other.sml": b"1\n"}))
            self.tree(t / "c", dict(files, **{
                "src/simp/src/Other.sml": b"2\n",
                "src/simp/src/New.sml": b"Globals.hol_clock\n"}))
            ov = g.Overlay(t / "b", t / "c", extra=[
                "src/simp/src/Same.sml", "src/simp/src/Fine.sml"])
            # Same.sml is declared (extra), Trace.sml is neither declared nor
            # different, New.sml is overlaid.
            self.assertEqual(ov.clock, ["src/simp/src/New.sml",
                                        "src/simp/src/Same.sml"])

    def test_gate_refuses_clock_mentions(self):
        ov = mock.Mock(clock=["src/simp/src/New.sml"])
        with self.assertRaisesRegex(sc.InvalidAllocation, "CPU timer"):
            g.require_no_clock(ov)
        g.require_no_clock(mock.Mock(clock=[]))

    def test_blob_id_is_the_git_blob(self):
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / "f"
            p.write_bytes(b"hello\n")
            want = subprocess.run(["git", "hash-object", str(p)], check=True,
                                  capture_output=True, text=True).stdout
            self.assertEqual(g.blob_id(b"hello\n"), want.strip())


class CellFixtureTest(unittest.TestCase):
    def test_fixtures_of_a_revision_are_the_committed_blobs(self):
        with tempfile.TemporaryDirectory() as raw:
            repo, dst = Path(raw) / "repo", Path(raw) / "dst"
            perf = repo / "src/simp/tests/performance"
            paired = repo / "src/simp/tests/compatibility/paired"
            perf.mkdir(parents=True)
            paired.mkdir(parents=True)
            dst.mkdir()
            (perf / "F1.sml").write_text("old1\n")
            (perf / "F2.sml").write_text("old2\n")
            (paired / "runner.sml").write_text("runner\n")
            (paired / "Holmakefile").write_text("hm\n")
            (paired / "note.txt").write_text("skip\n")
            (perf / "review-20261021").mkdir()
            (perf / "review-20261021/abicheck.sml").write_text(
                "val x = 1\nval _ = OS.Process.exit OS.Process.success\n")
            shutil.copyfile(g.rp.__file__, paired.parent / "run_paired.py")

            def git(*args):
                subprocess.run(("git", "-c", "user.name=t", "-c",
                                "user.email=t@t") + args, cwd=repo,
                               check=True, capture_output=True)
            git("init", "-q")
            git("add", ".")
            git("commit", "-q", "-m", "one")
            (perf / "F1.sml").write_text("new1\n")
            am = mock.Mock(FIXTURES=("F1.sml", "F2.sml"), HERE=perf)
            g.install_cell_fixtures(repo, "HEAD", dst, am)
            self.assertEqual((dst / "Performance.sml").read_text(), "old1\n")
            self.assertEqual((dst / "F2.sml").read_text(), "old2\n")
            self.assertEqual((dst / "runner.sml").read_text(), "runner\n")
            self.assertEqual((dst / "Holmakefile").read_text(), "hm\n")
            self.assertFalse((dst / "note.txt").exists())
            self.assertEqual((dst / "SignatureCheck.sml").read_text(),
                             'val x = 1\nval _ = Paired.check '
                             '"legacy signature" true\n')


    def test_the_revisions_own_runner_installs_its_fixtures(self):
        with tempfile.TemporaryDirectory() as raw:
            repo, job = Path(raw) / "repo", Path(raw) / "job"
            dst = job / "sel"
            compat = repo / "src/simp/tests/compatibility"
            perf = repo / "src/simp/tests/performance"
            (compat / "paired").mkdir(parents=True)
            (perf / "review-20261021").mkdir(parents=True)
            dst.mkdir(parents=True)
            (compat / "paired/runner.sml").write_text("r\n")
            (perf / "review-20261021/abicheck.sml").write_text("x\n")
            (perf / "F1.sml").write_text("old1\n")
            (compat / "run_paired.py").write_text(
                "from pathlib import Path\n"
                "HERE = Path(__file__).resolve().parent\n"
                "def install_fixtures(dst):\n"
                "    (dst / 'REV-RUNNER').write_text(str(HERE.name))\n")

            def git(*args):
                subprocess.run(("git", "-c", "user.name=t", "-c",
                                "user.email=t@t") + args, cwd=repo,
                               check=True, capture_output=True)
            git("init", "-q")
            git("add", ".")
            git("commit", "-q", "-m", "one")
            before = g.rp.HERE
            am = mock.Mock(FIXTURES=("F1.sml",), HERE=perf)
            g.install_cell_fixtures(repo, "HEAD", dst, am)
            self.assertEqual((dst / "REV-RUNNER").read_text(),
                             "compatibility")
            self.assertEqual((dst / "Performance.sml").read_text(), "old1\n")
            self.assertIs(g.rp.HERE, before)
            # The temporary tree lives beside dst, not inside it.
            self.assertEqual(sorted(p.name for p in dst.iterdir()),
                             ["Performance.sml", "REV-RUNNER"])
            self.assertEqual([p.name for p in job.iterdir()], ["sel"])


class SizedTmpdirTest(unittest.TestCase):
    def test_path_has_the_requested_length(self):
        with tempfile.TemporaryDirectory() as raw:
            base = Path(raw) / "t"
            for n in (len(str(base)) + 3, len(str(base)) + 8):
                path = g.sized_tmpdir(base, n)
                self.assertEqual(len(str(path)), n)
                self.assertTrue(path.is_dir())
            self.assertEqual(g.sized_tmpdir(base, None), base.resolve())
            # A relative or symlinked base is resolved before padding.
            link = Path(raw) / "link"
            link.symlink_to(Path(raw))
            padded = g.sized_tmpdir(link / "t", len(str(base)) + 4)
            self.assertEqual(padded, padded.resolve())
            self.assertEqual(len(str(padded)), len(str(base)) + 4)
            cwd = os.getcwd()
            os.chdir(raw)
            try:
                rel = g.sized_tmpdir(Path("t"), len(str(base)) + 6)
            finally:
                os.chdir(cwd)
            self.assertEqual(len(str(rel)), len(str(base)) + 6)
            with self.assertRaises(sc.InvalidAllocation):
                g.sized_tmpdir(base, len(str(base)) - 1)


class PlanTest(unittest.TestCase):
    def test_every_cell_once_with_alternating_order(self):
        plan = g.plan_runs(["hol-startup", "load-simpLib"], SIDES, 4)
        self.assertEqual(len(plan), 4 * 4 * (1 + 2))
        self.assertEqual(len(set(plan)), len(plan))
        by = {}
        for i, (kind, image, variant, pair) in enumerate(plan):
            by[(kind, image, variant, pair)] = i
        for pair in range(4):
            first = by[("load-simpLib", "b1", "base", pair)] < \
                by[("load-simpLib", "b1", "candidate", pair)]
            self.assertEqual(first, pair % 2 == 0)
        self.assertLess(by[("load-simpLib", "b1", "base", 0)],
                        by[("load-simpLib", "s2", "base", 0)])
        self.assertLess(by[("load-simpLib", "s2", "base", 1)],
                        by[("load-simpLib", "b1", "base", 1)])


class ArchiveTest(unittest.TestCase):
    def archive(self, root, records, record=RECORD):
        header = dict(
            schema=g.SCHEMA, sides=SIDES, null=False, pairs=TEST_PAIRS,
            record_sha256=record, clock_mentions=[],
            hol={l: "/s/%s/hol-source" % l for l in BASE + CAND},
            holdir_length=len("/s/b1/hol-source"), sources=SOURCES,
            declared_text=json.dumps(declared_data_raw()),
            declared_sha256=hashlib.sha256(
                json.dumps(declared_data_raw()).encode()).hexdigest())
        with mock.patch.object(g, "PAIRS", TEST_PAIRS):
            report = g.analyse(records, SIDES, g.parse_declared(
                header["declared_text"]), SOURCES, TEST_PAIRS, False, record)
        g.write_archive(root, records, header, report)
        return report

    def test_replay_and_tamper_detection(self):
        records, _ = attributed_world()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            record = root / "record.md"
            record.write_text("x\n")
            self.archive(root, records, g.sha_file(record))
            patch = mock.patch.object(g, "PAIRS", TEST_PAIRS)
            patch.start()
            self.addCleanup(patch.stop)
            args = mock.Mock(output=root, record=record)
            with self.assertRaisesRegex(sc.InvalidAllocation, "--record"):
                g.replay(mock.Mock(output=root, record=None))
            record.write_text("y\n")
            with self.assertRaisesRegex(sc.InvalidAllocation, "seal"):
                g.replay(args)
            record.write_text("x\n")
            self.assertEqual(g.replay(args), 0)
            self.assertIn("receipt.json", os.listdir(root))
            text = (root / "decisions.json").read_text()
            (root / "decisions.json").write_text(
                text.replace('"attributed"', '"pass"'))
            with self.assertRaisesRegex(sc.InvalidAllocation, "receipt"):
                g.replay(args)

    def test_replay_refuses_clock_mentions(self):
        records, _ = attributed_world()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            self.archive(root, records)
            self.reseal(root, clock_mentions=["src/simp/src/New.sml"])
            with mock.patch.object(g, "PAIRS", TEST_PAIRS):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "CPU timer"):
                    g.replay(mock.Mock(output=root, record=None))

    def test_replay_refuses_an_old_schema_cleanly(self):
        records, _ = attributed_world()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            self.archive(root, records)
            self.reseal(root, schema="task31-startup-gate-v2")
            header = json.loads((root / "header.json").read_text())
            del header["clock_mentions"]
            (root / "header.json").write_text(json.dumps(header))
            self.reseal(root)
            with self.assertRaisesRegex(sc.InvalidAllocation,
                                        "schema.*task31-startup-gate-v2"):
                g.replay(mock.Mock(output=root, record=None))

    def test_replay_refuses_schema_v3_cleanly(self):
        records, _ = attributed_world()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            self.archive(root, records)
            self.assertEqual(g.SCHEMA, "task31-startup-gate-v4")
            self.reseal(root, schema="task31-startup-gate-v3")
            with self.assertRaisesRegex(sc.InvalidAllocation,
                                        "schema.*task31-startup-gate-v3"):
                g.replay(mock.Mock(output=root, record=None))

    def reseal(self, root, **fields):
        header = json.loads((root / "header.json").read_text())
        header.update(fields)
        (root / "header.json").write_text(json.dumps(header))
        (root / "receipt.json").write_text(json.dumps({
            n: g.sha_file(root / n) for n in (
                "records.json.gz", "header.json", "decisions.json",
                "RESULTS.md")}))

    def test_replay_checks_the_declaration_seal(self):
        records, _ = attributed_world()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            self.archive(root, records)
            patch = mock.patch.object(g, "PAIRS", TEST_PAIRS)
            patch.start()
            self.addCleanup(patch.stop)
            header = json.loads((root / "header.json").read_text())
            header["declared_sha256"] = "0" * 64
            (root / "header.json").write_text(json.dumps(header))
            (root / "receipt.json").write_text(json.dumps({
                n: g.sha_file(root / n) for n in (
                    "records.json.gz", "header.json", "decisions.json",
                    "RESULTS.md")}))
            with self.assertRaisesRegex(sc.InvalidAllocation, "declaration"):
                g.replay(mock.Mock(output=root, record=None))

    def test_render_is_stable_and_shows_the_figures(self):
        records, _ = attributed_world()
        report = run(records)
        text = g.render(report, {})
        self.assertEqual(g.render(report, {}), text)
        self.assertIn("Decision: **attributed**", text)
        self.assertIn(BR["Cond_rewr.sig"], text)


def declared_data_raw():
    return dict(schema=g.DECLARED_SCHEMA, entries=[
        entry_of("Cond_rewr.sig"), entry_of("Cond_rewr.sml"),
        entry_of("simpLib.sml"), entry_of("congLib.sml", ["load-congLib"])],
        noise=[dict(path=PATHS["Trace.sml"], blob=BLOB["Trace.sml"][0],
                    reason="r", mechanism="shown")], candidate_only=[])


class RecipeTest(unittest.TestCase):
    def test_command_lines(self):
        client = Path("/c/StartupGate.sml")
        self.assertEqual(
            g.command("/h", "hol-startup", client),
            ["/h/bin/hol", "--gcthreads=1", "run", str(client)])
        self.assertEqual(
            g.command("/h", "load-simpLib", client),
            ["/h/bin/hol", "--gcthreads=1", "run",
             "--holstate=/h/bin/hol.state0", str(client)])

    def test_tree_spec(self):
        self.assertEqual(g.split_tree("b1=abc")[:2], ("b1", "abc"))
        with self.assertRaises(sc.InvalidAllocation):
            g.split_tree("=abc")

    def test_hol_build_commands(self):
        """The commands of bootstrap_probe.build_native_hol, in order, in a
        fresh clone: no cache, HOME, the include override, one HOLDIR, and
        a recorded patch applied only after a check."""
        with tempfile.TemporaryDirectory() as raw:
            t = Path(raw)
            repo = t / "repo"
            (repo / "tools-poly").mkdir(parents=True)
            (repo / "f.txt").write_text("one\n")
            (repo / "tools-poly/keep").write_text("k\n")
            git = lambda *c, cwd=repo: subprocess.run(
                ["git", *c], cwd=cwd, check=True, capture_output=True)
            git("init", "-q")
            git("add", ".")
            git("-c", "user.name=t", "-c", "user.email=t@t", "commit",
                "-qm", "x")
            mk = ("f.txt", "one\n", "two\n")
            seen = []

            def run(cmd, cwd=None, runtime_env=None):
                seen.append((cmd, runtime_env))
                if cmd[0] == "git":
                    subprocess.run(cmd, cwd=cwd, check=True,
                                   capture_output=True)
                if cmd[0].endswith("bin/build"):
                    (Path(cwd) / "bin").mkdir()
                    for n in ("hol", "hol.state0", "hol.state", "Holmake"):
                        (Path(cwd) / "bin" / n).write_text(n)
                return {"stdout": ""}
            env = g.tool_env(t)
            hol, prefix = t / "h" / "hol-source", t / "native-install"
            hol.parent.mkdir()
            report = {}
            with mock.patch.dict(os.environ):
                os.environ.pop("GATE_BUILD_DETERMINISTIC", None)
                with mock.patch.object(g, "MKTOOL", mk):
                    g.build_hol(repo, "HEAD", hol, prefix, env, run, report,
                                "mktool")
            self.assertIs(report["hol_build_deterministic"], False)
            self.assertEqual((hol / "f.txt").read_text(), "two\n")
            commands = [c for c, _ in seen]
            self.assertEqual(commands[0][:4],
                             ["git", "clone", "--shared", "--no-checkout"])
            self.assertEqual(commands[1][:2], ["git", "checkout"])
            self.assertEqual(commands[2], [
                str(prefix / "bin/poly"), "--error-exit", "--use",
                "tools/smart-configure.sml"])
            self.assertEqual(commands[3], [
                str(hol / "bin/build"), "--no-cache", "-j2",
                "--seq=tools/sequences/upto-parallel"])
            for _, command_env in seen[2:]:
                self.assertEqual(command_env["HOLDIR"], str(hol))
                self.assertEqual(command_env["HOME"], "/nonexistent")
            self.assertEqual((hol / "tools-poly/poly-includes.ML").read_text(),
                             'val poly = "%s";\nval polymllibdir = "%s";\n'
                             % (prefix / "bin/poly", prefix / "lib"))
            self.assertEqual(report["hol_snapshot"], report["hol_snapshot"])
            self.assertEqual(report["hol_patch"]["name"], "mktool")
            self.assertEqual(report["hol_patch"]["bytes"],
                             len(subprocess.run(
                                 ["git", "diff"], cwd=hol, check=True,
                                 capture_output=True).stdout))

    def test_determinism_edits_touch_image_creation_only(self):
        with tempfile.TemporaryDirectory() as t:
            hol = Path(t)
            subprocess.run(["git", "init", "-q", str(hol)], check=True)
            for name, old, _ in g.DETERMINISM:
                path = hol / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("x\n" + old + "y\n")
            subprocess.run(["git", "-C", str(hol), "add", "-A"], check=True)
            subprocess.run(["git", "-C", str(hol), "-c", "user.name=t",
                            "-c", "user.email=t@t", "commit", "-qm", "m"],
                           check=True)
            diff = g.make_deterministic(hol, None)
            self.assertIn("PolyML.fullGC", diff)
            self.assertEqual(diff.count("--gcthreads=1 buildheap"), 3)
            self.assertEqual(
                sorted(n for n, _, _ in g.DETERMINISM),
                ["src/boss/Holmakefile", "src/num/termination/Holmakefile",
                 "src/proofman/Holmakefile", "tools-poly/hol.ML"])

    def test_polyc_copy_leaves_the_install_alone(self):
        with tempfile.TemporaryDirectory() as t:
            prefix, root = Path(t) / "install", Path(t) / "tree"
            (prefix / "bin").mkdir(parents=True)
            root.mkdir()
            original = ('"${COMPILER}" -q --error-exit\n'
                        'PolyML.export(x)\n')
            (prefix / "bin/polyc").write_text(original)
            (prefix / "bin/poly").write_text("poly")
            before = sorted(p.name for p in prefix.rglob("*"))
            poly, seal = g.deterministic_polyc(prefix, root / "detbin")
            self.assertEqual(sorted(p.name for p in prefix.rglob("*")),
                             before)
            self.assertEqual((prefix / "bin/polyc").read_text(), original)
            self.assertEqual(root / "detbin", poly.parent)
            self.assertIn("--gcthreads=1",
                          (root / "detbin/polyc").read_text())

    def test_mktool_replacement_is_counted(self):
        with tempfile.TemporaryDirectory() as t:
            hol = Path(t)
            subprocess.run(["git", "init", "-q", str(hol)], check=True)
            name, old, _ = g.MKTOOL
            path = hol / name
            path.parent.mkdir(parents=True)
            for text in (old + old, "x\n"):
                path.write_text(text)
                with self.assertRaises(g.sc.InvalidAllocation):
                    g.apply_mktool(hol)
            self.assertEqual(name, "src/portableML/rawtheory/mktool.ML")


class StyleTest(unittest.TestCase):
    def test_files(self):
        for name in ("startup_gate.py", "test_startup_gate.py",
                     "StartupGate.sml", "StartupGateUse.sml"):
            for number, line in enumerate(
                    (HERE / name).read_text().split("\n"), 1):
                where = "%s:%d" % (name, number)
                self.assertNotIn("\t", line, where)
                self.assertEqual(line, line.rstrip(), where)
                self.assertLess(len(line), 80, where)


if __name__ == "__main__":
    unittest.main()
