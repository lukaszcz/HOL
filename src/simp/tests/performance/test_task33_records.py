"""Tests of the TASK33 record validator: canned outputs (well-formed, each
malformed field, each control, each new rule), golden outputs captured from
real probe runs, and ties between the validator's constants and the SML
sources of the probes."""
import copy
import json
import re
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.dont_write_bytecode = True
import task33_records as r

HERE = Path(__file__).resolve().parent
SML = HERE / "task33"
GOLDEN = HERE / "task33_golden"
ROOT = "/snap/base"
SWITCHES = dict(graph_extra=False, leak=False, hook=False)
SEG = r.SEGMENT


def rec(name, probe, kind, **fields):
    return dict(record=name, probe=probe, kind=kind, **fields)


def live(probe, kind, phase, words=1000, share=0, alloc=SEG):
    return rec("live", probe, kind, phase=phase,
               size_heap=8 * words + 3000 + alloc, free_full=3000,
               alloc=alloc, alloc_free=alloc, gc_share=share,
               comparable=True, words=words)


def stale(run, phase):
    """`run` with the allocation area of a live reading not fresh (the
    probe's retries ran out): comparable false."""
    i = find(run, "live", phase=phase)
    return edit(run, i, alloc_free=SEG // 2, comparable=False)


def check(probe, kind, label, value="v"):
    return rec("check", probe, kind, check=label, ok=True, value=value)


def head(probe, kind, params, **switches):
    return rec("probe", probe, kind, holdir=ROOT,
               switches=dict(SWITCHES, **switches), params=params)


def anchored(reps=(5, 5, 5), missing=(), union=10, d=True):
    """The anchored record; d=False: D is not loaded (nothing anchored,
    repeat_ok and total null)."""
    others = [n for n in r.SIZED if n not in r.DECLARED]
    if not d:
        return dict(d=list(r.DECLARED), d_vals=None, total=None,
                    rows=[dict(name=n, vals=None) for n in others],
                    repeat_ok=None)
    total = None if missing else [1000 + r.CONS * len(others) + union
                                  ] * r.REPEATS
    return dict(d=list(r.DECLARED), d_vals=[1000] * r.REPEATS, total=total,
                rows=[dict(name=n, vals=None if n in missing
                           else list(reps)) for n in others],
                repeat_ok=len(set(reps)) == 1)


def registry(probe, kind, hook=False, **kw):
    missing = kw.pop("missing", ())
    return rec("registry", probe, kind, loaded=["Abbrev", "simpLib"],
               files=[["Abbrev.uo", "/snap/sigobj"]],
               listeners=(["t33.hook"] if hook else []) + ["DB"],
               attributes=["userdef"], set_types=["userdef"],
               structures=["A", "B"], signatures=["A"], functors=[],
               sizes=[dict(name=n, struct=None if n in missing else 100 + i,
                           sig=None)
                      for i, n in enumerate(r.SIZED)],
               anchored=kw.get("anchored", anchored(missing=missing)))


def load_run(probe, kind, **switches):
    module = kind[5:] if kind.startswith("load-") else None
    out = [head(probe, kind, dict(module=module), **switches)]
    if kind in r.LOAD_CHECK:
        out += [rec("time", probe, kind, label="load", cpu=0.5, wall=0.6),
                check(probe, kind, r.LOAD_CHECK[kind])]
    if kind == "first-use":
        for label in r.FIRST_USE:
            out += [rec("time", probe, kind, label=label, cpu=1e-5,
                        wall=2e-5), check(probe, kind, label, "v")]
    if probe == "registry":
        out += [live(probe, kind, "registry"),
                registry(probe, kind, switches.get("hook", False))]
    return out + [rec("done", probe, kind)]


def trivial_run(kind="state0-empty"):
    return [head("trivial", kind, dict(module=None)),
            rec("done", "trivial", kind)]


def window(ok=True, gap=10 ** 6):
    """A verified window (status ok) or, with gap=0, an unverifiable one."""
    status = "ok" if ok and gap > r.RESET_SLACK else "unsupported"
    return dict(reset_ok=ok, rss_before=10 ** 8, hwm_before=10 ** 8 + gap,
                rss_reset=10 ** 8, hwm_reset=10 ** 8, rss_after=10 ** 8 + 4096,
                hwm_after=10 ** 8 + 8192, status=status)


def words_of(g, n, extra):
    if g == "cells_cons":
        return 3 * n
    if g == "cells_ref":
        return 5 * n
    return 10 + 7 * n + extra * n


def graph_rows(probe, kind, sizes, extra=0, shares=None, canon_delta=0):
    out = [live(probe, kind, "start")]
    for n in sizes:
        s0, s1, s2, s3 = (shares or {}).get(n, (0, 0, 0, 0))
        out += [check(probe, kind, "%s %d" % (c, n))
                for c in r.GRAPH_CHECKS]
        for g in r.GRAPH_KINDS:
            w = words_of(g, n, extra)
            cw = w - (canon_delta if g == "compiled" else 0)
            a = 5 if g.startswith("cells") else 1000
            out.append(rec("graph", probe, kind, graph=g, n=n, anchor=a,
                           anchor_post=a, union=a + w, words=w, share=s0,
                           canon_anchor=a, canon_anchor_post=a,
                           canon_union=a + cw, canon_words=cw,
                           canon_share=s3))
        out += [live(probe, kind, "graph.%d" % n, 1000 + n),
                rec("phase", probe, kind, n=n, share_start=s0,
                    share_built=s1, share_shared=s2, share_canon=s3,
                    build=window(), rows=window(gap=0))]
    if all(n in sizes for n in r.STEP_SIZES):
        for mode in r.STEP_MODES:
            for g in r.GRAPH_KINDS:
                f = "words" if mode == "built" else "canon_words"
                w = [x[f] for x in (
                    [y for y in out if y["record"] == "graph" and
                     y["graph"] == g and y["n"] == n][0]
                    for n in r.STEP_SIZES)]
                out.append(rec("step", probe, kind, graph=g, mode=mode,
                               first=w[1] - w[0], rest=w[2] - w[1], span=9))
    return out + [live(probe, kind, "end", 900)]


def graph_run_shares(sizes, shares):
    return ([head("graph", "graph", dict(sizes=list(sizes)))] +
            graph_rows("graph", "graph", sizes, shares=shares) +
            [rec("done", "graph", "graph")])


def graph_run(sizes=(0, 1), **switches):
    extra = 3 if switches.get("graph_extra") else 0
    return ([head("graph", "graph", dict(sizes=list(sizes)), **switches)] +
            graph_rows("graph", "graph", sizes, extra) +
            [rec("done", "graph", "graph")])


def release_rows(probe, kind, kinds, m, leak=0):
    out = []
    for k in kinds:
        before = 5000
        after = before + leak * m
        held = after + 600 * m
        out += [live(probe, kind, k + ".before", before),
                live(probe, kind, k + ".after", after),
                live(probe, kind, k + ".held", held),
                rec("release", probe, kind, release=k, m=m, before=before,
                    after=after, held=held)]
    return out


def release_run(m=4, **switches):
    return ([head("release", "release", dict(m=m), **switches),
             live("release", "release", "start")] +
            release_rows("release", "release", r.RELEASE_KINDS, m,
                         1 if switches.get("leak") else 0) +
            [rec("weak", "release", "release",
                 scope="controlled-simpset-ref-closure", retained=True,
                 collected=True, full_gcs=4, status="pass"),
             rec("done", "release", "release")])


def ext_run(m=2, sizes=(0, 1)):
    p = k = "ext"
    return ([head(p, k, dict(m=m, sizes=list(sizes)))] +
            [check(p, k, c) for c in r.EXT_CHECKS] +
            [live(p, k, "ext.start")] +
            release_rows(p, k, r.EXT_RELEASE_KINDS, m) +
            graph_rows(p, k, sizes) +
            [live(p, k, "registry"), registry(p, k), rec("done", p, k)])


def text(records, noise=True):
    lines = []
    for i, x in enumerate(records):
        if noise and i % 3 == 0:
            lines.append("compiler chatter %d" % i)
        lines.append(r.PREFIX + json.dumps(x))
    return "\n".join(lines) + "\n"


def edit(records, index, **fields):
    out = copy.deepcopy(records)
    out[index].update(fields)
    return out


def find(records, name, **match):
    for i, x in enumerate(records):
        if x["record"] == name and all(x.get(k) == v
                                       for k, v in match.items()):
            return i
    raise KeyError((name, match))


class WellFormed(unittest.TestCase):
    def test_load_and_registry_kinds(self):
        for probe in ("load", "registry"):
            for kind in r.LOAD_KINDS:
                summary = r.validate(text(load_run(probe, kind)), root=ROOT)
                self.assertEqual((summary["probe"], summary["kind"]),
                                 (probe, kind))
        s = r.validate(text(load_run("registry", "first-use")))
        self.assertEqual(s["checks"], list(r.FIRST_USE))
        self.assertEqual(sorted(s["times"]), sorted(r.FIRST_USE))
        self.assertEqual(len(s["registry"]["sizes"]), len(r.SIZED))

    def test_trivial_kinds(self):
        for kind in r.STARTUP_KINDS:
            s = r.validate(text(trivial_run(kind)))
            self.assertEqual((s["probe"], s["checks"]), ("trivial", []))
        bad = trivial_run("load-simpLib")
        with self.assertRaises(r.RecordError):
            r.validate(text(bad))

    def test_graph(self):
        s = r.validate(text(graph_run((0, 1, 10))))
        self.assertEqual(sorted(s["graph"]), sorted(r.GRAPH_KINDS))
        self.assertEqual(s["graph"]["cells_ref"][10]["words"], 50)
        self.assertEqual(s["live"]["graph.10"], 1010)
        self.assertEqual(s["phase"][10]["build"]["status"], "ok")
        self.assertEqual(s["phase"][10]["rows"]["status"], "unsupported")
        self.assertEqual(s["share"]["start"], 0)
        self.assertEqual(s["alloc"]["start"], SEG)

    def test_default_sizes(self):
        s = r.validate(text(graph_run(r.DEFAULT_SIZES)))
        self.assertEqual(sorted(s["phase"]), list(r.DEFAULT_SIZES))

    def test_steps(self):
        s = r.validate(text(graph_run((0, 1, 10))))
        step = s["step"]["compiled"]["built"]
        self.assertEqual((step["first"], step["rest"], step["span"]),
                         (7, 63, 9))
        self.assertTrue(step["match"])
        self.assertEqual(sorted(s["step"]), sorted(r.GRAPH_KINDS))
        # without sizes 0, 1 and 10 there are no step records
        s = r.validate(text(graph_run((0, 1, 100))))
        self.assertEqual(s["step"], {})
        s = r.validate(text(graph_run((1, 10))))
        self.assertEqual(s["step"], {})

    def test_step_mismatch_is_reported_not_refused(self):
        run = graph_run((0, 1, 10))
        # the 0 -> 1 step of `compiled` is larger than the per-object step
        for x in run:
            if x["record"] == "graph" and x["graph"] == "compiled" and \
                    x["n"] > 0:
                for a, w in (("union", "words"),
                             ("canon_union", "canon_words")):
                    x[a] += 20
                    x[w] += 20
        for x in run:
            if x["record"] == "step" and x["graph"] == "compiled":
                x["first"] += 20
        s = r.validate(text(run))
        self.assertFalse(s["step"]["compiled"]["built"]["match"])
        self.assertTrue(s["step"]["merge"]["built"]["match"])

    def test_gateable_windows(self):
        shares = {0: (0, 0, 0, 0), 1: (0, 1, 1, 1), 10: (2, 2, 2, 3)}
        run = ([head("graph", "graph", dict(sizes=[0, 1, 10]))] +
               graph_rows("graph", "graph", (0, 1, 10), shares=shares) +
               [rec("done", "graph", "graph")])
        s = r.validate(text(run))
        self.assertEqual(s["gateable"], {
            0: dict(built=True, canonical=True),
            1: dict(built=False, canonical=True),
            10: dict(built=True, canonical=False)})

    def graph_with(self, sizes, shares=None, **moves):
        """A graph run whose `compiled` row at the first size has the
        given fields changed."""
        run = ([head("graph", "graph", dict(sizes=list(sizes)))] +
               graph_rows("graph", "graph", sizes, shares=shares) +
               [rec("done", "graph", "graph")])
        i = find(run, "graph", graph="compiled", n=sizes[0])
        run[i].update(moves)
        return run

    def test_a_moved_anchor_is_data_not_an_error(self):
        s = r.validate(text(self.graph_with((0, 1), anchor_post=1004)))
        self.assertEqual(s["anchor_moved"], [dict(
            kind="compiled", n=0, mode="built", pre=1000, post=1004)])
        self.assertEqual(s["gateable_coverage"]["compiled"], [1])
        self.assertEqual(s["gateable_coverage"]["merge"], [0, 1])
        self.assertTrue(s["gateable"][0]["built"])
        s = r.validate(text(self.graph_with((0, 1), canon_anchor_post=999)))
        self.assertEqual(s["anchor_moved"], [dict(
            kind="compiled", n=0, mode="canonical", pre=1000, post=999)])
        self.assertEqual(s["gateable_coverage"]["compiled"], [0, 1])

    def test_no_move_is_an_empty_list(self):
        s = r.validate(text(graph_run((0, 1, 10))))
        self.assertEqual(s["anchor_moved"], [])
        self.assertEqual(set(s["gateable_coverage"]), set(r.GRAPH_KINDS))
        self.assertTrue(all(v == [0, 1, 10]
                            for v in s["gateable_coverage"].values()))

    def test_the_canonical_pre_anchor_is_checked_whatever_passes_ran(self):
        # share passes inside both windows: the as-built post-anchor and
        # the canonical one are not compared, but the canonical anchor of
        # the rows must still be the canonical pre-anchor
        shares = {0: (0, 1, 1, 2)}
        s = r.validate(text(self.graph_with(
            (0,), shares=shares, anchor_post=1004, canon_anchor_post=999)))
        self.assertEqual(s["anchor_moved"], [])
        self.assertEqual(s["gateable_coverage"]["compiled"], [])
        self.assertEqual(s["gateable_coverage"]["merge"], [])
        run = self.graph_with((0,), shares=shares, canon_anchor=999,
                              canon_union=999 + 7 * 0 + 10 - 0,
                              canon_words=10 - 0)
        s = r.validate(text(run))
        self.assertEqual(s["anchor_moved"], [dict(
            kind="compiled", n=0, mode="canonical", pre=1000, post=999)])

    def test_a_pass_inside_the_window_leaves_the_size_out_of_coverage(self):
        shares = {0: (0, 0, 0, 0), 1: (0, 1, 1, 1)}
        s = r.validate(text(graph_run_shares((0, 1), shares)))
        self.assertEqual(s["gateable_coverage"]["tactic"], [0])

    def test_release(self):
        s = r.validate(text(release_run(4)))
        self.assertEqual(sorted(s["release"]), sorted(r.RELEASE_KINDS))
        self.assertEqual(s["weak"]["status"], "pass")
        self.assertEqual(r.RELEASE_KINDS[0], "noop")
        self.assertEqual(s["residual"]["noop"], 0)
        self.assertEqual(s["held"]["tactic"], 600)

    def test_release_residual_is_exact(self):
        run = release_run(4)
        i = find(run, "release", release="simpset")
        j = find(run, "live", phase="simpset.after")
        run[i]["after"] += 2
        run[j].update(words=run[j]["words"] + 2,
                      size_heap=run[j]["size_heap"] + 16)
        run[i]["held"] += 2
        k = find(run, "live", phase="simpset.held")
        run[k].update(words=run[k]["words"] + 2,
                      size_heap=run[k]["size_heap"] + 16)
        s = r.validate(text(run))
        self.assertEqual(s["residual"]["simpset"], Fraction(1, 2))

    def test_ext(self):
        s = r.validate(text(ext_run()))
        self.assertEqual(sorted(s["release"]), sorted(r.EXT_RELEASE_KINDS))
        self.assertEqual(s["checks"][:3], list(r.EXT_CHECKS))
        self.assertIsNotNone(s["registry"])

    def test_anchored_summary(self):
        s = r.validate(text(load_run("registry", "state-empty")))
        self.assertTrue(s["anchored"]["repeat_ok"])
        self.assertEqual(s["anchored"]["rows"]["simpLib"], [5, 5, 5])
        self.assertEqual(s["anchored"]["total"], [1028] * 3)
        run = load_run("registry", "state-empty")
        i = find(run, "registry")
        run[i]["anchored"] = anchored(reps=(5, 6, 5))
        s = r.validate(text(run))
        self.assertFalse(s["anchored"]["repeat_ok"])
        run[i] = registry("registry", "state-empty", missing=("simpLib",))
        s = r.validate(text(run))
        self.assertIsNone(s["anchored"]["rows"]["simpLib"])
        self.assertTrue(s["anchored"]["repeat_ok"])
        # D not loaded: not applicable, neither repeatable nor not
        run[i] = registry("registry", "state-empty",
                          anchored=anchored(d=False))
        s = r.validate(text(run))
        self.assertIsNone(s["anchored"]["repeat_ok"])
        self.assertIsNone(s["anchored"]["total"])
        self.assertIsNone(s["anchored"]["d"])
        self.assertTrue(all(v is None
                            for v in s["anchored"]["rows"].values()))

    def test_unverified_peak_is_accepted_when_consistent(self):
        run = graph_run((0,))
        i = find(run, "phase")
        weak = window(gap=100)
        s = r.validate(text(edit(run, i, build=weak)))
        self.assertEqual(s["phase"][0]["build"]["status"], "unsupported")
        failed = window(ok=False)
        r.validate(text(edit(run, i, build=failed)))
        null = dict(window(), hwm_after=None, status="unsupported")
        r.validate(text(edit(run, i, build=null)))

    def test_noise_is_ignored(self):
        run = graph_run((0,))
        body = text(run) + "@@MATRIX_RELEASE\t{}\n@@T3\tx\n"
        r.validate(body)


class Malformed(unittest.TestCase):
    def bad(self, body, fragment=None, **kw):
        with self.assertRaises(r.RecordError) as caught:
            r.validate(body, **kw)
        if fragment:
            self.assertIn(fragment, str(caught.exception))

    def line(self, record):
        return r.PREFIX + json.dumps(record) + "\n"

    def test_lines(self):
        run = load_run("load", "state0-empty")
        self.bad("@@T33 " + json.dumps(run[0]) + "\n", "malformed")
        self.bad("@@T33\t{not json}\n", "bad JSON")
        self.bad("@@T33\t[1]\n", "not an object")
        self.bad(r.PREFIX + '{"record":"done","record":"done"}\n',
                 "duplicate")
        self.bad(r.PREFIX + '{"record":"done","probe":"x","kind":"y",'
                 '"n":NaN}\n', "non-finite")
        self.bad("", "first record")
        self.bad(text(run[1:]), "first record")

    def test_fields(self):
        run = graph_run((0,))
        i = find(run, "graph", graph="compiled")
        extra = copy.deepcopy(run)
        extra[i]["more"] = 1
        self.bad(text(extra), "fields")
        for field in ("share", "anchor_post", "canon_union", "canon_share"):
            missing = copy.deepcopy(run)
            del missing[i][field]
            self.bad(text(missing), "fields")
        for field, value in (("n", -1), ("n", True), ("anchor", 1.5),
                             ("graph", 3), ("words", "7"), ("union", None),
                             ("anchor", -1), ("union", -5),
                             ("anchor_post", -1), ("canon_anchor", -1),
                             ("canon_words", 1.5)):
            self.bad(text(edit(run, i, **{field: value})), "bad %s" % field)
        self.bad(text(edit(run, i, record="nonesuch")), "unknown record")
        j = find(run, "check")
        self.bad(text(edit(run, j, ok=1)), "bad ok")
        self.bad(text(edit(run, j, value=None)), "bad value")

    def test_unsigned_fields(self):
        reg = load_run("registry", "state-empty")
        i = find(reg, "registry")
        sizes = copy.deepcopy(reg[i]["sizes"])
        sizes[0]["struct"] = -1
        self.bad(text(edit(reg, i, sizes=sizes)), "bad sizes")
        rel = release_run()
        j = find(rel, "release", release="tactic")
        for field in ("before", "after", "held"):
            self.bad(text(edit(rel, j, **{field: -1})), "bad %s" % field)

    def test_header(self):
        run = load_run("load", "load-simpLib")
        self.bad(text(edit(run, 0, probe="nonesuch")), "unknown probe")
        self.bad(text(edit(run, 0, kind="graph")), "unknown probe")
        self.bad(text(edit(run, 0, switches=dict(leak=False))), "switches")
        self.bad(text(edit(run, 0, switches=dict(SWITCHES, leak=1))),
                 "switches")
        self.bad(text(edit(run, 0, params=dict(module="congLib"))),
                 "bad params")
        self.bad(text(edit(run, 0, params=dict(module=None))), "bad params")
        self.bad(text(run), "holdir", root="/other")
        for params in (dict(sizes=[]), dict(sizes=[1, 1]),
                       dict(sizes=[10, 1]), dict(sizes=[0, -1]), dict()):
            self.bad(text(edit(graph_run((0, 1)), 0, params=params)),
                     "bad params")
        for params in (dict(m=0), dict(m=-3), dict(m=1.5), dict(n=1)):
            self.bad(text(edit(release_run(), 0, params=params)),
                     "bad params")

    def test_sequence(self):
        run = graph_run((0, 1))
        i = find(run, "graph", graph="merge", n=1)
        self.bad(text(run[:i] + run[i + 1:]), "expected")
        self.bad(text(run[:i] + [run[i]] + run[i:]), "expected")
        swapped = run[:i] + [run[i + 1], run[i]] + run[i + 2:]
        self.bad(text(swapped), "expected")
        self.bad(text(run[:-1]), "expected")
        self.bad(text(run + [run[-1]]), "expected")
        wrong = edit(run, i, kind="release")
        self.bad(text(wrong), "inside")
        rel = release_run()
        self.bad(text(rel[:-2] + rel[-1:]), "expected")
        ext = ext_run()
        self.bad(text([x for x in ext if x["record"] != "registry"]),
                 "expected")
        full = graph_run((0, 1, 10))
        self.bad(text([x for x in full if x["record"] != "step"]),
                 "expected")
        self.bad(text(graph_run((0, 1))[:-2] + [
            rec("step", "graph", "graph", graph="fragment", mode="built",
                first=1, rest=2, span=9)] + graph_run((0, 1))[-2:]),
                 "expected")

    def test_extra_record_is_named_in_the_message(self):
        run = graph_run((0,))
        extra = rec("time", "graph", "graph", label="zz", cpu=1, wall=1)
        self.bad(text(run + [extra]), "next ('time', 'zz')")
        self.bad(text(run[:-1]), "next ('done',)")

    def test_failed_check(self):
        run = load_run("load", "load-simpLib")
        i = find(run, "check")
        self.bad(text(edit(run, i, ok=False)), "failed check")
        with self.assertRaises(r.RecordError):
            r.normalized_checks(text(edit(run, i, ok=False)))

    def test_live(self):
        run = graph_run((0,))
        i = find(run, "live", phase="graph.0")
        # the flag must say what the allocation area says
        self.bad(text(edit(run, i, alloc_free=SEG - 1)), "comparable")
        self.bad(text(edit(run, i, comparable=False)), "comparable")
        self.bad(text(edit(run, i, comparable=1)), "comparable")
        self.bad(text(edit(run, i, words=run[i]["words"] + 1)), "formula")
        self.bad(text(edit(run, i, size_heap=100, words=-300)), "formula")
        self.bad(text(edit(run, i, gc_share=-1)), "gc_share")
        half = SEG // 2
        self.bad(text(edit(run, i, alloc=half, alloc_free=half,
                           size_heap=run[i]["size_heap"] - half)),
                 "comparable")
        double = 2 * SEG
        ok = edit(run, i, alloc=double, alloc_free=double,
                  size_heap=run[i]["size_heap"] + SEG)
        r.validate(text(ok))

    def test_graph_arithmetic(self):
        run = graph_run((1,))
        i = find(run, "graph", graph="compiled")
        row = run[i]
        self.bad(text(edit(run, i, union=row["anchor"] - 1,
                           words=-1)), "union")
        self.bad(text(edit(run, i, words=row["words"] + 1)), "union")
        self.bad(text(edit(run, i, canon_words=row["canon_words"] + 1)),
                 "canonical")
        self.bad(text(edit(run, i, canon_union=row["canon_anchor"] - 1,
                           canon_words=-1)), "canonical")
        c = find(run, "graph", graph="cells_cons")
        self.bad(text(edit(run, c, union=run[c]["union"] + 1,
                           words=run[c]["words"] + 1)), "3 per input")
        self.bad(text(edit(run, c, canon_union=run[c]["canon_union"] + 1,
                           canon_words=run[c]["canon_words"] + 1)),
                 "3 per input")
        f = find(run, "graph", graph="cells_ref")
        self.bad(text(edit(run, f, union=run[f]["union"] + 1,
                           words=run[f]["words"] + 1)), "2 words")
        self.bad(text(edit(run, f, anchor=6, union=run[f]["union"] + 1)),
                 "anchors")
        self.bad(text(edit(run, f, canon_anchor=6,
                           canon_union=run[f]["canon_union"] + 1)),
                 "anchors")

    def test_share_counts(self):
        shares = {0: (0, 5, 5, 10)}
        run = ([head("graph", "graph", dict(sizes=[0]))] +
               graph_rows("graph", "graph", (0,), shares=shares) +
               [rec("done", "graph", "graph")])
        r.validate(text(run))
        p = find(run, "phase")
        self.bad(text(edit(run, p, share_built=6, share_shared=5)),
                 "share counts decrease")
        i = find(run, "graph", graph="merge")
        self.bad(text(edit(run, i, share=7)), "outside its window")
        self.bad(text(edit(run, i, canon_share=9)), "canon_share")
        self.bad(text(edit(run, i, share=11)), "share counts decrease")

    def test_steps(self):
        run = graph_run((0, 1, 10))
        i = find(run, "step", graph="compiled", mode="built")
        self.bad(text(edit(run, i, first=run[i]["first"] + 1)),
                 "disagrees with the rows")
        self.bad(text(edit(run, i, rest=run[i]["rest"] - 1)),
                 "disagrees with the rows")
        self.bad(text(edit(run, i, span=8)), "bad mode or span")
        self.bad(text(edit(run, i, mode="other")), "expected")

    def test_phase_windows(self):
        run = graph_run((0,))
        i = find(run, "phase")
        for name in ("build", "rows"):
            good = run[i][name]
            self.bad(text(edit(run, i, **{name: dict(
                good, status="unsupported" if good["status"] == "ok"
                else "ok")})), "status")
            self.bad(text(edit(run, i, **{name: dict(good, hwm_after=1)})),
                     "VmHWM below VmRSS")
            self.bad(text(edit(run, i, **{name: dict(good, bogus=1)})),
                     "bad %s" % name)
        build = run[i]["build"]
        # a failed write cannot give status ok, even with good readings
        self.bad(text(edit(run, i, build=dict(build, reset_ok=False))),
                 "status")
        # nothing to reset: hwm = rss before it, so it is not verified
        self.bad(text(edit(run, i, build=dict(
            build, hwm_before=build["rss_before"]))), "status")
        gap = r.RESET_SLACK
        self.bad(text(edit(run, i, build=dict(
            build, hwm_before=build["rss_before"] + gap))), "status")
        r.validate(text(edit(run, i, build=dict(
            build, hwm_before=build["rss_before"] + gap + 1))))
        # the reset did not take
        self.bad(text(edit(run, i, build=dict(
            build, hwm_reset=build["rss_reset"] + gap + 1))), "status")
        self.bad(text(edit(run, i, build=dict(build, rss_before=None))),
                 "status")
        self.bad(text(edit(run, i, n=1)), "expected")

    def test_release(self):
        run = release_run(4)
        i = find(run, "release", release="tactic")
        self.bad(text(edit(run, i, after=run[i]["after"] + 1)),
                 "differs from its live")
        self.bad(text(edit(run, i, m=5)), "declared")
        w = find(run, "weak")
        self.bad(text(edit(run, w, collected=False)), "weak")
        self.bad(text(edit(run, w, status="maybe")), "weak")
        self.bad(text(edit(run, w, retained=False)), "weak")
        for n in (0, 3):
            self.bad(text(edit(run, w, full_gcs=n)), "at least 4")
        r.validate(text(edit(run, w, full_gcs=r.WEAK_MIN_FULL_GCS)))

    def test_registry(self):
        run = load_run("registry", "state-empty")
        i = find(run, "registry")
        self.bad(text(edit(run, i, listeners=["t33.hook", "DB"])),
                 "hook switch")
        self.bad(text(edit(run, i, structures=["B", "A"])), "sorted")
        sizes = copy.deepcopy(run[i]["sizes"])
        self.bad(text(edit(run, i, sizes=sizes[:-1])), "sizes")
        self.bad(text(edit(run, i, sizes=[dict(name="x")])), "sizes")
        self.bad(text(edit(run, i, files=[["a"]])), "files")
        self.bad(text(edit(run, i, loaded=["a", 1])), "loaded")

    def test_anchored_rules(self):
        run = load_run("registry", "state-empty")
        i = find(run, "registry")
        good = run[i]["anchored"]

        def with_(**kw):
            return text(edit(run, i, anchored=dict(good, **kw)))
        self.bad(with_(d=["ThmAttribute"]), "anchor set")
        self.bad(with_(rows=good["rows"][:-1]), "anchored rows")
        self.bad(with_(repeat_ok=False), "repeat_ok")
        self.bad(with_(d_vals=[1000, 1000]), "repeats")
        self.bad(with_(d_vals=None), "disagree")
        rows = copy.deepcopy(good["rows"])
        rows[0]["vals"] = [5, 5]
        self.bad(with_(rows=rows), "repeats")
        rows[0]["vals"] = None
        self.bad(with_(rows=rows), "disagree")
        self.bad(with_(d_vals=[1, 2, 1], total=[29, 30, 29], repeat_ok=True),
                 "repeat_ok")
        self.bad(with_(extra=1), "bad anchored")
        # the closure total U: presence, repeats, bounds
        self.bad(with_(total=None), "total and the anchored")
        self.bad(with_(total=[1028, 1028]), "total has 2 repeats")
        self.bad(with_(total=[1028, 1029, 1028], repeat_ok=True),
                 "repeat_ok")
        self.bad(with_(total=[1004] * 3), "between the largest")
        self.bad(with_(total=[1018 + 31] * 3), "between the largest")
        r.validate(text(edit(run, i, anchored=dict(
            good, total=[1018 + 5] * 3))))
        r.validate(text(edit(run, i, anchored=dict(
            good, total=[1018 + 30] * 3))))
        # a structure that is missing has no anchored values
        miss = load_run("registry", "state-empty")
        miss[i] = registry("registry", "state-empty", missing=("simpLib",))
        r.validate(text(miss))
        bad = copy.deepcopy(miss)
        bad[i]["anchored"]["rows"][0]["vals"] = [5, 5, 5]
        self.bad(text(bad), "disagree")
        bad = copy.deepcopy(miss)
        bad[i]["anchored"]["total"] = [1028] * 3
        self.bad(text(bad), "total and the anchored")


class Comparable(unittest.TestCase):
    def raises(self, run, kind):
        with self.assertRaises(r.NotComparable) as caught:
            r.validate(text(run))
        self.assertIn(kind, str(caught.exception))
        self.assertNotIsInstance(caught.exception, r.RecordError)

    def test_gc_share_differs_inside_a_kind(self):
        run = release_run(4)
        i = find(run, "live", phase="tactic.after")
        self.raises(edit(run, i, gc_share=1), "tactic")

    def test_alloc_differs_inside_a_kind(self):
        run = release_run(4)
        i = find(run, "live", phase="noop.after")
        big = 2 * SEG
        run[i].update(alloc=big, alloc_free=big,
                      size_heap=run[i]["size_heap"] + SEG)
        self.raises(run, "noop")

    def test_a_stale_allocation_area_is_not_comparable(self):
        # emitted with comparable false, not a failed process
        for phase in ("start", "tactic.before", "tactic.after"):
            self.raises(stale(release_run(4), phase), phase)
        self.raises(stale(graph_run((0, 1)), "graph.1"), "graph.1")
        self.raises(stale(load_run("registry", "state-empty"), "registry"),
                    "registry")
        self.raises(stale(ext_run(), "ext_views.after"), "ext_views.after")

    def test_the_held_reading_only_clears_held_comparable(self):
        s = r.validate(text(release_run(4)))
        self.assertTrue(all(s["held_comparable"].values()))
        self.assertEqual(sorted(s["held_comparable"]),
                         sorted(r.RELEASE_KINDS))
        run = release_run(4)
        i = find(run, "live", phase="removed.held")
        s = r.validate(text(edit(run, i, gc_share=3)))
        self.assertFalse(s["held_comparable"]["removed"])
        self.assertTrue(s["held_comparable"]["cong"])
        big = 2 * SEG
        j = find(run, "live", phase="noop.held")
        run[j].update(alloc=big, alloc_free=big,
                      size_heap=run[j]["size_heap"] + SEG)
        s = r.validate(text(run))
        self.assertFalse(s["held_comparable"]["noop"])
        s = r.validate(text(stale(release_run(4), "tactic.held")))
        self.assertFalse(s["held_comparable"]["tactic"])
        self.assertEqual(s["held"]["tactic"], 600)

    def test_graph_and_registry_probes_have_no_held_comparable(self):
        self.assertEqual(r.validate(text(graph_run((0,))))[
            "held_comparable"], {})

    def test_differences_between_kinds_are_comparable(self):
        run = release_run(4)
        for k in ("cong", "removed"):
            for phase in (".before", ".after", ".held"):
                i = find(run, "live", phase=k + phase)
                run[i]["gc_share"] = 2 if k == "cong" else 1
        r.validate(text(run))

    def test_ext_release_kinds_are_checked_too(self):
        run = ext_run()
        i = find(run, "live", phase="ext_views.after")
        self.raises(edit(run, i, gc_share=9), "ext_views")

    def test_malformed_wins_over_not_comparable(self):
        run = release_run(4)
        i = find(run, "live", phase="tactic.after")
        run = edit(run, i, gc_share=1)
        j = find(run, "release", release="cong")
        with self.assertRaises(r.RecordError):
            r.validate(text(edit(run, j, m=9)))


class Controls(unittest.TestCase):
    def test_switches_are_visible_and_expected(self):
        probes = dict(graph_extra=graph_run, leak=release_run)
        for name, make in probes.items():
            run = make((0,), **{name: True}) if name == "graph_extra" \
                else make(4, **{name: True})
            with self.assertRaises(r.RecordError) as caught:
                r.validate(text(run))
            self.assertIn(name, str(caught.exception))
            s = r.validate(text(run), controls=(name,))
            self.assertTrue(s["switches"][name])
            self.assertEqual(sum(s["switches"].values()), 1)

    def test_an_expected_control_must_be_active(self):
        for run in (graph_run((0,)), release_run(4)):
            with self.assertRaises(r.RecordError) as caught:
                r.validate(text(run), controls=("leak",))
            self.assertIn("expected leak", str(caught.exception))

    def test_a_different_control_is_refused(self):
        run = release_run(4, leak=True)
        with self.assertRaises(r.RecordError):
            r.validate(text(run), controls=("graph_extra",))
        with self.assertRaises(r.RecordError):
            r.validate(text(run), controls=("leak", "hook"))
        with self.assertRaises(r.RecordError):
            r.validate(text(run), controls=("nonesuch",))

    def test_an_inert_control_is_refused(self):
        # T33_LEAK in a graph run, T33_GRAPH_EXTRA in a release run: the
        # probe records the switch but the probe never uses it
        graph = graph_run((0,), leak=True)
        with self.assertRaises(r.RecordError) as caught:
            r.validate(text(graph), controls=("leak",))
        self.assertIn("inert", str(caught.exception))
        release = release_run(4, graph_extra=True)
        with self.assertRaises(r.RecordError) as caught:
            r.validate(text(release), controls=("graph_extra",))
        self.assertIn("inert", str(caught.exception))
        run = load_run("load", "state-empty", hook=True)
        with self.assertRaises(r.RecordError):
            r.validate(text(run), controls=("hook",))

    def test_leak_in_release_rows(self):
        s = r.validate(text(release_run(4, leak=True)), controls=("leak",))
        self.assertEqual(s["residual"]["tactic"], 1)
        self.assertEqual(s["residual"]["noop"], 1)
        clean = r.validate(text(release_run(4)))
        self.assertEqual(clean["residual"]["tactic"], 0)

    def test_hook_in_registry(self):
        run = load_run("registry", "state-empty", hook=True)
        s = r.validate(text(run), controls=("hook",))
        self.assertIn(r.HOOK_NAME, s["registry"]["listeners"])
        self.assertTrue(s["switches"]["hook"])
        self.assertNotIn(r.HOOK_NAME, r.validate(text(load_run(
            "registry", "state-empty")))["registry"]["listeners"])
        s = r.validate(text(ext_run()))
        self.assertFalse(s["switches"]["hook"])

    def test_graph_extra_in_rows(self):
        s = r.validate(text(graph_run((0, 10), graph_extra=True)),
                       controls=("graph_extra",))
        plain = r.validate(text(graph_run((0, 10))))
        self.assertEqual(s["graph"]["compiled"][10]["words"] -
                         plain["graph"]["compiled"][10]["words"], 30)
        self.assertEqual(s["graph"]["cells_cons"][10]["words"], 30)

    def test_controls_apply_to_the_probes_that_show_them(self):
        for name, probes in r.CONTROL_PROBES.items():
            self.assertTrue(set(probes) <= set(r.PROBE_KINDS))
        self.assertEqual(set(r.CONTROL_PROBES), set(r.SWITCHES))


class Digest(unittest.TestCase):
    def test_normalized_checks(self):
        run = load_run("load", "first-use")
        lines = r.normalized_checks(text(run))
        self.assertEqual(lines, ["load\tfirst-use\t%s\tv" % c
                                 for c in r.FIRST_USE])
        self.assertEqual(r.normalized_checks(text(load_run(
            "load", "state-empty"))), [])

    def test_digest_ignores_timing_and_noise(self):
        run = load_run("load", "load-simpLib")
        other = copy.deepcopy(run)
        other[find(other, "time")].update(cpu=9.5, wall=9.9)
        self.assertEqual(r.digest(text(run)),
                         r.digest(text(other, noise=False)))
        self.assertEqual(len(r.digest(text(run))), 64)

    def test_digest_changes_with_a_check(self):
        run = load_run("load", "first-use")
        other = edit(run, find(run, "check", check="first-tac"), value="w")
        self.assertNotEqual(r.digest(text(run)), r.digest(text(other)))
        other = edit(run, find(run, "check", check="first-tac"),
                     check="second-tac")
        self.assertNotEqual(r.digest(text(run)), r.digest(text(other)))

    def test_digest_is_strict(self):
        with self.assertRaises(r.RecordError):
            r.digest("@@T33\t{bad\n")


class Masking(unittest.TestCase):
    ROOT = "/dev/shm/x/snap/base"
    PROBE = "/dev/shm/x/probe-base"

    def test_the_rule_is_the_downstream_drivers(self):
        # one rule, in the sealed task32_downstream.py (TASK32 replay runs
        # it); a misplaced prefix is a RecordError here
        import task32_downstream as d
        self.assertEqual(r.ROOT_MASK, d.ROOT_MASK)
        self.assertEqual(r.PROBE_MASK, d.PROBE_MASK)
        self.assertEqual(r.mask_path(self.ROOT + "/x", self.ROOT,
                                     self.PROBE),
                         d.mask_path(self.ROOT + "/x", self.ROOT,
                                     self.PROBE))
        with self.assertRaises(d.MaskError):
            d.mask_path(self.ROOT + "2", self.ROOT, self.PROBE)
        with self.assertRaises(r.RecordError):
            r.mask_path(self.ROOT + "2", self.ROOT, self.PROBE)
        with self.assertRaises(AttributeError):
            r.NO_SUCH_MASK

    def path(self, p):
        return r.mask_path(p, self.ROOT, self.PROBE)

    def text(self, t):
        return r.mask_text(t, self.ROOT, self.PROBE)

    def test_paths(self):
        self.assertEqual(self.path(self.ROOT), "<ROOT>")
        self.assertEqual(self.path(self.ROOT + "/src/simp"),
                         "<ROOT>/src/simp")
        self.assertEqual(self.path(self.PROBE), "<PROBE>")
        self.assertEqual(self.path(self.PROBE + "/sub"), "<PROBE>/sub")
        self.assertEqual(self.path("/elsewhere/x"), "/elsewhere/x")

    def test_misplaced_paths_are_refused(self):
        for bad in (self.ROOT + "2/src", self.ROOT + "-old",
                    "/tmp" + self.ROOT, "/a/" + self.PROBE,
                    self.PROBE + ".bak"):
            with self.assertRaises(r.RecordError, msg=bad):
                self.path(bad)

    def test_text(self):
        body = '{"holdir":"%s","at":"%s/T33.sml","x":"%s"}' % (
            self.ROOT, self.PROBE, self.ROOT + "/a")
        self.assertEqual(
            self.text(body),
            '{"holdir":"<ROOT>","at":"<PROBE>/T33.sml","x":"<ROOT>/a"}')
        self.assertEqual(self.text("no paths"), "no paths")

    def test_misplaced_text_is_refused(self):
        for bad in ("at %s2/x" % self.ROOT, "at /q%s/x" % self.ROOT,
                    "at %s.d" % self.PROBE, "at x%s" % self.PROBE):
            with self.assertRaises(r.RecordError, msg=bad):
                self.text(bad)

    def test_nested_probe_directory_masks_by_the_longer_first(self):
        got = r.mask_text("a /r/x/probe/y b /r/x/z", "/r/x", "/r/x/probe")
        self.assertEqual(got, "a <PROBE>/y b <ROOT>/z")


def golden(name):
    """A real probe output (task33_golden/NAME.txt): the TAB after @@T33 is
    stored as a space (no TAB in the repository), the snapshot root is
    masked, and the probe directory does not occur in it."""
    body = (GOLDEN / (name + ".txt")).read_text(encoding="utf-8")
    out = []
    for line in body.splitlines():
        if line.startswith("@@T33 "):
            line = r.PREFIX + line[len("@@T33 "):]
        out.append(line.replace("@ROOT@", ROOT))
    return "\n".join(out) + "\n"


class Golden(unittest.TestCase):
    def test_graph(self):
        s = r.validate(golden("graph"), root=ROOT)
        self.assertEqual(s["params"]["sizes"], [0, 1, 10])
        self.assertEqual(sorted(s["step"]), sorted(r.GRAPH_KINDS))
        self.assertTrue(all(g["built"] and g["canonical"]
                            for g in s["gateable"].values()))
        for g, rows in s["graph"].items():
            for n, row in rows.items():
                self.assertLessEqual(row["anchor"], row["union"])
        cells = s["graph"]["cells_cons"][10]
        self.assertEqual((cells["words"], cells["canon_words"]), (30, 30))
        self.assertEqual(s["graph"]["cells_ref"][10]["words"], 50)
        self.assertEqual(len(r.normalized_checks(golden("graph"))),
                         len(r.GRAPH_CHECKS) * 3)
        self.assertEqual(s["phase"][0]["build"]["status"], "ok")
        self.assertEqual(s["anchor_moved"], [])
        self.assertEqual(s["gateable_coverage"]["tactic"], [0, 1, 10])

    def test_release(self):
        s = r.validate(golden("release"), root=ROOT)
        self.assertEqual(s["params"], {"m": 3})
        self.assertEqual(sorted(s["release"]), sorted(r.RELEASE_KINDS))
        self.assertEqual(s["residual"]["noop"], 0)
        self.assertEqual(s["weak"]["status"], "pass")
        self.assertEqual(set(s["alloc"].values()), {SEG})
        self.assertTrue(all(s["held_comparable"].values()))

    def test_first_use(self):
        text_ = golden("first-use")
        s = r.validate(text_, root=ROOT)
        self.assertEqual(s["checks"], list(r.FIRST_USE))
        for label in r.FIRST_USE:
            self.assertGreater(s["times"][label]["cpu"], 0)
        lines = r.normalized_checks(text_)
        self.assertTrue(all(len(x.split("\t")) == 4 for x in lines))
        self.assertIn("T", lines[0].split("\t")[3])
        self.assertEqual(len(r.digest(text_)), 64)

    def test_the_noise_line_of_a_real_release_run_is_ignored(self):
        body = golden("release")
        self.assertIn("@@MATRIX_RELEASE", body)

    def test_golden_is_sensitive(self):
        body = golden("graph")
        lines = body.splitlines()
        i = next(k for k, x in enumerate(lines)
                 if '"graph":"tactic","n":10' in x)
        record = json.loads(lines[i][len(r.PREFIX):])
        record["words"] += 1
        lines[i] = r.PREFIX + json.dumps(record)
        with self.assertRaises(r.RecordError):
            r.validate("\n".join(lines) + "\n")
        with self.assertRaises(r.RecordError):
            r.validate("\n".join(body.splitlines()[:-1]) + "\n")

    def test_real_real_formats(self):
        # Real.fmt (SCI (SOME 12)) with `~` mapped to `-`, as the probes
        # print it: exponent 00, negative exponents, a zero
        for number in ("0.000000000000E00", "6.100000000000E-5",
                       "8.767260000000E-1", "1.234567890123E01"):
            self.assertIsInstance(json.loads(number), float)
        self.assertIn("E-5", golden("first-use"))
        body = text(load_run("load", "load-simpLib"))
        body = body.replace('"cpu": 0.5', '"cpu": 0.000000000000E00')
        r.validate(body)


class Ties(unittest.TestCase):
    """The validator's constants against the SML text of the probes."""

    def src(self, name):
        return (SML / name).read_text(encoding="utf-8")

    def names(self, name, pattern):
        return re.findall(pattern, self.src(name))

    def test_probe_sources_are_the_directory(self):
        listing = sorted(p.name for p in SML.iterdir()
                         if p.suffix in (".sml", ".ML"))
        self.assertEqual(sorted(r.PROBE_SOURCES), listing)
        for target in r.PROBE_TARGETS.values():
            self.assertIn(target[:-3] + ".sml", listing)
        self.assertEqual(sorted(r.PROBE_TARGETS),
                         sorted(r.PROBE_KINDS))
        for name in r.PROBE_REUSED:
            self.assertTrue((HERE / name).is_file())

    def test_probe_sources_are_ascii_and_clean(self):
        for name in r.PROBE_SOURCES:
            body = (SML / name).read_bytes()
            self.assertEqual([b for b in body if b > 127], [], name)
            self.assertNotIn(b"\t", body, name)
            for line in body.decode().splitlines():
                self.assertEqual(line, line.rstrip(), name)
                self.assertLess(len(line), 80, name)

    def test_structure_list(self):
        body = self.src("T33.sml")
        sized = re.search(r"val sized = \[(.*?)\]", body, re.S).group(1)
        self.assertEqual(tuple(re.findall(r'"(\w+)"', sized)), r.SIZED)
        declared = re.search(r"val declared = \[(.*?)\]", body, re.S)
        self.assertEqual(tuple(re.findall(r'"(\w+)"', declared.group(1))),
                         r.DECLARED)
        self.assertEqual(r.DECLARED, r.SIZED[:len(r.DECLARED)])
        self.assertIn("val repeats = %d" % r.REPEATS, body)

    def test_constants(self):
        self.assertIn("val slack = %d" % r.RESET_SLACK,
                      self.src("T33GraphLib.sml"))
        self.assertIn("val segment = %d" % r.SEGMENT, self.src("T33.sml"))
        self.assertIn("val default_sizes = [%s]" % ", ".join(
            map(str, r.DEFAULT_SIZES)), self.src("T33GraphLib.sml"))
        self.assertIn('("span", T33.ji %d)' % r.STEP_SPAN,
                      self.src("T33GraphLib.sml"))
        self.assertEqual(r.STEP_SPAN, r.STEP_SIZES[2] - r.STEP_SIZES[1])
        self.assertIn('"%s"' % r.HOOK_NAME, self.src("T33.sml"))
        self.assertEqual(tuple(self.names("T33.sml",
                                          r'switch "(T33_\w+)"')),
                         r.CONTROLS)
        sw = re.search(r"val switches_json = (.*?)\n\n", self.src("T33.sml"),
                       re.S).group(1)
        self.assertEqual(tuple(re.findall(r'\("(\w+)", jb', sw)),
                         r.SWITCHES)
        self.assertEqual(len(r.CONTROLS), len(r.SWITCHES))
        load = self.src("T33Load.sml")
        self.assertIn("{" + ",".join('\\"%s\\":false' % x
                                     for x in r.SWITCHES) + "}", load)
        trivial = self.src("T33Trivial.sml")
        for x in r.SWITCHES:
            self.assertIn('\\"%s\\":false' % x, trivial)

    def test_graph_rows_and_checks(self):
        body = self.src("T33GraphLib.sml")
        block = body[body.index("val anchor_rows"):body.index("fun anchors")]
        self.assertEqual(tuple(re.findall(r'\("(\w+)", fn', block)),
                         r.GRAPH_KINDS)
        union = body[body.index("val union_rows"):body.index("fun unions")]
        self.assertEqual(union.count("fn () =>"), len(r.GRAPH_KINDS))
        self.assertEqual(tuple(re.findall(r'chk "(\w+)"', body)),
                         r.GRAPH_CHECKS)
        modes = re.findall(r'emit_step "(\w+)"', body)
        self.assertEqual(tuple(modes), r.STEP_MODES)
        self.assertEqual(sorted(set(re.findall(r'words (\d+) label', body))),
                         sorted(str(n) for n in r.STEP_SIZES))
        self.assertEqual(tuple(re.findall(r'\("(\w+)", T33.jopt T33.jn',
                                          body)), r.WINDOW_FIELDS)

    def test_record_fields(self):
        graph = self.src("T33GraphLib.sml")
        row = graph[graph.index("fun row "):graph.index("val labels")]
        self.assertEqual(
            set(re.findall(r'\("(\w+)", T33', row)),
            set(r.FIELDS["graph"]) - {"n"} | {"n"})
        phase = graph[graph.index('T33.emit "phase"'):]
        self.assertEqual(
            set(re.findall(r'\("(\w+)", ', phase[:phase.index("(n,")])),
            set(r.FIELDS["phase"]))
        steps = graph[graph.index('T33.emit "step"'):]
        self.assertEqual(
            set(re.findall(r'\("(\w+)", ', steps[:steps.index("| _")])),
            set(r.FIELDS["step"]))
        t33 = self.src("T33.sml")
        live_ = t33[t33.index('emit "live"'):t33.index("words\n  end")]
        self.assertEqual(set(re.findall(r'\("(\w+)", ', live_)),
                         set(r.FIELDS["live"]))
        reg = t33[t33.index('emit "registry"'):t33.index("end\nend")]
        self.assertEqual(set(re.findall(r'\("(\w+)", ', reg)),
                         set(r.FIELDS["registry"]))
        anc = t33[t33.index('jo [("d"'):t33.index("fun registry")]
        self.assertEqual(
            set(re.findall(r'\("(\w+)", ', anc)),
            {"d", "d_vals", "total", "rows", "name", "vals",
             "repeat_ok"})

    def test_kinds(self):
        body = self.src("T33Release.sml")
        kinds = body[body.index("val kinds"):body.index("val m =")]
        got = [a or b for a, b in re.findall(
            r'\("(\w+)", fn|conv_kind "(\w+)"', kinds)]
        self.assertEqual(tuple(got), r.RELEASE_KINDS)
        ext = self.src("T33ExtUse.ML")
        got = re.findall(r'\("((?:ext_)?\w+)", fn', ext)
        self.assertEqual(tuple(got), r.EXT_RELEASE_KINDS)
        self.assertEqual(tuple(re.findall(r'proof "(ext \w+)"', ext)),
                         r.EXT_CHECKS)

    def test_load_kinds(self):
        kind = self.src("T33Kind.ML")
        self.assertEqual(tuple(re.findall(r'"([\w-]+)" =>', kind)),
                         r.LOAD_KINDS)
        self.assertEqual(r.STARTUP_KINDS, r.LOAD_KINDS[:2])
        simp = self.src("T33CheckSimp.ML")
        cong = self.src("T33CheckCong.ML")
        self.assertIn('t33_check "%s"' % r.LOAD_CHECK["load-simpLib"], simp)
        self.assertIn('t33_check "%s"' % r.LOAD_CHECK["load-congLib"], cong)
        first = self.src("T33CheckFirst.ML")
        self.assertEqual(tuple(re.findall(r'(?:conv|tac) "([\w-]+)"',
                                          first)), r.FIRST_USE)
        for name, source in (("simpLib", "T33CheckSimp.ML"),
                             ("congLib", "T33CheckCong.ML")):
            self.assertIn('t33_loading "%s" "%s"' % (name, source), kind)
        self.assertIn('"first-use" => QUse.use "T33CheckFirst.ML"', kind)

    def test_timing_probes_use_no_support_code(self):
        # the timed probes must not mention the T33 support structure
        for name in ("T33Load.sml", "T33Trivial.sml", "T33Kind.ML",
                     "T33CheckSimp.ML", "T33CheckCong.ML",
                     "T33CheckFirst.ML"):
            self.assertNotRegex(self.src(name), r"\bT33\.", name)
        self.assertIn('QUse.use "T33Kind.ML"', self.src("T33Load.sml"))
        # the module name is never a static reference in a probe source
        for name in r.PROBE_SOURCES:
            self.assertNotRegex(self.src(name),
                                r"\b(simpLib|congLib)\.[a-zA-Z]"
                                if name in ("T33Load.sml", "T33Kind.ML",
                                            "T33Trivial.sml") else
                                r"\Z\A", name)

    def test_probe_names(self):
        probes = dict(load="T33Load.sml", trivial="T33Trivial.sml",
                      registry="T33Registry.sml", graph="T33Graph.sml",
                      release="T33Release.sml", ext="T33Ext.sml")
        for probe, source in probes.items():
            body = self.src(source)
            self.assertTrue('"%s"' % probe in body or
                            '\\"%s\\"' % probe in body, source)
        self.assertEqual(sorted(probes), sorted(r.PROBE_KINDS))

    def test_schema_name(self):
        self.assertEqual(r.SCHEMA, "task33-records-v4")


if __name__ == "__main__":
    unittest.main()
