"""The decisions of the TASK33 storage cases (design §1, §8.1, §8.3, §8.4),
as pure functions of validated process summaries (`task33_records.validate`):
no process, no file, no ledger. The storage driver (task33_storage.py) runs
the processes and calls these; its replay calls them again on the archived
receipts, so a run and its replay decide alike.

A rule takes the summaries of the baseline side (`base`) and of the
candidate side (`cand`), each a list: k = 3 fresh processes per side (order
B C C B B C) for the exact mode, or 10 aligned pairs (the contingency stage)
for the paired mode. It returns rows, dicts with `case`, `kind`, `decision`
(pass, fail, inconclusive, blocked; `reported` and `unsupported` rows are
not gates), `reason` and its numbers; `owed` is None, "extend" (a value is
not repeatable within a side: the 10-pair zero-margin stage) or "followup"
(R1 is unresolved: a larger M). A row never says more than the numbers
show: "unstable" values are not judged, they are owed the next stage.

  S1  per graph kind: the canonical rows (`canon_words`) are exact within a
      side over the k processes and the candidate is at most the baseline
      at every size and every adjacent slope (words per rule); the as-built
      rows (`words`) are gated the same way only where every process of
      both sides had no GC share pass in the window (`gateable`) and the
      values repeat, else reported; the step match (0->1 against 1->10) is
      reported only (§8.3). Paired mode: `acceptance.paired_statistics`
      at zero margin per series.
  S2  per registry kind on hol.state: the closure total U (the anchored
      structures D plus the others) changes baseline to candidate by
      exactly the declared `total_delta`, no exclusive part grows, and
      every process has `repeat_ok`; absolute sizes and live words are
      reported (§8.3).
  R1  per release kind (§8.1, 8.6): the no-op floor gives the resolution
      (its range across all processes <= RESOLUTION words per object);
      then, per process on exact fractions: the candidate fails when any of
      its processes has a residual >= 1/2 word per object while every
      baseline process is under 1/2 in magnitude; a baseline process at or
      over 1/2, an unresolved floor or a kind whose residuals range over
      more than RESOLUTION on a side (a leak in some processes only) is
      inconclusive (a larger M); a held size under H_MIN words per object,
      no comparable held reading or a weak probe that did not collect on
      the baseline is blocked (the probe cannot see, a larger M cannot
      help); the weak probe must have collected on the candidate.
  L1, L3  per registry kind: the masked sets and the ordered lists equal.
  E2  (a) the ordinary rows in an `ext` process equal the candidate's
      (exact, or paired in the 10-pair stage), (b) the residual of the
      extension objects is under 1/2 word per object, (c) the L3 lists
      equal the ordinary ones apart from what the declaration says the
      extension registers; the extension's U against the ordinary
      candidate's is reported (the ext probe is not part of the S2 gate).
"""
from fractions import Fraction
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task33_records as records

PASS, FAIL, INCONCLUSIVE, BLOCKED = "pass", "fail", "inconclusive", "blocked"
REPORTED, UNSUPPORTED = "reported", "unsupported"
GATES = (PASS, FAIL, INCONCLUSIVE, BLOCKED)
RESOLUTION = Fraction(1, 4)  # words per object: the no-op floor's range
HALF = Fraction(1, 2)  # a residual of this much is a retained word
H_MIN = 20  # words per object a held object must have (R1 sensitivity)
BUILT_MIN_SIZE = 100  # the as-built rows need a gateable size this big
EXTEND_PAIRS = 10  # the least that paired_statistics accepts
GRAPH_GATED = tuple(g for g in records.GRAPH_KINDS
                    if not g.startswith("cells"))
ORDINARY_RELEASE = tuple(k for k in records.RELEASE_KINDS if k != "noop")
EXT_RELEASE = tuple(k for k in records.EXT_RELEASE_KINDS if k != "noop")
ALLOCATION_NOTE = (
    "cumulative allocation is not measurable on the stock Poly/ML 5.9.2 "
    "runtime of the snapshots (no counter; heap and allocation-area sizes "
    "are not allocation); TASK31 gate 5 measured exact allocation words "
    "of the same compiled sources on independent clean images with the "
    "private TASK29B counter, and the TASK29B matrix reports it")
# Registry lists of L3 and what each is: the ordered listeners, the sorted
# rest (T33.sml sorts them).
L3_LISTS = records.L3_LISTS


def num(x):
    """A number as JSON holds it: an int, a float, or p/q for a fraction."""
    if isinstance(x, Fraction):
        return int(x) if x.denominator == 1 else str(x)
    return x


def row(case, kind, decision, reason, owed=None, **detail):
    assert decision in GATES + (REPORTED, UNSUPPORTED), decision
    return dict(case=case, kind=kind, decision=decision, reason=reason,
                owed=owed, **detail)


def key_of(case, kind):
    return "%s:%s" % (case, kind)


def constant(values):
    return all(v == values[0] for v in values)


def worst(decisions):
    """fail over blocked over inconclusive over pass."""
    for d in (FAIL, BLOCKED, INCONCLUSIVE):
        if d in decisions:
            return d
    return PASS


# --- series: what is compared -------------------------------------------

def zero_margin(pairs):
    """The decision of `candidate <= baseline` over aligned (base, cand)
    pairs, by the existing paired statistics at zero margin: equal values
    pass; a zero baseline with a larger candidate fails; the rest is the
    paired bootstrap of the ratios (`acceptance.paired_statistics`, zero
    margin: low > 1 fails, high <= 1 passes). A pair of zeros is the ratio
    1, a negative value is not judged."""
    pairs = [(float(b), float(c)) for b, c in pairs]
    if any(v < 0 for p in pairs for v in p):
        return INCONCLUSIVE
    if all(b == c for b, c in pairs):
        return PASS
    if any(b == 0 and c > 0 for b, c in pairs):
        return FAIL
    obs = [dict(baseline=b or 1.0, candidate=c or 1.0) for b, c in pairs]
    return a.paired_statistics(obs, 0.0, True)["decision"]


def compare(bvals, cvals, paired):
    """(status, detail) of one series: the values of the baseline and of
    the candidate, one per process (exact mode) or per pair (paired mode).
    Exact: `unstable` when a side's values differ among themselves, else
    pass when cand <= base and fail otherwise. Paired: zero_margin."""
    detail = dict(base=[num(v) for v in bvals], cand=[num(v) for v in cvals])
    if paired:
        return zero_margin(list(zip(bvals, cvals))), detail
    if not (constant(bvals) and constant(cvals)):
        return "unstable", detail
    return (PASS if cvals[0] <= bvals[0] else FAIL), detail


def settle(statuses, paired):
    """The decision and owed stage of a kind from its series' statuses: a
    stable failure is final, an unstable series is owed the 10-pair stage
    (exact mode), an inconclusive paired series blocks."""
    if FAIL in statuses:
        return FAIL, None
    if "unstable" in statuses:
        return INCONCLUSIVE, None if paired else "extend"
    if INCONCLUSIVE in statuses:
        return INCONCLUSIVE, None
    return PASS, None


# --- S1 ------------------------------------------------------------------

def graph_values(procs, g, field):
    sizes = sorted(procs[0]["graph"][g])
    return {n: [p["graph"][g][n][field] for p in procs] for n in sizes}


def slopes(by_size):
    """{(n1, n2): [words per rule per process]} of adjacent sizes."""
    sizes = sorted(by_size)
    return {(n1, n2): [Fraction(w2 - w1, n2 - n1)
                       for w1, w2 in zip(by_size[n1], by_size[n2])]
            for n1, n2 in zip(sizes, sizes[1:])}


def gateable(procs, n, mode):
    return all(p["gateable"][n][mode] for p in procs)


def series_of(base, cand, g, mode, paired, keep=None):
    """({name: (status, detail)}, the sizes left out) of kind g in the mode
    "canonical" or "built". `keep(procs, n)` limits the sizes to those it
    accepts for every process of both sides (a slope needs both its
    sizes)."""
    field = "canon_words" if mode == "canonical" else "words"
    bv, cv = graph_values(base, g, field), graph_values(cand, g, field)
    if sorted(bv) != sorted(cv):
        return None, []
    sizes = sorted(bv)
    kept = [n for n in sizes if keep is None or keep(base + cand, n)]
    out = {}
    for n in kept:
        out["size %d" % n] = compare(bv[n], cv[n], paired)
    for n1, n2 in zip(sizes, sizes[1:]):
        if n1 in kept and n2 in kept:
            out["slope %d-%d" % (n1, n2)] = compare(
                [Fraction(y - x, n2 - n1) for x, y in zip(bv[n1], bv[n2])],
                [Fraction(y - x, n2 - n1) for x, y in zip(cv[n1], cv[n2])],
                paired)
    return out, [n for n in sizes if n not in kept]


def step_report(procs, g):
    steps = [p["step"].get(g) for p in procs]
    if not all(steps):
        return None
    return {mode: [s[mode]["match"] for s in steps]
            for mode in records.STEP_MODES}


def coverage(p, g):
    """The sizes whose as-built rows of graph kind g are gateable in the
    process: the summary's own list (`gateable_coverage`, design 8.5) or,
    without it, the sizes whose as-built window held no GC share pass."""
    given = (p.get("gateable_coverage") or {}).get(g)
    if given is not None:
        return sorted(given)
    return sorted(n for n, w in p["gateable"].items() if w["built"])


def moved_anchors(procs, g):
    """The anchor movements (design 8.5) of kind g in the processes: a
    retention into the shared base, a finding about the side."""
    return [m for p in procs for m in p.get("anchor_moved") or ()
            if m.get("kind") == g]


def s1_kind(base, cand, g, paired=False):
    """The S1 row of graph kind g. An anchor moved on the candidate is a
    fail (a base's is the caller's refusal)."""
    moved = moved_anchors(cand, g)
    if moved:
        return row("S1", g, FAIL, "the anchor moved while the candidate's "
                   "rows were measured (retention into the shared base)",
                   moved=moved)
    canon, left = series_of(base, cand, g, "canonical", paired,
                            lambda procs, n: gateable(procs, n, "canonical"))
    if not canon and not left:
        return row("S1", g, BLOCKED, "the two sides measured different "
                   "sizes")
    statuses = [s for s, _ in canon.values()]
    if left:  # a GC share pass fell inside a canonical window
        statuses.append("unstable")
    # as-built rows: only the sizes gateable (no share pass, no moved
    # anchor) in every process of both sides are compared, and the kind
    # needs one of them of at least BUILT_MIN_SIZE (design 8.6)
    built, left_built = series_of(
        base, cand, g, "built", paired,
        lambda procs, n: all(n in coverage(p, g) for p in procs))
    kept = sorted(set(graph_values(base, g, "words")) - set(left_built))
    gated_built = bool(built) and any(n >= BUILT_MIN_SIZE for n in kept)
    if gated_built:
        statuses += [s for s, _ in built.values()]
    else:
        statuses.append("unstable")
    decision, owed = settle(statuses, paired)
    why = ", ".join("%s %s" % (k, s) for k, (s, _) in canon.items()
                    if s != PASS)
    if left:
        why += "; canonical size(s) %s not gateable (a GC share pass)" % (
            left,)
    if not gated_built:
        why += ("; no as-built size >= %d is gateable in every process "
                "(kept: %s)" % (BUILT_MIN_SIZE, kept))
    return row("S1", g, decision, why.strip("; ") if decision != PASS else
               "canonical and as-built rows equal or smaller at every "
               "gateable size and slope",
               owed, mode="paired" if paired else "exact",
               canonical={k: dict(status=s, **d)
                          for k, (s, d) in canon.items()},
               canonical_left_out=left,
               as_built=None if not built else {
                   k: dict(status=s, **d) for k, (s, d) in built.items()},
               as_built_kept=kept, as_built_gated=gated_built,
               step=dict(base=step_report(base, g),
                         cand=step_report(cand, g)))


# --- S2 ------------------------------------------------------------------

def total_deltas(declared):
    """The declared closure-total changes as scoped entries {heap, kinds,
    value} (design 8.5): `s2.total_delta` of the declaration
    (task33_offline.load_declared())."""
    return [dict(heap=e["heap"], kinds=e.get("kinds"), value=e["value"])
            for e in declared["s2"]["total_delta"]]


def declared_delta(entries, heap, kind):
    """The one entry covering (heap, kind): its value. None or several is
    a Refusal's business (the caller's): `ValueError`."""
    found = [e for e in entries if e["heap"] == heap and
             (e["kinds"] is None or kind in e["kinds"])]
    if len(found) != 1:
        raise ValueError("%d declared total_delta entries cover %s on %s, "
                         "not one" % (len(found), kind, heap))
    return found[0]["value"]


def anchored_of(procs):
    return [p["anchored"] for p in procs]


def applicable(procs):
    """The closure total U is computed (D and every structure loaded)."""
    return [p["anchored"]["total"] is not None for p in procs]


def s2_kind(base, cand, kind, delta, paired=False):
    """The S2 row of a registry kind. `delta` is the declared closure total
    change in words, or None where the kind computes no U (a structure of
    the closure is not loaded in its heap: not applicable, reported)."""
    ab, ac = anchored_of(base), anchored_of(cand)
    detail = dict(mode="paired" if paired else "exact", declared=delta,
                  sizes=dict(base=base[0]["registry"]["sizes"],
                             cand=cand[0]["registry"]["sizes"]),
                  live=dict(base=[p["live"] for p in base][:1],
                            cand=[p["live"] for p in cand][:1]))
    here = applicable(base + cand)
    if not any(here):
        return row("S2", kind, REPORTED, "no closure total here: a "
                   "structure of the closure is not loaded in this heap",
                   **detail)
    if not all(here):
        return row("S2", kind, FAIL, "the closure total is computed on one "
                   "side only (a structure is missing on the other)",
                   **detail)
    if delta is None:
        raise ValueError("S2 %s: U is computed but no total_delta covers "
                         "it" % kind)
    if not all(x["repeat_ok"] for x in ab + ac):
        return row("S2", kind, INCONCLUSIVE, "the repeats of a process "
                   "disagree (repeat_ok)", None if paired else "extend",
                   **detail)
    ub = [x["total"][0] for x in ab]
    uc = [x["total"][0] for x in ac]
    change = [c - b for b, c in zip(ub, uc)]
    detail["total"] = dict(base=ub, cand=uc, change=change)
    exclusive = {}
    for name in sorted(ab[0]["rows"]):
        exclusive[name] = compare([x["rows"][name][0] for x in ab],
                                  [x["rows"][name][0] for x in ac], paired)
    detail["exclusive"] = {n: dict(status=s, **d)
                           for n, (s, d) in exclusive.items()}
    statuses = [s for s, _ in exclusive.values()]
    if paired:
        # the change is constant in the sides' repeats: compare each
        # candidate U with its baseline plus the declaration (both ways)
        want = [b + delta for b in ub]
        statuses.append(worst([zero_margin(list(zip(want, uc))),
                               zero_margin(list(zip(uc, want)))]))
    elif not (constant(ub) and constant(uc)):
        statuses.append("unstable")
    elif change[0] != delta:
        statuses.append(FAIL)
    decision, owed = settle(statuses, paired)
    if decision == PASS:
        why = ("closure total changes by the declared %d words and no "
               "exclusive part grows" % delta)
    else:
        why = "total change %s (declared %d); exclusive parts: %s" % (
            sorted(set(change)), delta, ", ".join(
                "%s %s" % (n, s) for n, (s, _) in exclusive.items()
                if s != PASS) or "ok")
    return row("S2", kind, decision, why, owed, **detail)


# --- L1 and L3 -----------------------------------------------------------

def lists_equal(base, cand, case, kind, fields, view):
    """Within a side the lists are one (a baseline that disagrees with
    itself blocks, a candidate that does fails); across the sides they are
    equal (fail otherwise)."""
    seen = {}
    for side, procs in (("base", base), ("cand", cand)):
        seen[side] = []
        for f in fields:
            values = [view(p, f) for p in procs]
            if not all(v == values[0] for v in values):
                return row(case, kind, BLOCKED if side == "base" else FAIL,
                           "the %s processes disagree on %s" % (side, f))
            seen[side].append(values[0])
    diff = {f: dict(only_base=[x for x in b if x not in c],
                    only_cand=[x for x in c if x not in b])
            for f, b, c in zip(fields, seen["base"], seen["cand"]) if b != c}
    if diff:
        return row(case, kind, FAIL, "differs: " + ", ".join(sorted(diff)),
                   differences=diff)
    return row(case, kind, PASS, "equal on both sides: " +
               ", ".join(fields))


def l1_kind(base, cand, kind, mask):
    """`mask(side, path)` masks a directory (the side's root and probe
    directory)."""
    def view(side):
        def get(p, f):
            if f == "loaded":
                return sorted(set(p["registry"]["loaded"]))
            return sorted({(n, mask(side(p), d))
                           for n, d in p["registry"]["files"]})
        return get
    side_of = {id(p): "base" for p in base}
    side_of.update({id(p): "cand" for p in cand})
    return lists_equal(base, cand, "L1", kind, ("loaded", "files"),
                       view(lambda p: side_of[id(p)]))


def l3_kind(base, cand, kind):
    def view(p, f):
        values = list(p["registry"][f])
        return values if f == "listeners" else sorted(values)
    return lists_equal(base, cand, "L3", kind, L3_LISTS, view)


# --- R1 ------------------------------------------------------------------

def noop_floor(procs):
    """The no-op kind's residual (words per object) of every process."""
    return [p["residual"]["noop"] for p in procs]


def resolved(procs):
    floor = noop_floor(procs)
    return max(floor) - min(floor) <= RESOLUTION


def comparable_held(p, kind):
    return p["held_comparable"][kind]


def held_problem(procs, kind):
    """None, or why the sensitivity requirement (h >= H_MIN words per
    object on the comparable held readings, at least one per side) is
    not met. Neither a larger M nor a redraw of the rows helps with the
    second: the probe cannot see a retained word."""
    held = [p["held"][kind] for p in procs if comparable_held(p, kind)]
    if not held:
        return "no comparable held reading"
    if min(held) < H_MIN:
        return ("a held object has under %d words (%s): the probe cannot "
                "see a retained word" % (H_MIN, num(min(held))))
    return None


def spread(values):
    return max(values) - min(values)


def r1_kind(base, cand, kind, case="R1"):
    """The R1 row of a release kind (per process, exact fractions); with
    no baseline (`base` empty: E2 (b), the extension kinds) the candidate's
    residuals must all be under 1/2 word per object."""
    procs = base + cand
    floor = noop_floor(procs)
    rb = [p["residual"][kind] for p in base]
    rc = [p["residual"][kind] for p in cand]
    detail = dict(floor=[num(x) for x in floor],
                  floor_range=num(spread(floor)),
                  residual=dict(base=[num(x) for x in rb],
                                cand=[num(x) for x in rc]),
                  held=[num(p["held"][kind]) for p in procs])
    if not resolved(procs):
        return row(case, kind, INCONCLUSIVE, "the no-op floor's range %s "
                   "exceeds the resolution %s words per object" % (
                       num(spread(floor)), RESOLUTION), "followup",
                   **detail)
    for side, group in (("base", base), ("cand", cand)):
        problem = group and held_problem(group, kind)
        if problem:
            return row(case, kind, BLOCKED, "%s: %s" % (side, problem),
                       **detail)
    if any(abs(x) >= HALF for x in rb):
        return row(case, kind, INCONCLUSIVE, "a baseline process's "
                   "residual is %s words per object, not under 1/2" % (
                       [num(x) for x in rb],), "followup", **detail)
    if any(x >= HALF for x in rc):
        return row(case, kind, FAIL, "a candidate process retains %s "
                   "words per object (1/2 or more)" % (
                       [num(x) for x in rc],), **detail)
    unstable = [side for side, v in (("base", rb), ("cand", rc))
                if v and spread(v) > RESOLUTION]
    if unstable:
        return row(case, kind, INCONCLUSIVE, "the residuals of the %s "
                   "processes range over more than %s words per object" % (
                       " and ".join(unstable), RESOLUTION), "followup",
                   **detail)
    return row(case, kind, PASS, "every residual is under 1/2 word per "
               "object", **detail)


def weak_row(base, cand):
    detail = dict(base=[p["weak"]["status"] for p in base],
                  cand=[p["weak"]["status"] for p in cand])
    if not all(p["weak"]["status"] == "pass" for p in base):
        return row("R1", "weak", BLOCKED, "the weak probe was not "
                   "collected on the baseline: the probe cannot show "
                   "a discarded simpset is collected", **detail)
    if not all(p["weak"]["status"] == "pass" for p in cand):
        return row("R1", "weak", FAIL, "the weak probe was not collected "
                   "on the candidate: the discarded simpset is retained",
                   **detail)
    return row("R1", "weak", PASS, "collected on both sides", **detail)


def r1_rows(base, cand):
    return [weak_row(base, cand)] + [r1_kind(base, cand, k)
                                     for k in ORDINARY_RELEASE]


# --- E1 and E2 -------------------------------------------------------------

def e1_ext(ext):
    """The explicit extension use worked: every extension process printed
    its kernel checks (the validator refuses a failed one)."""
    ok = bool(ext) and all(set(records.EXT_CHECKS) <= set(p["checks"])
                           for p in ext)
    return row("E1", "ext", PASS if ok else BLOCKED,
               "the explicit extension checks passed in %d process(es)" %
               len(ext) if ok else "no extension check records")


def e2a(ext, ordinary, paired=False):
    """The ordinary rows (canonical words of every graph kind and size) in
    an extension process equal those of the ordinary candidate, routed as
    S1 is: an anchor that moved in an extension process fails; a size whose
    canonical window held a GC share pass in some process, or a value not
    repeatable within a side, is owed the 10-pair stage (`paired`: the
    pairs agree both ways at zero margin)."""
    moved = [m for g in GRAPH_GATED for m in moved_anchors(ext, g)]
    if moved:
        return row("E2", "a", FAIL, "the anchor moved in an extension "
                   "process (retention into the shared base)", moved=moved)
    bad, statuses, left = [], [], {}
    for g in GRAPH_GATED:
        ev = graph_values(ext, g, "canon_words")
        ov = graph_values(ordinary, g, "canon_words")
        if sorted(ev) != sorted(ov):
            return row("E2", "a", BLOCKED, "different sizes")
        for n in ev:
            if not gateable(ext + ordinary, n, "canonical"):
                left.setdefault(g, []).append(n)
                statuses.append("unstable")
            elif paired:
                one = worst([zero_margin(list(zip(ev[n], ov[n]))),
                             zero_margin(list(zip(ov[n], ev[n])))])
                statuses.append(one)
                if one == FAIL:
                    bad.append("%s %d: %s vs %s" % (g, n, ev[n], ov[n]))
            elif not (constant(ev[n]) and constant(ov[n])):
                statuses.append("unstable")
            elif ev[n][0] != ov[n][0]:
                statuses.append(FAIL)
                bad.append("%s %d: %s vs %s" % (g, n, ev[n][0], ov[n][0]))
    decision, owed = settle(statuses, paired)
    detail = dict(mode="paired" if paired else "exact", differences=bad,
                  not_gateable=left)
    if decision == FAIL:
        return row("E2", "a", FAIL, "ordinary rows differ in an extension "
                   "process: " + "; ".join(bad[:5]), **detail)
    if decision != PASS:
        return row("E2", "a", decision, "rows are not repeatable, or a GC "
                   "share pass fell in a canonical window (%s)" % (
                       sorted(left) or "none"), owed, **detail)
    return row("E2", "a", PASS, "the canonical rows equal the ordinary "
               "candidate's at every kind and size", **detail)


def e2b(ext):
    out = [r1_kind([], ext, k, "E2") for k in EXT_RELEASE]
    decisions = [r["decision"] for r in out]
    return row("E2", "b", worst(decisions),
               "residual of the extension objects: " + ", ".join(
                   "%s %s" % (r["kind"], r["decision"]) for r in out),
               "followup" if INCONCLUSIVE in decisions else None,
               kinds={r["kind"]: r for r in out})


def agreed(procs, field, view):
    """(the one value of `field` in every process, None) or (None, why)."""
    values = [view(p["registry"][field]) for p in procs]
    if not all(v == values[0] for v in values):
        return None, "the processes disagree on %s" % field
    return values[0], None


def declared_names(declared):
    """({list: set of names}, {list: set of names of required entries},
    set of the probe's own) of the declared e2c state: the observable
    entries' `registers` and the `probe_support` ones."""
    allowed = {f: set() for f in L3_LISTS}
    required = {f: set() for f in L3_LISTS}
    for e in declared["extension_state"]:
        if not e["observable"]:
            continue  # prose-only state satisfies nothing
        for f, names in e["registers"].items():
            allowed[f] |= set(names)
            if e["required"]:
                required[f] |= set(names)
    for f, names in declared["probe_support"]["registers"].items():
        allowed[f] |= set(names)
    return allowed, required


def in_order(sub, whole):
    it = iter(whole)
    return all(x in it for x in sub)


def e2c(ext, ordinary, declared):
    """The L3 lists after explicit use equal the ordinary candidate's (same
    heap, nothing used) apart from what the declaration (`declared`: the
    e2c part) says: per list the names the extension processes add are
    among those the observable entries register (or the probe's own
    support), every name of a required entry is added, no ordinary name is
    gone and the ordinary listeners keep their relative order. All
    extension processes agree, and so do the ordinary ones. `loaded` and
    `files` are not compared: the probe modules differ by design."""
    allowed, required = declared_names(declared)
    added, removed, undeclared, missing, reorder = {}, {}, {}, {}, []
    for f in L3_LISTS:
        e, why = agreed(ext, f, list)
        o, why_o = agreed(ordinary, f, list)
        if why or why_o:
            return row("E2", "c", FAIL, why or why_o)
        added[f] = [x for x in e if x not in o]
        removed[f] = [x for x in o if x not in e]
        undeclared[f] = [x for x in added[f] if x not in allowed[f]]
        missing[f] = sorted(required[f] - set(added[f]))
        if f == "listeners" and not removed[f] and not in_order(o, e):
            reorder.append(f)
    flat = lambda d: {f: v for f, v in d.items() if v}
    detail = dict(added=flat(added), removed=flat(removed),
                  undeclared=flat(undeclared), required_missing=flat(
                      missing), reordered=reorder)
    problems = ["%s %s" % (text, value) for text, value in (
        ("ordinary entries removed:", detail["removed"]),
        ("undeclared entries added by the extension:",
         detail["undeclared"]),
        ("required declared entries not added:", detail["required_missing"]),
        ("ordinary lists reordered:", reorder)) if value]
    if problems:
        return row("E2", "c", FAIL, "; ".join(problems), **detail)
    return row("E2", "c", PASS, "the L3 lists equal the ordinary ones "
               "apart from the declared additions", **detail)


def e2u(ext, ordinary):
    """Reported (E2, not S2: the ext probe is outside the S2 gate): the
    closure total U of an extension process against the ordinary
    candidate's on the same heap, and the exclusive parts. Growth of
    ordinary structures after explicit use is E2-relevant."""
    xe, xo = [p["anchored"] for p in ext], [p["anchored"] for p in ordinary]
    if not all(x["total"] is not None for x in xe + xo):
        return row("E2", "u", REPORTED, "no closure total in an extension "
                   "or an ordinary process (a structure is not loaded)")
    detail = dict(
        total=dict(ext=[x["total"][0] for x in xe],
                   cand=[x["total"][0] for x in xo],
                   change=xe[0]["total"][0] - xo[0]["total"][0]),
        d=dict(ext=[x["d"][0] for x in xe], cand=[x["d"][0] for x in xo],
               change=xe[0]["d"][0] - xo[0]["d"][0]),
        exclusive={n: dict(ext=[x["rows"][n][0] for x in xe],
                           cand=[x["rows"][n][0] for x in xo],
                           change=xe[0]["rows"][n][0] - xo[0]["rows"][n][0])
                   for n in sorted(xe[0]["rows"])})
    return row("E2", "u", REPORTED, "closure total U after explicit "
               "extension use, less the ordinary candidate's: %+d words" %
               detail["total"]["change"], **detail)


# --- S3 and S4 (reported) --------------------------------------------------

def s3_report(groups):
    """Reported, not gated: per unit and side the live words at each phase
    (the processes' readings) and the build-window peaks. `groups` is
    {unit: {side: [summary]}}."""
    out = {}
    for unit, sides in groups.items():
        out[unit] = {}
        for side, procs in sides.items():
            if not procs:
                continue
            data = dict(live={ph: [p["live"].get(ph) for p in procs]
                              for ph in sorted(procs[0]["live"])})
            if procs[0]["phase"]:
                data["peaks"] = {
                    str(n): [dict(status=p["phase"][n]["build"]["status"],
                                  hwm_after=p["phase"][n]["build"][
                                      "hwm_after"],
                                  rss_after=p["phase"][n]["build"][
                                      "rss_after"]) for p in procs]
                    for n in sorted(procs[0]["phase"])}
            out[unit][side] = data
    return out


def s4_row():
    return row("S4", "allocation", UNSUPPORTED, ALLOCATION_NOTE)
