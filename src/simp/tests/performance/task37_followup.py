#!/usr/bin/env python3
"""TASK37 follow-up: the cells a timing shard left open, measured again by
the shared engine (the method of task31_followup.py, whose precedent this
module keeps: the follow-up declaration is apart from the shard tables, so
declaring one changes no seal of task37_grid.py and voids no pilot, counts
file or record of a shard).

A table for timing_grid.py (read that module, and the "TASK37" and "TASK31
follow-up" sections of PROTOCOL.md). The follow-up of shard KEY replaces the
cells of CELLS[KEY], which a policy decision names after the shard's grid
(and its second stage) left them inconclusive, and nothing else: the
policy, the batch seconds, the samples, the baseline, the sources, the
pins and the seals are the shard's (task37_grid.py), whose grid is replayed
in full by the shard's own engine before the counts are derived, and again
by `replay`. The layout seed is another than the shard's and its second
stage's, the pairs of a cell derive from the shard's develop/develop
control (`Grid.followup_pairs`, twice the pairs of the shard), and the
attempts go into the shard's ledger.

With no declaration file there is no follow-up and no engine: every
command is refused. A follow-up is declared by one data file per shard,
`task37_<kind>_<n>_followup_cells.json` (`declaration_file`):

  {"schema": "task37-followup-cells-v1", "shard": "matrix-2",
   "cells": ["case-size", ...]}

where "shard" is the shard key of the file name and the cells are a
non-empty subset of the shard's part (`task37_grid.PARTS`), without
repeats. This module discovers the files that exist and its text never
changes on a declaration; each follow-up table seals its own declaration
file (and no other), so declaring the follow-up of one shard changes no
seal of the follow-up table of another (whose pilot, counts and records
stay valid). The declaration file is committed ALONE, before any
observation of the follow-up (the counts-alone rule of PROTOCOL.md). The
follow-up table of shard `matrix-2` is
`task37-matrix-2-followup`, its counts file
`task37_matrix_2_followup_iterations.json` (made by `pilot` and
`predeclare --replaces GRID --replaces-pilot DIR`, committed alone).

The declaration must precede the follow-up's counts: the engine here
(`Followup`) checks, wherever it reads the commit of a counts file, that the
declaration file was committed alone and that its commit is an ancestor of
that counts commit (`check_declaration_order`); task37_dispose.py checks it
again. Counts revisions of the follow-up (`STEM_2.json`, ...) are discovered
as for the shards (`task37_grid.revisions_of`), each bound to its own table.

  task37_followup.py SHARD COMMAND ...

with the engine's commands (`prepare`, `pilot`, `predeclare`,
`verify-counts`, `run`, `extend`, `replay`). GRIDS holds the engines
declared, by table name; task37_dispose.py takes them with
`task37_grid.GRIDS` (`--followup SHARD=DIR`, `--pilot`,
`--followup-pilot`).
"""
import subprocess
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task37_cases as cases
import task37_grid as base
import timing_grid as tg

SCHEMA = "task37-followup-cells-v1"
# The shard's sealed files and its driver (this table takes its constants
# and replays its grid through its table).
SEALED = {k: base.SEALED[base.KIND[k]] + ("task37_grid.py",)
          for k in base.SHARD_KEYS}


def declaration_file(key):
    """The declaration file of the follow-up of a shard."""
    kind, number = key.split("-")
    return a.HERE / ("task37_%s_%s_followup_cells.json" % (kind, number))


def load_declaration(key, path=None):
    """The cells the declaration file of shard `key` (or `path`, for a
    test) declares, validated: the schema, the shard key of the file name
    and a non-empty subset of the shard's part, without repeats."""
    a.require(key in base.PARTS, "no such shard: %r" % (key,))
    path = declaration_file(key) if path is None else path
    found = a.load(path)
    a.require(isinstance(found, dict) and set(found) == {
        "schema", "shard", "cells"} and found["schema"] == SCHEMA,
        "%s is not a %s declaration" % (path, SCHEMA))
    a.require(found["shard"] == key, "%s declares the follow-up of %r, "
              "not of the shard %s of its file name" % (
                  path, found["shard"], key))
    cells = found["cells"]
    a.require(isinstance(cells, list) and cells and all(
        isinstance(c, str) for c in cells) and
        len(set(cells)) == len(cells) and set(cells) <= set(
            base.PARTS[key]), "%s declares cells that are not a non-empty "
        "subset of the part of shard %s, or repeats one" % (path, key))
    return tuple(cells)


def declared():
    """{shard key: cells} of the declaration files that exist."""
    return {k: load_declaration(k) for k in base.SHARD_KEYS
            if declaration_file(k).exists()}


def name_of(key):
    """The table name of the follow-up of a shard."""
    return base.name_of(key) + "-followup"


def file_of(key):
    """The counts file of the follow-up of a shard."""
    kind, number = key.split("-")
    return a.HERE / ("task37_%s_%s_followup_iterations.json" % (kind,
                                                                 number))


def declaration_commit(repo, candidate, key):
    """The one commit of the history of `candidate` that introduced the
    declaration file of shard `key`; the file is the committed one (so not
    untracked, staged only or edited) and that commit changed nothing
    else."""
    path = declaration_file(key)
    name = tg.repo_relative(repo, path)
    try:
        commit = tg.git_introduced(repo, candidate, name)
    except ValueError as error:
        raise ValueError("the declaration file %s is not committed in the "
                         "history of %s (an untracked or uncommitted "
                         "declaration declares nothing): %s" % (
                             name, str(candidate)[:12], error)) from None
    a.require(tg.git_blob(repo, candidate, name) ==
              a.git(repo, "hash-object", str(path)),
              "the declaration file %s is not the committed one" % name)
    a.require(set(tg.git_touched(repo, commit)) == {name},
              "the commit %s that introduced %s must change only that "
              "file: commit the declaration alone" % (commit[:12], name))
    return commit


def is_ancestor(repo, commit, descendant):
    return subprocess.run(
        ["git", "-C", str(repo), "merge-base", "--is-ancestor", commit,
         descendant], stdin=subprocess.DEVNULL).returncode == 0


def check_declaration_order(repo, candidate, key, counts_commit):
    """The declaration file of shard `key` was committed alone (the one
    commit of the candidate's history that touched it changed nothing else,
    and the file is the committed one) and that commit is an ancestor of
    the commit of the follow-up's counts file `counts_commit`: the cells
    were fixed before the follow-up's counts, hence before any observation
    of it (the counts-alone rule of PROTOCOL.md)."""
    commit = declaration_commit(repo, candidate, key)
    a.require(commit != counts_commit and
              is_ancestor(repo, commit, counts_commit),
              "the declaration %s (commit %s) is not an ancestor of the "
              "commit %s of the follow-up's counts file: declare the "
              "follow-up before its counts are made" % (
                  declaration_file(key).name, commit[:12],
                  counts_commit[:12]))


def check_declaration_at_pilot(repo, key, head):
    """The declaration of shard `key` was committed, alone, before the
    follow-up's pilot: its commit is `head` or an ancestor of it (`head`:
    the checkout head the pilot ran at, or runs at), and the file is the
    committed one. An untracked or uncommitted declaration is refused: the
    pilot's cells must have been fixed in git first."""
    commit = declaration_commit(repo, head, key)
    a.require(is_ancestor(repo, commit, head),
              "the declaration %s (commit %s) is not an ancestor of the "
              "pilot's checkout head %s" % (
                  declaration_file(key).name, commit[:12], head[:12]))


def repo_of_code():
    """The repository this code is in (where the declaration files are)."""
    return Path(a.git(a.HERE, "rev-parse", "--show-toplevel").strip())


class Followup(tg.Grid):
    """The engine of a follow-up: the shared engine, and the counts commit
    of any of its counts files is checked to follow the declaration."""

    def __init__(self, table, key, doc=None):
        super().__init__(table, doc=doc)
        self.key = key

    def pilot(self, args):
        """The pilot of the follow-up: the declaration is committed alone
        first (HEAD of the pilot's repository holds it), so no untracked or
        uncommitted declaration reaches a pilot."""
        head = a.git(args.repo, "rev-parse", "HEAD").strip()
        check_declaration_at_pilot(args.repo, self.key, head)
        return super().pilot(args)

    def check_pilot_settings(self, inventory, seconds=None):
        """The shared checks, and the declaration's commit is an ancestor
        of the checkout head the pilot inventory records."""
        super().check_pilot_settings(inventory, seconds)
        head = (inventory.get("checkout") or {}).get("head")
        a.require(isinstance(head, str) and head,
                  "the pilot inventory records no checkout head")
        check_declaration_at_pilot(repo_of_code(), self.key, head)

    def counts_commit(self, repo, candidate, path):
        commit = super().counts_commit(repo, candidate, path)
        check_declaration_order(repo, candidate, self.key, commit)
        return commit


def table(key, cells, replaced, revisions=None):
    """The follow-up table of shard `key` for `cells` (a non-empty subset
    of its cells), replacing the grid of the engine `replaced`, with the
    counts revisions that exist (`task37_grid.revisions_of`, or
    `revisions`, for a test)."""
    cells = tuple(cells)
    kind = base.KIND[key]
    a.require(cells and set(cells) <= set(base.PARTS[key]),
              "a follow-up measures cells of its shard")
    first = replaced.t
    found = tuple(dict.fromkeys(cases.split(c)[0] for c in cells))
    if revisions is None:
        revisions = base.revisions_of(file_of(key))
    return tg.Table(
        name_of(key), "TASK37-%s-FOLLOWUP" % key.upper(), found, __file__,
        file_of(key), revisions=revisions, cells=cells,
        family=first.family,
        replaces=tg.Replaces(replaced), seconds=base.SECONDS,
        seconds_by_case={c: base.LONG_SECONDS for c in found
                         if c in base.LONG[kind]},
        fixed_seconds=True, schedule="warmup", headroom=1,
        pairs=2 * base.PAIRS, samples=base.SAMPLES,
        seed="%s-layout-1" % name_of(key), baseline=a.BASE, engine=True,
        engines=base.ENGINES, drivers=base.DRIVERS,
        layout_acceptance=base.ACCEPTANCE,
        sealed_history=base.SEALED_HISTORY, tree="src",
        sealed=SEALED[key] + (declaration_file(key).name,),
        require_seed=True, sources=first.sources,
        pinned=first.pinned, pin_file=first.pin_file,
        pin_history=first.pin_history, allocation=first.allocation)


def declare(key, cells, grids=base.GRIDS):
    """The (table, engine) of the follow-up of shard `key`, or None for no
    cell."""
    if not cells:
        return None
    built = table(key, cells, grids[base.name_of(key)])
    return built, Followup(built, key, doc=__doc__)


# The cells of the follow-up of each shard, by shard key (`matrix-2`), read
# from the declaration files; none until a policy decision declares one.
CELLS = declared()
TABLES, GRIDS = {}, {}
for _key, _cells in CELLS.items():
    _found = declare(_key, _cells)
    if _found is not None:
        TABLES[_found[0].name], GRIDS[_found[0].name] = _found


def commands():
    """The engines by the name a command line gives them (`matrix-2`)."""
    return {n[len("task37-"):-len("-followup")]: g for n, g in GRIDS.items()}


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    found = commands()
    if not argv or argv[0] not in found:
        print("REFUSED: no such TASK37 follow-up is declared (declared: "
              "%s; the declaration files): task37_followup.py SHARD "
              "COMMAND ..." % (",".join(found) or "none"), file=sys.stderr)
        return tg.REFUSED
    return found[argv[0]].main(argv[1:])


if __name__ == "__main__":
    sys.exit(main())
