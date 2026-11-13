"""TASK37 lineage: the one commit point and the candidate equivalence.

Every TASK37 commit is made in the main worktree, and the stream clones only
fast-forward from it, so the inputs of the disposition may name different
revisions of the candidate (a stream's clone is at the head it was at when
it launched). The disposition runs in that main worktree `D` (the checkout
that holds this code), whose HEAD contains every one of them (design
decision 17). `Lineage` is the one place that accepts a revision:

- `--candidate` names a commit of D;
- the candidate `Ci` an input records is accepted only if it exists in D, is
  an ancestor of D's HEAD, and has the tree outside the performance area
  (`timing_grid.git_tree_outside`) of `--candidate`: the inputs measured the
  same sources, whatever performance-only commits they were at;
- a harness an input records (a checkout, a clean head) is accepted by the
  same rule for its head, and its recorded tree is the one git gives.

Every accepted revision is recorded under the label of the input that
named it (`recorded`).
"""
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
import acceptance as a
import timing_grid as tg

HEX = frozenset("0123456789abcdef")


class Lineage:
    def __init__(self, repo, candidate):
        self.repo = Path(repo).resolve()
        here = a.HERE.parents[3].resolve()
        a.require(self.repo == here,
                  "the disposition runs in the checkout that holds this "
                  "code (%s), not in %s: every input's candidate must be "
                  "a commit of that one commit point" % (here, self.repo))
        self.trees = {}
        self.recorded = {}
        self.candidate = self.commit("--candidate", candidate)
        self.tree = self.tree_of(self.candidate)

    def commit(self, label, rev):
        """The full sha of `rev` (at least ten hex digits), a commit of the
        repository."""
        a.require(isinstance(rev, str) and len(rev) >= 10 and
                  set(rev) <= HEX,
                  "%s names no revision of at least ten hex digits: %r"
                  % (label, rev))
        found = subprocess.run(
            ["git", "-C", str(self.repo), "cat-file", "-e",
             rev + "^{commit}"], stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        a.require(found.returncode == 0,
                  "%s names %s, which is no commit of %s: fetch it there "
                  "first" % (label, rev, self.repo))
        return a.git(self.repo, "rev-parse", rev + "^{commit}")

    def tree_of(self, rev):
        if rev not in self.trees:
            self.trees[rev] = tg.git_tree_outside(self.repo, rev)
        return self.trees[rev]

    def equivalent(self, label, rev):
        """The full sha of `rev` when it is an ancestor of HEAD with the
        tree outside the performance area of the candidate."""
        full = self.commit(label, rev)
        found = subprocess.run(
            ["git", "-C", str(self.repo), "merge-base", "--is-ancestor",
             full, "HEAD"], stdin=subprocess.DEVNULL)
        a.require(found.returncode == 0,
                  "%s names %s, which is not an ancestor of HEAD of %s"
                  % (label, full, self.repo))
        a.require(self.tree_of(full) == self.tree,
                  "%s names %s, whose tree outside the performance area "
                  "is not that of the candidate %s" % (
                      label, full, self.candidate))
        return full

    def candidate_of(self, label, rev):
        """The candidate an input records, accepted by equivalence and
        recorded under `label`."""
        full = self.equivalent(label + " candidate", rev)
        self.recorded[label] = full
        return full

    def harness(self, label, found, clean=False):
        """A harness checkout an input records: {head,
        tree_outside_performance} (and `dirty`, which with `clean` must be
        present and false). Its head is accepted as a candidate is and its
        recorded tree is the one git gives for it."""
        a.require(isinstance(found, dict) and
                  isinstance(found.get("head"), str) and
                  isinstance(found.get("tree_outside_performance"), str),
                  "%s records no harness checkout" % label)
        a.require(("dirty" in found or not clean) and
                  found.get("dirty", False) is False,
                  "%s was made in a dirty harness checkout" % label)
        full = self.equivalent(label + " harness", found["head"])
        a.require(found["tree_outside_performance"] == self.tree,
                  "%s records another tree outside the performance area "
                  "than the candidate's: a different harness" % label)
        self.recorded[label + " harness"] = full
        return full
