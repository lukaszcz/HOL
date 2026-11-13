"""Static check: modules added by the simplifier project (compiled by `load`
in the user's toplevel when not in the default heap) must not use basis
names that HOL libraries designed for toplevel `open` re-export."""
import re
import subprocess
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from run_paired import require_revisions  # noqa: E402

ROOT = HERE.parents[4]
BASE = "cccaa27d70"
# Derived from the *Lib/*Utils signatures that re-export a basis toplevel
# value: patriciaLib.size, hurdUtils.concat, liteLib.foldr.  The dynamic
# test src/simp/tests/fresh-load/shadowed.sml carries the same list; the
# two are cross-checked below.
SHADOWED = ["size", "concat", "foldr"]
FALLBACK_GLOBS = ["*Ext*.sml", "split*.sml", "SplitData.sml",
                  "simpMarker*.sml", "trackedSimpDefaults.sml"]


def strip_comments_strings(text):
    """Remove (nested) comments and string/char literals, keeping newlines."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "(*":
                depth += 1
                i += 2
            elif two == "*)":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif two == "(*":
            depth = 1
            i += 2
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                i += 1
            i += 1
            out.append('""')
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def unqualified(text, names=SHADOWED):
    """(line, name) for each use of a name not preceded by `.`."""
    code = strip_comments_strings(text)
    hits = []
    for m in re.finditer(r"[A-Za-z_][A-Za-z0-9_']*", code):
        if m.group(0) in names and code[max(0, m.start() - 1):m.start()] != ".":
            hits.append((code.count("\n", 0, m.start()) + 1, m.group(0)))
    return hits


def added_files():
    require_revisions(BASE)
    out = subprocess.run(
        ["git", "-C", str(ROOT), "diff", "--name-status", BASE, "HEAD",
         "--", "src"], capture_output=True, text=True, check=True,
        stdin=subprocess.DEVNULL).stdout.splitlines()
    files = []
    for line in out:
        status, _, path = line.partition("\t")
        if (status == "A" and path.endswith(".sml") and
                "/tests/" not in path and not path.endswith("Script.sml")):
            files.append(ROOT / path)
    return files


def fallback_files():
    found = set()
    for g in FALLBACK_GLOBS:
        found.update(p for p in (ROOT / "src").rglob(g)
                     if "/tests/" not in str(p) and
                     not p.name.endswith("Script.sml"))
    return sorted(found)


def candidates():
    try:
        files = added_files()
    except (unittest.SkipTest, subprocess.CalledProcessError, OSError):
        files = []
    return files or fallback_files()


class ShadowedNames(unittest.TestCase):
    def test_scanner_negative_controls(self):
        self.assertEqual(unqualified("val n = size s"), [(1, "size")])
        self.assertEqual(unqualified("val _ = foldr f a l\nconcat l"),
                         [(1, "foldr"), (2, "concat")])
        self.assertEqual(
            unqualified('val x = String.size s + List.foldr f a l'), [])
        self.assertEqual(unqualified(
            '(* size (* nested *) concat *) val s = "foldr size"'), [])

    def test_single_source_list(self):
        sml = (HERE.parents[1] / "fresh-load" / "shadowed.sml").read_text()
        m = re.search(r"val shadowed = \[([^\]]*)\]", sml)
        self.assertIsNotNone(m)
        self.assertEqual(re.findall(r'"([^"]*)"', m.group(1)), SHADOWED)

    def test_added_modules_qualify_shadowed_names(self):
        files = candidates()
        self.assertGreaterEqual(len(files), 10)
        bad = ["%s:%d: unqualified %s" % (f.relative_to(ROOT), ln, nm)
               for f in files for ln, nm in unqualified(f.read_text())]
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()
