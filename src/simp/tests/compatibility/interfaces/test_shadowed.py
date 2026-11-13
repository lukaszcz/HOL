"""Static check: modules added by the simplifier project (compiled by `load`
in the user's toplevel when not in the default heap) must not use basis
names that HOL libraries designed for toplevel `open` re-export."""
import fnmatch
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
SIMP_SRC = ROOT / "src" / "simp" / "src"
LAUNCHER = HERE.parents[1] / "fresh-load" / "shadowed.sml"
HOLMAKEFILE = SIMP_SRC / "Holmakefile"
# Basis names rebound by libraries designed for toplevel `open`: size
# (patriciaLib) and concat (hurdUtils) are type-incompatible re-exports;
# foldr (liteLib, same type) is kept defensively by decision.  Not every
# re-export is listed (liteLib.foldl and hurdUtils.map are compatible).
# The list itself lives in the launcher and is parsed from it here.
SHADOWED_RE = r"val shadowed = \[([^\]]*)\]"


def parse_shadowed():
    m = re.search(SHADOWED_RE, LAUNCHER.read_text())
    return re.findall(r'"([^"]*)"', m.group(1)) if m else []


SHADOWED = parse_shadowed()


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
        before = code[max(0, m.start() - 1):m.start()]
        if m.group(0) in names and before != ".":
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
        parts = Path(path).parts
        if (status == "A" and path.endswith(".sml") and
                "tests" not in parts and ".hol" not in parts and
                not path.endswith("Script.sml")):
            files.append(ROOT / path)
    return files


def launcher_patterns():
    """The name patterns of the launcher's SML selection rule."""
    m = re.search(r"val ext_patterns = \[([^\]]*)\]", LAUNCHER.read_text())
    return re.findall(r'"([^"]*)"', m.group(1)) if m else []


def holmake_patterns():
    """The wildcard patterns of FRESH_EXT_UO, with .sml dropped."""
    m = re.search(r"FRESH_EXT_UO\s*=\s*\$\(patsubst\s+%\.sml,%\.uo,"
                  r"\s*\\?\s*\$\(wildcard ([^)]*)\)",
                  HOLMAKEFILE.read_text())
    words = m.group(1).split() if m else []
    for w in words:
        if not w.endswith(".sml"):
            raise AssertionError("unexpected wildcard word: " + w)
    return [w[:-4] for w in words]


def select(patterns, scripts=False):
    """src/simp/src/*.sml basenames matching a pattern; the launcher skips
    theory scripts, the Holmake wildcard cannot (scripts=True)."""
    return {p.stem for p in SIMP_SRC.glob("*.sml")
            if (scripts or not p.stem.endswith("Script")) and
            any(fnmatch.fnmatchcase(p.stem, pat) for pat in patterns)}


def fallback_files():
    """Without git objects, mirror the naming of the added modules: the
    launcher patterns in src/simp/src, the *Ext.sml extension modules of the
    other libraries (not tests or .hol build products), and the one added
    module that follows no naming rule, boss/trackedSimpDefaults.sml."""
    files = {SIMP_SRC / (n + ".sml") for n in select(launcher_patterns())}
    files |= {p for p in (ROOT / "src").rglob("*Ext.sml")
              if not {"tests", ".hol"} & set(p.relative_to(ROOT).parts)}
    files.add(ROOT / "src" / "boss" / "trackedSimpDefaults.sml")
    return sorted(files)


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

    def test_shadowed_list_parsed(self):
        self.assertTrue(SHADOWED)
        self.assertEqual(len(SHADOWED), len(set(SHADOWED)))

    def test_one_module_selection_rule(self):
        added = {f.stem for f in added_files()
                 if f.parent == SIMP_SRC}
        self.assertTrue(added)
        self.assertEqual(select(launcher_patterns()), added)
        self.assertEqual(select(holmake_patterns(), scripts=True), added)

    def test_fallback_matches_added_files(self):
        require_revisions(BASE)
        self.assertEqual(set(fallback_files()), set(added_files()))

    def test_added_modules_qualify_shadowed_names(self):
        files = candidates()
        self.assertTrue(files)
        bad = ["%s:%d: unqualified %s" % (f.relative_to(ROOT), ln, nm)
               for f in files for ln, nm in unqualified(f.read_text())]
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()
