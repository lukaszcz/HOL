"""The import graph of the harness' Python modules, for the tests that keep
a seal list complete (test_timing_followup.py, test_task31_attempts.py).

A module is named by its stem; no stem is in two of the directories the
harness puts on its path: this one, allocator-counter/ (which timing_grid
adds) and ../compatibility (which loading and runtime_metrics add). An edge
is (importer, module imported, function it is made in), the function being
None for an import that runs when the importer is imported. Code that is
run by path (runpy, a subprocess) is not an import and is not seen: a test
names it as a root of the closure."""
import ast
from pathlib import Path

HERE = Path(__file__).resolve().parent
DIRECTORIES = (HERE, HERE / "allocator-counter",
               HERE.parent / "compatibility")


def sources():
    """The text of every module of the directories, by stem. Raises
    ValueError for a stem that is in two of them."""
    found, where = {}, {}
    for directory in DIRECTORIES:
        for path in directory.glob("*.py"):
            if path.stem in found:
                raise ValueError("module %s is in both %s and %s" % (
                    path.stem, where[path.stem], path))
            found[path.stem], where[path.stem] = path.read_text(), path
    return found


def edges(sources, name):
    """The edges from module `name` to the modules of `sources`, wherever in
    the module the import is (function-level imports included)."""
    found = set()

    def walk(node, function):
        for child in ast.iter_child_nodes(node):
            here = child.name if isinstance(
                child, (ast.FunctionDef, ast.AsyncFunctionDef)
            ) and function is None else function
            if isinstance(child, ast.Import):
                found.update((x.name.split(".")[0], function)
                             for x in child.names)
            elif isinstance(child, ast.ImportFrom) and child.level == 0:
                found.add((child.module.split(".")[0], function))
                found.update((x.name, function) for x in child.names)
            walk(child, here)
    walk(ast.parse(sources[name]), None)
    return {(name, m, function) for m, function in found if m in sources}


def closure(sources, roots, left_out=()):
    """(modules, used): the modules that the roots import to the transitive
    closure but for the edges of `left_out`, and those edges that a module
    of the closure makes."""
    left_out = set(left_out)
    seen, used, todo = set(), set(), list(roots)
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        for edge in sorted(edges(sources, name), key=str):
            if edge in left_out:
                used.add(edge)
            else:
                todo.append(edge[1])
    return seen, used
