#!/usr/bin/env python3
"""Run caller's unchanged probe, allowing newly added discovery commands.

Only the old mock's command dispatch needs adapting: compiler version and ldd
are real commands, not synthetic build/process events. All its validators,
Git extraction, API receipt, fixtures, mutation and assertions stay unchanged.
"""
import importlib.util
from pathlib import Path
import sys
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[7]
sys.path.insert(0, str(ROOT / "src/simp/tests/performance"))
import loading

spec = importlib.util.spec_from_file_location(
    "review_probe", Path(__file__).resolve().parents[1] /
    "review-v2/loading_binding_probe.py")
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
original_execute = loading.execute


def adapted_patch(target, name, replacement):
    if target is loading and name == "execute":
        def execute(command, cwd, env, timeout, fds):
            if str(command[0]) == "ldd" or "--version" in command:
                return original_execute(command, cwd, env, timeout, fds)
            return replacement(command, cwd, env, timeout, fds)
        return patch.object(target, name, execute)
    return patch.object(target, name, replacement)


probe.patch = SimpleNamespace(object=adapted_patch)
if __name__ == "__main__":
    sys.exit(probe.main())
