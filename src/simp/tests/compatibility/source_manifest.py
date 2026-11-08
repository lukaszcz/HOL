"""Library: the reviewed source manifest and the helpers audit_task27 uses.

The manifest (task16-source-manifest.json, sealed by MANIFEST_SHA256) covers
the transitive ordinary Poly/standard-kernel source closure of the ordinary
roots, including shared facilities and signatures. audit_task27.py applies
its overlay to it. Sources are compared as bytes against pinned revisions
(git_source), not as tokens. This module reads no build products and has no
command line.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = 'src/simp/src/'
BASE = 'cccaa27d7099cbadc886983020cbe745db7793f3'
START = '6d768feceae9033eb1ae8d34fb331b372f126384'
ORDINARY = tuple(SRC + 'simpLib' + s for s in ('.sml', '.sig'))
EXTENSIONS = tuple(SRC + name + s for name in (
    'simpExtLib', 'Cond_rewrExt', 'TraverseExt', 'OpeningExt',
    'TravrulesExt', 'congExtLib', 'pureSimpsExt', 'boolSimpsExt')
                   for s in ('.sml', '.sig'))
MANIFEST = HERE / 'task16-source-manifest.json'
MANIFEST_SHA256 = (
    'de0a16b4cef0de706df34ba247e3ff1332f53e1182bf548f1dd7b0315311100a')
ROOTS = ('simpLib', 'boolSimps', 'congLib', 'combinSimps')


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def seal(data):
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


@lru_cache(maxsize=None)
def git_source(revision, path):
    # Deliberately bytes: universal-newline decoding would waive CRLF drift.
    return subprocess.check_output(
        ['git', '-C', str(ROOT), 'show', revision + ':' + path])


def forbidden_module(name):
    return (name.endswith(('Ext', 'ExtLib')) or
            name.startswith('simpMarker') or
            name in {'SplitData', 'splitLib', 'splitPersistLib'})


def validate_manifest(manifest):
    """Check closure as well as the independent immutable manifest seal."""
    require(manifest['schema'] == 1 and manifest['task_start'] == START,
            'wrong source manifest version/revision')
    require(manifest['roots'] == list(ROOTS), 'wrong ordinary roots')
    nodes = manifest['modules']
    require(set(ROOTS) <= nodes.keys(), 'missing ordinary root')
    visited = set()

    def visit(name):
        require(name in nodes, 'missing transitive module: ' + name)
        require(not forbidden_module(name),
                'ordinary dependency reaches extension resource: ' + name)
        if name in visited:
            return
        visited.add(name)
        node = nodes[name]
        require(node['sources'], 'module without defining sources: ' + name)
        for path in node['sources']:
            require(not Path(path).is_absolute() and
                    '..' not in Path(path).parts,
                    'non-repository source path: ' + path)
        for name in node['basis_or_local_names']:
            require(not forbidden_module(name),
                    'ordinary unresolved extension resource: ' + name)
        for dependency in node['imports']:
            visit(dependency)

    for root in ROOTS:
        visit(root)
    require(visited == nodes.keys(), 'unreachable source manifest module')
    # Heap-preloaded repository services have no sigobj import edge. Include
    # their defining inputs too, rather than calling HOLFileSys/holpathdb and
    # bootstrap code unexamined external dependencies.
    preloaded = manifest['preloaded_sources']
    require(preloaded and all(not Path(p).is_absolute() and
                              '..' not in Path(p).parts for p in preloaded),
            'invalid preloaded source inputs')
    return ({p for node in nodes.values() for p in node['sources']} |
            set(preloaded))


def read_manifest():
    data = MANIFEST.read_bytes()
    require(seal(data)['sha256'] == MANIFEST_SHA256,
            'reviewed source manifest changed')
    manifest = json.loads(data)
    validate_manifest(manifest)
    return manifest
