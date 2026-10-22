#!/usr/bin/env python3
"""Offline TASK_16 whole-source correspondence and ordinary dependency gate.

Byte equality, not token equivalence: even comments in simpLib's restored pair
must match pinned develop. Extension compiler pairs stay at TASK_16 start.
The reviewed manifest covers the transitive ordinary Poly/standard-kernel
source closure, including shared facilities and signatures. It reads no build
products. This is not an execution, fresh-load or performance receipt.
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


def source_paths(manifest):
    return validate_manifest(manifest) | set(ORDINARY) | set(EXTENSIONS)


def read_sources():
    return {p: (ROOT / p).read_bytes()
            for p in sorted(source_paths(read_manifest()))}


def audit(sources=None):
    manifest = read_manifest()
    paths = source_paths(manifest)
    if sources is None:
        sources = read_sources()
    require(paths == sources.keys(), 'missing/unexpected audited sources')
    require(all(isinstance(s, bytes) for s in sources.values()),
            'source audit requires bytes')

    # No allowances for alternative representation, constructor staging,
    # callback order, history, tactics, names, printer spelling or shadow code.
    for path in ORDINARY:
        require(sources[path] == git_source(BASE, path),
                'ordinary source/signature differs from pinned develop: ' +
                path)
    for path in EXTENSIONS:
        require(sources[path] == git_source(START, path),
                'extension compiler differs from task start: ' + path)

    # This seal is transitive, not a grep of simpLib's direct imports and not
    # the aspirational interfaces/graph.json. Altering a shared dependency to
    # import/load an extension (even through a string or an alias) fails here.
    # All shared identities, including SimpTracking's sole slot, stay intact.
    dependencies = validate_manifest(manifest)
    for path in sorted(dependencies - set(ORDINARY)):
        require(sources[path] == git_source(START, path),
                'ordinary transitive source changed: ' + path)
    return dict(task=16, structural='pass', baseline=BASE, task_start=START,
                ordinary={p: seal(sources[p]) for p in ORDINARY},
                extension_compiler={p: seal(sources[p]) for p in EXTENSIONS},
                source_manifest=MANIFEST_SHA256,
                ordinary_roots=list(ROOTS),
                transitive_modules=len(manifest['modules']),
                transitive_sources=len(dependencies),
                scope='byte/source correspondence only; not runtime, '
                      'fresh-process loading, generated-product or timing '
                      'validation')


if __name__ == '__main__':
    try:
        print(json.dumps(audit(), indent=2))
    except (AssertionError, KeyError, OSError,
            subprocess.CalledProcessError) as error:
        raise SystemExit('TASK_16 audit failed: ' + str(error))
