#!/usr/bin/env python3
"""Live TASK27 defining-source dependency/control gate (no builds).

The TASK16 conservative runtime graph is trusted only with its independent
seal AND byte-identical transitive defining inputs. Fresh holdeptool output
on both the live snapshot and immutable references crosschecks that graph.
Aliases, computed loads and hidden registrations are rejected by byte equality,
not by pretending holdeptool (or a Python regexp) is an exhaustive SML parser.

Grammar/templates and theory scripts contain build-time references, not just
runtime imports. Keep those observations separate from the reviewed runtime
edges. No .ui/.uo, generated Theory.sml, heap or aspirational interfaces graph
is an oracle. An independent parent fresh-process gate must check actual loaded
paths/products and runtime pointer identities; this audit cannot certify them.
Only the Poly/standard-kernel TASK16 closure is transitive here. BasicProvers
and bossLib are additional byte-exact ordinary registry/default sentinels,
not a claim to have closed the entire boss dependency graph.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

import audit_task16 as prior

HERE, ROOT, SRC = prior.HERE, prior.ROOT, prior.SRC
BASE, START = prior.BASE, prior.START
REVIEW = 'c707baca802d7e0d22e7e8045a0dc5d3567bd7a9'
TOOL = ROOT / 'bin/holdeptool.exe'
ORDINARY_SENTINELS = tuple(directory + name + suffix
                           for directory, name in (
                               ('src/basicProof/', 'BasicProvers'),
                               ('src/boss/', 'bossLib'))
                           for suffix in ('.sml', '.sig'))
EXTENSIONS = tuple(sorted(set(prior.EXTENSIONS) | {
    SRC + name for name in (
        'combinSimpsExt.sml', 'combinSimpsExt.sig',
        'simpMarkerLib.sml', 'simpMarkerLib.sig', 'simpMarkerScript.sml',
        'splitLib.sml', 'splitLib.sig', 'SplitData.sml', 'SplitData.sig',
        'splitPersistLib.sml')} | {
            'src/boss/trackedSimpDefaults' + s for s in ('.sml', '.sig')}))

# Exactly six shared-identity inputs differ from pinned develop. TASK16 sealed
# them at START; everything else in the ordinary closure is exactly BASE.
SHARED_DELTAS = {
    'src/1/ThmAttribute.sig':
        'read-only exact installed attrfuns lookup API; no second registry',
    'src/1/ThmAttribute.sml':
        'two read-only lookup functions over the original Context registry',
    SRC + 'Cond_rewr.sig':
        'expose existing permutation predicate; document live depth control',
    SRC + 'Cond_rewr.sml':
        'extract reporter to SimpTracking; alias the single shared extent',
    SRC + 'SimpTracking.sig':
        'new internal shared reporter/bracketing interface',
    SRC + 'SimpTracking.sml':
        'new sole thread-local reporter slot extracted from Cond_rewr',
}
SHARED_ADDED = frozenset(SRC + 'SimpTracking' + s
                         for s in ('.sml', '.sig'))

# Reviewed extension deltas, NOT permission to accept HEAD generally.
# Each must equal its immutable REVIEW blob; report both old/new hashes.
DELTAS = {
    SRC + 'simpExtLib.sml':
        'TASK17-24 tracked installation, policy/quota and explicit recipes',
    SRC + 'simpExtLib.sig':
        'TASK17-24 explicit tracked API; no ordinary promotion adapter',
    SRC + 'TraverseExt.sml':
        'TASK17-22 child-first staging, aborts and configured traversal',
    SRC + 'TraverseExt.sig':
        'TASK17-22 configured traversal and policy callback contract',
    SRC + 'simpMarkerLib.sml':
        'TASK20 qualified directives and lossless nested actual bounds',
    SRC + 'simpMarkerLib.sig':
        'TASK20 explicit prepared directive interface',
    SRC + 'SplitData.sml':
        'TASK23 context-owned transactional persistence and pointer ownership',
    SRC + 'splitLib.sig':
        'TASK23 explicit persistence API documentation',
    SRC + 'combinSimpsExt.sml':
        'TASK24 new explicit typed COMBIN recipe, not copied compiled state',
    SRC + 'combinSimpsExt.sig':
        'TASK24 new explicit typed COMBIN recipe signature',
    'src/boss/trackedSimpDefaults.sml':
        'TASK24 explicit typed provider; missing provider raises, no fallback',
    'src/boss/trackedSimpDefaults.sig':
        'TASK24 new explicit typed recipe/provider boundary',
}
ADDED = frozenset({SRC + 'combinSimpsExt' + s
                   for s in ('.sml', '.sig')} |
                  {'src/boss/trackedSimpDefaults' + s
                   for s in ('.sml', '.sig')})

# These mappings already exist in the sealed TASK16 manifest. holdeptool on
# their *defining inputs* also sees build-time imports/template/make syntax.
# Exact reference analysis below pins every such name; this is not a wildcard
# allowance for arbitrary unresolved dependencies or new source changes.
MAPPED_INPUTS = {
    'HOLsexp.grm': 'ML-Yacc defining grammar, not emitted parser structure',
    'HOLsexp.grm-sig': 'ML-Yacc defining grammar, not emitted signature',
    'SHA1_ML': 'word-size alias/template plus Holmakefile',
    'Systeml': 'configured platform implementation plus configure script',
    'Term': 'standard-kernel FinalTerm alias',
    'Thm': 'standard-kernel theorem template plus Holmakefile',
    'Thm-sig': 'standard-kernel theorem signature template plus Holmakefile',
    'Type': 'standard-kernel FinalType alias',
    'base_lexer': 'ML-Lex defining input plus Holmakefile',
    'boolSimpsContextTheory': 'theory construction script',
    'canonContextTheory': 'theory construction script',
    'boolTheory': 'theory construction script',
    'combinTheory': 'theory construction script',
    'markerTheory': 'theory construction script',
    'satTheory': 'theory construction script',
}
# Not a simplifier extension: a local String helper in this exact sealed file.
LOCAL_NAMES = {
    'tools/Holmake/toml/parseTOMLUtil.sml': {
        'StringExt': 'local String.implodeRev helper, not a loader module'}}

# Seal of sorted per-defining-input holdeptool observations on the immutable
# references. This prevents an empty/stale/replaced analyzer passing merely
# because it produces the same wrong answer on both snapshots.
ANALYSIS_SHA256 = (
    '57c7c9aa9e9da63327f55fd3a445b65223b17f27888cc7f414b61742aa7b9692')

require, seal, git_source = prior.require, prior.seal, prior.git_source


def digest(value):
    return hashlib.sha256(json.dumps(
        value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def forbidden_module(name):
    return (prior.forbidden_module(name) or name == 'trackedSimpDefaults')


def validate_manifest(manifest):
    paths = prior.validate_manifest(manifest)
    for name, node in manifest['modules'].items():
        for dependency in (name, *node['imports'],
                           *node['basis_or_local_names']):
            require(not forbidden_module(dependency),
                    'ordinary dependency reaches extension: ' + dependency)
        for path in node['sources']:
            require(not forbidden_module(Path(path).stem),
                    'ordinary defining input is extension-owned: ' + path)
    for path in manifest['preloaded_sources']:
        require(not forbidden_module(Path(path).stem),
                'ordinary preload is extension-owned: ' + path)
    return paths


def source_paths(manifest):
    return (validate_manifest(manifest) | set(EXTENSIONS) |
            set(ORDINARY_SENTINELS))


def read_sources():
    return {p: (ROOT / p).read_bytes()
            for p in sorted(source_paths(prior.read_manifest()))}


def reference_revision(path):
    if path in EXTENSIONS:
        return REVIEW if path in DELTAS else START
    return START if path in SHARED_DELTAS else BASE


def baseline_source(path):
    if path in ADDED or path in SHARED_ADDED:
        return None
    return git_source(START if path in EXTENSIONS else BASE, path)


def reference_sources(paths):
    return {p: git_source(reference_revision(p), p) for p in sorted(paths)}


@lru_cache(maxsize=None)
def delta_records():
    records = {}
    for path, reason in sorted({**SHARED_DELTAS, **DELTAS}.items()):
        before = baseline_source(path)
        revision = reference_revision(path)
        after = git_source(revision, path)
        require(before != after, 'vacuous reviewed delta: ' + path)
        records[path] = dict(
            reason=reason,
            baseline_revision=START if path in EXTENSIONS else BASE,
            baseline=None if before is None else seal(before),
            reviewed_revision=revision, reviewed=seal(after))
    return records


def analyze_sources(sources):
    """Run the existing analyzer, serially, on a private byte-exact snapshot.

    Use file mode (HOLSource.fileToReader), not stdin, for theory quotations.
    No Holmake/build is invoked and no build/cache files are read or written.
    Temporary inputs are removed even on an analyzer error.
    """
    result = {}
    with tempfile.TemporaryDirectory(prefix='task27-deps-') as directory:
        for path, data in sorted(sources.items()):
            target = Path(directory) / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            completed = subprocess.run(
                [str(TOOL), str(target)], capture_output=True, timeout=30,
                check=True)
            require(not completed.stderr,
                    'dependency analyzer diagnostics for ' + path + ': ' +
                    completed.stderr.decode(errors='replace'))
            names = completed.stdout.decode().splitlines()
            require(names == sorted(set(names)) and all(names),
                    'malformed dependency analyzer output: ' + path)
            result[path] = names
    return result


def check_analysis(manifest, observations, baseline):
    require(observations.keys() == baseline.keys(),
            'missing/unexpected fresh defining-source dependency inputs')
    require(digest(baseline) == ANALYSIS_SHA256,
            'reference dependency analyzer output differs from reviewed seal')
    for path, names in observations.items():
        require(names == baseline[path],
                'fresh defining-source dependencies changed: ' + path)
    nodes = manifest['modules']
    graph, mapped = {}, set()
    ordinary_paths = validate_manifest(manifest) | set(ORDINARY_SENTINELS)
    for path in ordinary_paths:
        for name in observations[path]:
            require(not forbidden_module(name) or
                    name in LOCAL_NAMES.get(path, {}),
                    'ordinary defining-source extension edge: ' + path +
                    ' -> ' + name)
    for name, node in sorted(nodes.items()):
        observed = set().union(*(set(observations[p])
                                 for p in node['sources']))
        extras = observed - set(node['imports']) - set(
            node['basis_or_local_names'])
        if extras:
            require(name in MAPPED_INPUTS,
                    'manifest omits defining-source dependencies: ' + name)
            mapped.add(name)
        graph[name] = dict(
            sources=node['sources'],
            reviewed_runtime_imports=node['imports'],
            defining_source_names=sorted(observed),
            defining_source_imports=sorted(observed & nodes.keys()),
            basis_local_or_build_names=sorted(observed - nodes.keys()),
            mapped_input_reason=MAPPED_INPUTS.get(name),
            additional_defining_input_names=sorted(extras))
    require(mapped == MAPPED_INPUTS.keys(),
            'reviewed defining-input mappings changed')
    # Crucial source-discovered edge: old .uo metadata could omit this.
    require('SimpTracking' in graph['Cond_rewr']['defining_source_imports'] and
            'ThreadLocal' in graph['SimpTracking']['defining_source_imports'],
            'fresh dependency graph lost the shared tracking path')
    return graph


# Explanatory anchors, not a parser-based proof. The whole-file seals enforce
# everything around them (including private scopes, shadow declarations and
# registry miss branches). Counts are deliberately explicit for shared users.
IDENTITIES = {
    'tracking_slot': (
        (SRC + 'SimpTracking.sml', b'ThreadLocal.new ()', 1),
        (SRC + 'Cond_rewr.sml',
         b'val note_rewrite = SimpTracking.note_rewrite', 1),
        (SRC + 'Cond_rewr.sml',
         b'val with_tracking = SimpTracking.with_tracking', 1),
        (SRC + 'Cond_rewrExt.sml', b'SimpTracking.note_rewrite th', 2),
        (SRC + 'simpLib.sml', b'val track = with_tracking', 1),
        (SRC + 'simpExtLib.sml', b'val track = with_tracking', 1)),
    'conditional_depth': (
        (SRC + 'Cond_rewr.sml', b'val stack_limit = ref 4', 1),
        (SRC + 'Cond_rewrExt.sml', b'!Cond_rewr.stack_limit', 2),
        (SRC + 'TraverseExt.sml', b'!Cond_rewr.stack_limit', 2)),
    'actual_bounds': (
        ('src/1/BoundedRewrites.sml',
         b'datatype control = UNBOUNDED | BOUNDED of int ref', 1),
        (SRC + 'Cond_rewrExt.sml', b'BoundedRewrites.BOUNDED r', 1),
        (SRC + 'Cond_rewrExt.sml', b'before Portable.dec r', 2)),
    'trace': (
        (SRC + 'Trace.sml', b'datatype action =', 1),
        (SRC + 'Trace.sml', b'val trace_level = ref 0', 1),
        (SRC + 'Trace.sml', b'Listener.new_listener()', 1),
        (SRC + 'Trace.sml',
         b'Feedback.register_trace("simplifier", trace_level, 7)', 1)),
    'shared_types': (
        (SRC + 'OpeningExt.sml', b'type congproc = Opening.congproc', 1),
        (SRC + 'TravrulesExt.sml', b'type preorder = Travrules.preorder', 1),
        (SRC + 'TravrulesExt.sml', b'type travrules = Travrules.travrules', 1),
        (SRC + 'TraverseExt.sml', b'type context = exn', 1),
        (SRC + 'TraverseExt.sml',
         b'datatype reducer = LIFTED of Traverse.reducer', 1)),
    'shared_exceptions': (
        ('src/prekernel/Feedback.sml', b'exception HOL_ERR of hol_error', 1),
        ('src/1/Conv.sml', b'exception UNCHANGED', 1),
        ('src/portableML/Portable.sml',
         b'exception Interrupt = MLSYSPortable.Interrupt', 1)),
    'typed_registries_no_fallback': (
        (SRC + 'simpLib.sml', b'name = "simpLib.ssfragDB"', 1),
        (SRC + 'simpExtLib.sml', b'name = "simpExtLib.ssfragDB"', 1),
        (SRC + 'simpExtLib.sml',
         b'fun lookup_named_frag n = Symtab.lookup (ssfragDB ()) n', 1),
        ('src/boss/trackedSimpDefaults.sml',
         b'Unprepared tracked default provider; '
         b'explicitly build and install one',
         1)),
    'split_owner': (
        (SRC + 'SplitData.sml', b'name="splitLib.registration"', 1),
        (SRC + 'SplitData.sml', b'name="splitLib.rules"', 1),
        (SRC + 'SplitData.sml',
         b'Portable.pointer_eq (attribute,current)', 1)),
}


def check_identities(sources):
    result = {}
    for identity, anchors in IDENTITIES.items():
        result[identity] = []
        for path, anchor, count in anchors:
            require(sources[path].count(anchor) == count,
                    'shared identity anchor changed: ' + identity + ': ' +
                    path)
            result[identity].append(dict(source=path, anchor=anchor.decode(),
                                         occurrences=count))
    return result


def audit(sources=None):
    # Read live inputs on every invocation. No historical snapshot default,
    # baseline substitution, token/comment normalization or catch-and-skip.
    manifest = prior.read_manifest()
    paths = source_paths(manifest)
    if sources is None:
        sources = read_sources()
    require(paths == sources.keys(), 'missing/unexpected live audited sources')
    require(all(isinstance(data, bytes) for data in sources.values()),
            'live source audit requires bytes')
    references = reference_sources(paths)
    for path in sorted(paths):
        category = ('baseline ordinary' if path in prior.ORDINARY or
                    path in ORDINARY_SENTINELS else
                    'reviewed extension/control' if path in EXTENSIONS else
                    'ordinary transitive')
        require(sources[path] == references[path],
                category + ' source bytes changed: ' + path)
    deltas = delta_records()
    require(set(SHARED_DELTAS) <= validate_manifest(manifest),
            'shared identity delta outside ordinary closure')
    require(set(DELTAS) <= set(EXTENSIONS), 'non-extension source delta')
    identities = check_identities(sources)
    # Do not replace the live analysis with cached reference observations.
    baseline = analyze_sources(references)
    observations = analyze_sources(sources)
    graph = check_analysis(manifest, observations, baseline)
    return dict(
        task=27, structural='pass',
        head=subprocess.check_output(
            ['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip(),
        baseline=BASE, manifest_snapshot=START,
        reviewed_extension_revision=REVIEW,
        source_manifest=prior.MANIFEST_SHA256,
        ordinary_roots=list(prior.ROOTS), transitive_modules=len(graph),
        transitive_sources=len(validate_manifest(manifest)),
        ordinary_source_deltas={},
        shared_identity_deltas={p: deltas[p] for p in sorted(SHARED_DELTAS)},
        reviewed_extension_deltas={p: deltas[p] for p in sorted(DELTAS)},
        sources={p: dict(
            actual=seal(sources[p]),
            baseline=None if baseline_source(p) is None else
            seal(baseline_source(p)),
            baseline_revision=START if p in EXTENSIONS else BASE,
            reviewed_reference=seal(references[p]),
            reviewed_revision=reference_revision(p)) for p in sorted(paths)},
        analyzer=dict(path='bin/holdeptool.exe',
                      binary=seal(TOOL.read_bytes()),
                      reference_observations_sha256=digest(baseline),
                      live_observations_sha256=digest(observations)),
        dependency_graph=graph, defining_source_dependencies=observations,
        preloaded_sources=manifest['preloaded_sources'],
        ordinary_sentinels=list(ORDINARY_SENTINELS),
        reviewed_local_names=LOCAL_NAMES, identities=identities,
        scope='live byte-exact defining-source closure and control ownership; '
              'not an exhaustive SML parser, emitted-product, '
              'alternate-kernel or runtime load/path/pointer-identity '
              'certificate; parent fresh '
              'runtime path/identity gate required separately')


if __name__ == '__main__':
    try:
        print(json.dumps(audit(), indent=2, sort_keys=True))
    except (AssertionError, KeyError, OSError, UnicodeError,
            subprocess.SubprocessError) as error:
        raise SystemExit('TASK27 live source audit failed: ' + str(error))
