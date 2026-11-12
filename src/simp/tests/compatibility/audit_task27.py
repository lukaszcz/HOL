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
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

import source_manifest as prior

HERE, ROOT, SRC = prior.HERE, prior.ROOT, prior.SRC
BASE, START = prior.BASE, prior.START
REVIEW = 'c707baca802d7e0d22e7e8045a0dc5d3567bd7a9'
# Reviewed deltas of TASK31 and TASK34.  TASK31: one rewrite-tracking extent,
# owned by develop's Cond_rewr and shared by both engines through the one
# added Cond_rewr.note_rewrite spec; Cond_rewr.sml itself is pinned develop
# again, and Cond_rewrExt keeps its own is_var_perm.  TASK34: the abstract
# TraverseExt.reducer, its congExtLib client, SplitData.preflight using
# is_attribute, and ThmAttribute.attribute_fns_of.  The files
# below are sealed by content (git blob id), not by the id of a commit, so
# the seal survives rebases and squashes.  A change to one of them needs a
# new blob and a new reason here.
REVIEWED_31 = {
    SRC + 'Cond_rewr.sig': dict(
        blob='7ab7bafd0ea45756b6f4ac2a35447e7da33fe085',
        reason='develop plus the note_rewrite spec and its comment; the '
               'signature is otherwise unchanged'),
    SRC + 'Cond_rewrExt.sml': dict(
        blob='378b9bbe6dd5c3a2404a5ec7571f7d61a422bac1',
        reason='TASK31 own pure is_var_perm (audited token-equal to '
               'develop) and reporting through Cond_rewr.note_rewrite'),
    SRC + 'simpExtLib.sml': dict(
        blob='c146d65ff7b1d7014f71bcfb46fe4ed4c88e9d05',
        reason='TASK17-24 tracked installation, policy/quota and explicit '
               'recipes; TASK31 track is Cond_rewr.with_tracking'),
    SRC + 'simpExtLib.sig': dict(
        blob='247f6a892c57f90a74035b2186fbab6bac174aea',
        reason='TASK17-24 explicit tracked API; TASK31 documents the one '
               'tracking extent shared with simpLib.track'),
    # TASK34: TraverseExt.reducer becomes abstract (no LIFTED reverse
    # adapter); CONTEXT_REDUCER and CONFIG_REDUCER are constructor functions.
    SRC + 'TraverseExt.sig': dict(
        blob='d3829da16e472913fc10fd41e00f92eb033a5355',
        reason='TASK17-22 configured traversal and policy callback contract; '
               'TASK34 abstract reducer type with explicit constructor '
               'functions and reducer_kind, no reverse adapter'),
    SRC + 'TraverseExt.sml': dict(
        blob='1d370733b1bd28886dbc31566adfe094faad3bc4',
        reason='TASK17-22 child-first staging, aborts and configured '
               'traversal; TASK34 reducer_kind for the abstract reducer'),
    SRC + 'congExtLib.sml': dict(
        blob='42e535d4924e82a7aa55804673fa3a8e27220852',
        reason='TASK34 eq_reducer_wrapper reads any reducer through '
               'reducer_config_data; the reducer type is abstract'),
    # TASK34 removes the ambient attribute_fns; only attribute_fns_of stays.
    # SplitData.preflight uses ThmAttribute.is_attribute, develop's lookup.
    SRC + 'SplitData.sml': dict(
        blob='eb703ea016b3c2d7c7778ccf707b9d9c096a3071',
        reason='TASK23 context-owned transactional persistence and pointer '
               'ownership; TASK34 preflight uses develop is_attribute'),
    'src/1/ThmAttribute.sig': dict(
        blob='0277788be43d67ed8724d677c562d61e125a9e69',
        reason='read-only exact installed attrfuns lookup API in a '
               'supplied Context; no second registry'),
    'src/1/ThmAttribute.sml': dict(
        blob='b2161e0effd516e2bfffdbfba81bcd5c5a708e21',
        reason='one read-only lookup function over the original Context '
               'registry'),
}
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

# Exactly three shared-identity inputs differ from pinned develop:
# ThmAttribute.sig, ThmAttribute.sml (TASK16, resealed by TASK34) and
# Cond_rewr.sig (TASK31). All three are sealed by REVIEWED_31 blob ids, not
# by a revision. Everything else in the ordinary closure is exactly BASE,
# Cond_rewr.sml included.
SHARED_DELTAS = {
    'src/1/ThmAttribute.sig':
        REVIEWED_31['src/1/ThmAttribute.sig']['reason'],
    'src/1/ThmAttribute.sml':
        REVIEWED_31['src/1/ThmAttribute.sml']['reason'],
    SRC + 'Cond_rewr.sig': REVIEWED_31[SRC + 'Cond_rewr.sig']['reason'],
}
SHARED_ADDED = frozenset()

# Reviewed extension deltas, NOT permission to accept HEAD generally.
# Each must equal its immutable REVIEW blob (or, for the REVIEWED_31 files,
# the blob recorded above); report both old/new hashes.
DELTAS = {
    SRC + 'simpExtLib.sml': REVIEWED_31[SRC + 'simpExtLib.sml']['reason'],
    SRC + 'simpExtLib.sig': REVIEWED_31[SRC + 'simpExtLib.sig']['reason'],
    SRC + 'TraverseExt.sml': REVIEWED_31[SRC + 'TraverseExt.sml']['reason'],
    SRC + 'TraverseExt.sig': REVIEWED_31[SRC + 'TraverseExt.sig']['reason'],
    SRC + 'congExtLib.sml': REVIEWED_31[SRC + 'congExtLib.sml']['reason'],
    SRC + 'Cond_rewrExt.sml': REVIEWED_31[SRC + 'Cond_rewrExt.sml']['reason'],
    SRC + 'simpMarkerLib.sml':
        'TASK20 qualified directives and lossless nested actual bounds',
    SRC + 'simpMarkerLib.sig':
        'TASK20 explicit prepared directive interface',
    SRC + 'SplitData.sml': REVIEWED_31[SRC + 'SplitData.sml']['reason'],
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
ADDED = frozenset({SRC + 'combinSimpsExt' + s for s in ('.sml', '.sig')} |
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
    'd01da425ad91723363c9cec0284636af6bd88a21cfc56d07743fdcbcf8b781c1')

require, seal, git_source = prior.require, prior.seal, prior.git_source


def digest(value):
    return hashlib.sha256(json.dumps(
        value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def blob_id(data):
    # The git blob id: stable across rebases, squashes and cherry-picks.
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


def forbidden_module(name):
    return (prior.forbidden_module(name) or
            name in ('trackedSimpDefaults', 'SimpTracking'))


# TASK31 overlay on the sealed TASK16 manifest (which describes the closure
# at START, where Cond_rewr imported the extracted SimpTracking).  Cond_rewr
# is develop's again: it imports ThreadLocal directly and SimpTracking is
# gone.  The overlay asserts the exact TASK16 shape it edits.
OVERLAY31_REMOVED = {
    'SimpTracking': dict(
        sources=['src/simp/src/SimpTracking.sig',
                 'src/simp/src/SimpTracking.sml'],
        imports=['HolKernel', 'Overlay', 'Thm', 'ThreadLocal'],
        basis_or_local_names=['List'])}
OVERLAY31_CONDREWR_OLD = 'SimpTracking'
OVERLAY31_CONDREWR_NEW = 'ThreadLocal'


def overlay31(manifest):
    manifest = copy.deepcopy(manifest)
    nodes = manifest['modules']
    for name, node in OVERLAY31_REMOVED.items():
        require(nodes.get(name) == node,
                'TASK16 manifest differs from the TASK31 overlay base: ' +
                name)
        del nodes[name]
    imports = nodes['Cond_rewr']['imports']
    require(OVERLAY31_CONDREWR_OLD in imports and
            OVERLAY31_CONDREWR_NEW not in imports,
            'TASK16 Cond_rewr node differs from the TASK31 overlay base')
    imports.remove(OVERLAY31_CONDREWR_OLD)
    imports.append(OVERLAY31_CONDREWR_NEW)
    imports.sort()
    return manifest


def read_manifest():
    return overlay31(prior.read_manifest())


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
            for p in sorted(source_paths(read_manifest()))}


def reference_revision(path):
    if path in REVIEWED_31:
        return 'blob:' + REVIEWED_31[path]['blob']
    if path in EXTENSIONS:
        return REVIEW if path in DELTAS else START
    return START if path in SHARED_DELTAS else BASE


def baseline_source(path):
    if path in ADDED or path in SHARED_ADDED:
        return None
    return git_source(START if path in EXTENSIONS else BASE, path)


def reference_source(path, live):
    """Immutable reference bytes; a REVIEWED_31 file is its own reference
    once its content matches the recorded blob id."""
    if path in REVIEWED_31:
        require(blob_id(live) == REVIEWED_31[path]['blob'],
                'reviewed extension/control source bytes changed: ' +
                path)
        return live
    return git_source(reference_revision(path), path)


def reference_sources(sources):
    return {p: reference_source(p, sources[p]) for p in sorted(sources)}


@lru_cache(maxsize=None)
def delta_records():
    records = {}
    for path, reason in sorted({**SHARED_DELTAS, **DELTAS}.items()):
        before = baseline_source(path)
        revision = reference_revision(path)
        after = reference_source(path, (ROOT / path).read_bytes())
        require(before != after, 'vacuous reviewed delta: ' + path)
        records[path] = dict(
            reason=reason,
            baseline_revision=START if path in EXTENSIONS else BASE,
            baseline=None if before is None else seal(before),
            reviewed_revision=revision, reviewed=seal(after))
    return records


DECLARATION = re.compile(
    r'^[ \t]*(?:fun|val|type|datatype|structure|local|open|exception|end)\b',
    re.M)


# HOL's quotation filter (HOLSource.ToSML, from tools/parsing) is applied
# to every .sml file before the compiler reads it.  Under Poly/ML the build
# applies it in-process when it loads the module (QUse.use, through
# HOLSource.ToSML.mkPullTranslator); only Moscow ML's Holmake runs it as
# `bin/unquote file1 file2`.  The two give the same output, and the file
# name affects only what #(FILE) expands to.  Its declaration forms
# (`Quote x = f:`, `Theorem`, ...) open quotations with no quotation
# character, and a quotation body is not SML, so a scanner that read the
# unfiltered text could be desynchronised from the compiler, or miss a
# binding.  The var_perm audit therefore reads the filter's output, the
# text the compiler sees, in which a quotation is an ordinary string or
# QUOTE list.
UNQUOTE = ROOT / 'bin/unquote'


def quote_filter(source):
    """`source` (bytes) as HOL's quotation filter writes it for the
    compiler (two-file, non-interactive mode, as in a build).  Fails closed
    when the filter is missing or fails, or writes nothing or diagnostics."""
    require(UNQUOTE.is_file(), 'quotation filter missing (build HOL): ' +
            str(UNQUOTE))
    with tempfile.TemporaryDirectory(prefix='task27-unquote-') as directory:
        infile, outfile = Path(directory) / 'in.sml', Path(directory) / 'out'
        infile.write_bytes(source)
        try:
            completed = subprocess.run(
                [str(UNQUOTE), str(infile), str(outfile)],
                capture_output=True, timeout=60,
                stdin=subprocess.DEVNULL)
        except (OSError, subprocess.SubprocessError) as error:
            raise AssertionError('quotation filter did not run: ' +
                                 str(error))
        require(completed.returncode == 0 and not completed.stderr,
                'quotation filter failed: ' +
                completed.stderr.decode(errors='replace'))
        require(outfile.is_file(), 'quotation filter wrote no output')
        filtered = outfile.read_bytes().decode()
    require(filtered.strip(), 'quotation filter wrote empty output')
    return filtered


# A cheap pre-check that stays: after filtering, no quotation character can
# remain outside a string, so one that does means the filter and this
# scanner disagree, and the text is refused.
QUOTATION = re.compile('[‘’“”`]')
SML_KEYWORDS = frozenset("""
    abstype and andalso as case datatype do else end eqtype exception fn
    fun functor handle if in include infix infixr let local nonfix of op
    open orelse raise rec sharing sig signature struct structure then
    type val where while with withtype""".split())
WORD = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")


def lex(text):
    r"""A small, exact SML lexer for what the var_perm audit needs, for
    text already passed through the quotation filter (`quote_filter`).
    Returns `(kept, blanked)`: `text` without its comments (nested; `(*)`
    opens one), each replaced by a space, with string literals (every
    escape, and the `\<whitespace>\` gap, which is read explicitly) and
    `#"c"` literals kept, or blanked to spaces between their quotes.  The
    two have the same length, so an offset in one is the same text in the
    other.  Anything it cannot classify exactly is refused: an
    unterminated comment, string or gap, and a quotation character outside
    a comment or string."""
    kept, blank, i, depth, n = [], [], 0, 0, len(text)
    while i < n:
        c, two = text[i], text[i:i + 2]
        if two == '(*':
            if depth == 0:
                kept.append(' ')
                blank.append(' ')
            depth += 1
            i += 2
        elif depth:
            if two == '*)':
                depth -= 1
                i += 2
            else:
                i += 1
        elif c == '"':
            j = i + 1
            while True:
                require(j < n, 'unterminated string literal')
                if text[j] == '"':
                    break
                if text[j] != '\\':
                    j += 1
                elif text[j + 1:j + 2].isspace():
                    k = j + 1
                    while k < n and text[k].isspace():
                        k += 1
                    require(k < n and text[k] == '\\',
                            'unterminated or malformed string gap')
                    j = k + 1
                else:
                    j += 2
            kept.append(text[i:j + 1])
            blank.append('"' + ' ' * (j - i - 1) + '"')
            i = j + 1
        else:
            require(not QUOTATION.match(c), 'quotation outside a comment')
            kept.append(c)
            blank.append(c)
            i += 1
    require(depth == 0, 'unterminated comment')
    return ''.join(kept), ''.join(blank)


def strip_comments(text):
    return lex(text)[0]


SYMBOLIC = frozenset('!%&$#+-/:<=>?@\\~`^|*')


def binding_equals(text, start, end):
    """The position of the first `=` token of text[start:end] at bracket
    depth 0, or `end` if there is none.  An `=` inside a symbolic
    identifier (`<=>`) is not a token of its own."""
    depth = 0
    for i in range(start, end):
        c = text[i]
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif (c == '=' and depth <= 0 and text[i - 1] not in SYMBOLIC
              and text[i + 1:i + 2] not in SYMBOLIC):
            return i
    return end


def binder_heads(text):
    """(position, names) for each val/fun/and/exception/datatype/structure
    declaration of comment-free `text`: the names in its head (up to the
    first `=` token at bracket depth 0 of (), [] and {}, so that the names
    in a record or tuple pattern, `val {a = x} = ...`, are in it (a label
    is counted as a name too, conservatively); or to the next declaration at
    the start of a line; a datatype, or an `and` joined to one, always
    runs to that, to take in its constructors)."""
    heads, mode = [], None
    for m in re.finditer(r'\b(val|fun|and|exception|datatype|structure)\b',
                         text):
        kw = m.group(1)
        mode = mode if kw == 'and' else kw
        nxt = DECLARATION.search(text, m.end())
        end = len(text) if nxt is None else nxt.start()
        if mode != 'datatype':
            end = binding_equals(text, m.end(), end)
        heads.append((m.start(), WORD.findall(text[m.end():end])))
    return heads


def fixity_names(text):
    """The tokens named by each infix/infixr/nonfix declaration of
    comment-free `text`, up to `;` or the next declaration at the start of
    a line."""
    names = set()
    for m in re.finditer(r'\b(?:infix|infixr|nonfix)\b', text):
        nxt = DECLARATION.search(text, m.end())
        end = len(text) if nxt is None else nxt.start()
        semi = text.find(';', m.end(), end)
        end = end if semi < 0 else semi
        names.update(text[m.end():end].split())
    return names


def block_span(text):
    start = text.find('fun vperm')
    perm = text.find('fun is_var_perm', start)
    require(start >= 0 and perm > start, 'vperm/is_var_perm block not found')
    after = DECLARATION.search(text, perm + len('fun is_var_perm'))
    return start, len(text) if after is None else after.start()


def vperm_block(source):
    """The tokens of `fun vperm` and `fun is_var_perm` in `source` (bytes),
    as the quotation filter writes it and with comments removed, up to the
    next declaration keyword at the start of a line, so that nothing after
    the last parenthesis of is_var_perm escapes the comparison.  Fails
    closed (see `quote_filter` and `lex`) on what it cannot classify, on
    `functor` and `abstype` outside comments and strings (a functor
    parameter, or an abstype's constructors, bind names with none of the
    scanned keywords), and on shadowing: `vperm` and `is_var_perm` must
    each be bound exactly once in the file, and no free name of the block
    (its identifiers, less keywords and the names its own patterns bind)
    may be bound by val, fun, and, exception, datatype (constructors
    included) or structure anywhere else in the file, or be named, with
    `=`, by an infix, infixr or nonfix declaration.  A local
    structure's bindings are seen through its own `val` heads; only what
    an `open` brings in from outside the file is not seen here, also
    through an alias (`structure T = Term open T`); nor is what a
    pattern in `fn`, `case` or `handle` binds, which can rebind
    is_var_perm only for code in its scope; nor are the block's
    callers.  Those are left deliberately to the REVIEWED_31 blob seal
    (any byte change fails the audit until re-reviewed) and to the
    cond-rewr-ext selftest (both engines must accept and refuse the
    same permutative rewrites).  The compared
    tokens and the shadowing analysis are taken from the one filtered
    text, at the same offsets."""
    kept, code = lex(quote_filter(source))
    require(not re.search(r'\b(?:functor|abstype)\b', code),
            'functor or abstype outside a comment or string')
    start, end = block_span(code)
    block = code[start:end]
    heads = binder_heads(code)
    for name in ('vperm', 'is_var_perm'):
        require(sum(name in names for _, names in heads) == 1,
                name + ' is not bound exactly once')
    patterns = re.findall(r'\b(?:fun|of)\b(.*?)=|\|(.*?)=>', block, re.S)
    bound = {w for pair in patterns for part in pair
             for w in WORD.findall(part) if w[0].islower()}
    free = {w.split('.')[0] for w in WORD.findall(block)} \
        - SML_KEYWORDS - bound
    for pos, names in heads:
        if not start <= pos < end:
            clash = free & set(names)
            require(not clash,
                    'block name rebound: ' + ', '.join(sorted(clash)))
    clash = (free | {'='}) & fixity_names(code)
    require(not clash, 'block name given fixity: ' +
            ', '.join(sorted(clash)))
    return re.findall(r'\w+|\S', kept[start:end])


def check_var_perm_copy(sources):
    """Cond_rewrExt.is_var_perm must be develop's (unexported) block,
    token for token; only layout may differ."""
    develop = vperm_block(git_source(BASE, SRC + 'Cond_rewr.sml'))
    copy_ = vperm_block(sources[SRC + 'Cond_rewrExt.sml'])
    require(len(develop) > 40 and develop == copy_,
            'Cond_rewrExt.is_var_perm differs from develop Cond_rewr')


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
                stdin=subprocess.DEVNULL, check=True)
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
    # Source-discovered edge: rewrite tracking is one extent, owned by
    # Cond_rewr; Cond_rewrExt reports through Cond_rewr.note_rewrite.
    require('SimpTracking' not in graph and
            'SimpTracking' not in observations[SRC + 'Cond_rewr.sml'] and
            'SimpTracking' not in observations[SRC + 'Cond_rewrExt.sml'] and
            'ThreadLocal' in observations[SRC + 'Cond_rewr.sml'] and
            'Cond_rewr' in observations[SRC + 'Cond_rewrExt.sml'],
            'fresh dependency graph lost the shared tracking path')
    return graph


# Explanatory anchors, not a parser-based proof. The whole-file seals enforce
# everything around them (including private scopes, shadow declarations and
# registry miss branches). Counts are deliberately explicit for shared users.
IDENTITIES = {
    'tracking_slot': (
        (SRC + 'Cond_rewr.sml', b'ThreadLocal.new ()', 1),
        (SRC + 'Cond_rewr.sig', b'val note_rewrite : thm -> unit', 1),
        (SRC + 'Cond_rewrExt.sml', b'Cond_rewr.note_rewrite th', 2),
        (SRC + 'simpLib.sml', b'val track = with_tracking', 1),
        (SRC + 'simpExtLib.sml', b'val track = Cond_rewr.with_tracking', 1)),
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
    manifest = read_manifest()
    paths = source_paths(manifest)
    if sources is None:
        sources = read_sources()
    require(paths == sources.keys(), 'missing/unexpected live audited sources')
    require(all(isinstance(data, bytes) for data in sources.values()),
            'live source audit requires bytes')
    references = reference_sources(sources)
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
    check_var_perm_copy(sources)
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
        reviewed_31={p: dict(blob=v['blob'], reason=v['reason'])
                     for p, v in sorted(REVIEWED_31.items())},
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
