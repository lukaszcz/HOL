"""Live TASK27 gate and fail-closed mutations; no builds/production writes.

Run: PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
    -s src/simp/tests/compatibility -p test_task27.py
"""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import audit_task27 as audit


class RuntimeReceiptControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = audit.ROOT / 'src/simp/tests/api-audit/run.py'
        spec = importlib.util.spec_from_file_location('api_audit_run', path)
        cls.runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.runner)
        cls.text = ''.join('OBS used.path=' + str(
            audit.ROOT / 'src/simp/src' / (name + suffix)) + '\n'
            for name in ('simpLib', 'congLib', 'Traverse', 'Cond_rewr',
                         'Trace', 'simpExtLib', 'TraverseExt',
                         'Cond_rewrExt', 'congExtLib')
            for suffix in ('.sig', '.sml')) + ' ... OK\n' * 178 + (
                'OBS result=pass\n')

    def test_complete_receipt(self):
        self.assertEqual(self.runner.validate_output(
            self.text, 0, 'attribute', 'before'), 178)

    def test_incomplete_failed_and_wrong_count(self):
        for text, exitcode in ((self.text, 1), (self.text[:-1], 0),
                (self.text.replace('OBS result=pass', 'OBS incomplete'), 0),
                (self.text + 'OBS result=pass\n', 0),
                (self.text.replace(' ... OK\n', '', 1), 0),
                (self.text + 'FAILED!\n', 0)):
            with self.subTest(text=text[-50:], exitcode=exitcode):
                with self.assertRaisesRegex(ValueError, 'incomplete'):
                    self.runner.validate_output(
                        text, exitcode, 'attribute', 'before')

    def test_missing_actual_path_or_foreign_source(self):
        for text in (self.text.replace('OBS used.path=', 'OBS requested.path='),
                     self.text + 'OBS used.path=/foreign/Trace.sml\n'):
            with self.assertRaisesRegex(ValueError, 'native input'):
                self.runner.validate_output(text, 0, 'attribute', 'before')

    def test_missing_observed_file_is_not_a_null_seal(self):
        with self.assertRaisesRegex(ValueError, 'missing observed'):
            self.runner.resolve_observed('/does-not-exist/Trace.sml')


class LiveSourceGate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = audit.read_sources()
        cls.manifest = audit.read_manifest()
        # Deliberately exercise the default LIVE entry, not a historical map.
        cls.result = audit.audit()
        cls.observations = cls.result['defining_source_dependencies']

    def reject(self, path, extra=None, old=None, new=None, message='bytes'):
        changed = dict(self.sources)
        if extra is not None:
            changed[path] += b'\n' + extra + b'\n'
        else:
            self.assertEqual(changed[path].count(old), 1, old)
            self.assertNotEqual(old, new)
            changed[path] = changed[path].replace(old, new, 1)
        with self.assertRaisesRegex(AssertionError, message):
            audit.audit(changed)

    def test_live_graph_and_recorded_hashes(self):
        result = self.result
        self.assertEqual(result['structural'], 'pass')
        self.assertEqual(result['transitive_modules'], 230)
        self.assertEqual(result['transitive_sources'], 444)
        self.assertEqual(len(result['sources']), 476)
        self.assertEqual(result['head'], subprocess.check_output(
            ['git', '-C', str(audit.ROOT), 'rev-parse', 'HEAD'],
            text=True).strip())
        self.assertEqual(result['ordinary_source_deltas'], {})
        self.assertEqual(result['source_manifest'],
                         audit.prior.MANIFEST_SHA256)
        self.assertEqual(result['analyzer']['live_observations_sha256'],
                         audit.ANALYSIS_SHA256)
        self.assertEqual(result['analyzer']['reference_observations_sha256'],
                         audit.ANALYSIS_SHA256)
        for path, data in self.sources.items():
            with self.subTest(path=path):
                self.assertEqual(result['sources'][path]['actual'],
                                 audit.seal(data))
                self.assertEqual(result['sources'][path]['reviewed_reference'],
                                 audit.seal(data))
                baseline = audit.baseline_source(path)
                self.assertEqual(result['sources'][path]['baseline'],
                                 None if baseline is None else
                                 audit.seal(baseline))
        # Report is JSON, not an in-memory-only unexportable graph receipt.
        self.assertEqual(json.loads(json.dumps(result)), result)

    def test_exact_baseline_ordinary_and_narrow_shared_deltas(self):
        paths = audit.validate_manifest(self.manifest)
        for path in sorted(paths | set(audit.ORDINARY_SENTINELS)):
            with self.subTest(path=path):
                revision = (audit.START if path in audit.SHARED_DELTAS else
                            audit.BASE)
                if path in audit.REVIEWED_31:
                    # Sealed by content: the recorded git blob id.
                    self.assertEqual(
                        audit.blob_id(self.sources[path]),
                        audit.REVIEWED_31[path]['blob'])
                    continue
                self.assertEqual(self.sources[path],
                                 audit.git_source(revision, path))
        self.assertEqual(set(self.result['shared_identity_deltas']),
                         set(audit.SHARED_DELTAS))
        self.assertEqual(len(audit.SHARED_DELTAS), 3)
        for path in audit.prior.ORDINARY:
            self.assertEqual(self.sources[path],
                             audit.git_source(audit.BASE, path))

    def test_extension_delta_inventory_is_exact_not_blanket_head(self):
        self.assertEqual(set(self.result['reviewed_extension_deltas']),
                         set(audit.DELTAS))
        actual_deltas = set()
        for path in audit.EXTENSIONS:
            self.assertEqual(self.sources[path], audit.reference_source(
                path, self.sources[path]))
            if audit.baseline_source(path) != self.sources[path]:
                actual_deltas.add(path)
        self.assertEqual(actual_deltas, set(audit.DELTAS))
        self.assertEqual(len(actual_deltas), 13)
        for path, delta in audit.delta_records().items():
            self.assertTrue(delta['reason'])
            self.assertNotEqual(delta['baseline'], delta['reviewed'])
            if delta['baseline'] is not None:
                changed = dict(self.sources)
                changed[path] = audit.baseline_source(path)
                with self.subTest(path=path):
                    with self.assertRaisesRegex(AssertionError, 'bytes'):
                        audit.audit(changed)

    def test_actual_graph_keeps_tracking_out_of_the_ordinary_closure(self):
        graph = self.result['dependency_graph']
        self.assertNotIn('SimpTracking', graph)
        self.assertNotIn('SimpTracking',
                         graph['Cond_rewr']['defining_source_imports'])
        self.assertNotIn('SimpTracking',
                         self.observations[audit.SRC + 'Cond_rewrExt.sml'])
        self.assertIn('Cond_rewr',
                      self.observations[audit.SRC + 'Cond_rewrExt.sml'])
        self.assertIn('ThreadLocal',
                      self.observations[audit.SRC + 'Cond_rewr.sml'])
        for name, node in graph.items():
            self.assertEqual(node['reviewed_runtime_imports'],
                             self.manifest['modules'][name]['imports'])
            names = set().union(*(set(self.observations[p])
                                  for p in node['sources']))
            self.assertEqual(node['defining_source_names'], sorted(names))
        self.assertIn('theory construction',
                      graph['boolTheory']['mapped_input_reason'])
        self.assertEqual(set(self.result['identities']),
                         set(audit.IDENTITIES))
        self.assertIn('shared_exceptions', self.result['identities'])

    def test_every_transitive_defining_input_is_byte_sealed(self):
        # Includes signatures, scripts, templates, platform/heap bootstrap and
        # shared services. A new indirect dependency anywhere fails closed.
        for path in sorted(self.sources):
            with self.subTest(path=path):
                self.reject(path, extra=b'(* unreviewed change *)')

    def test_raw_bytes_not_comment_token_or_newline_equivalence(self):
        for path in (audit.SRC + 'simpLib.sml',
                     audit.SRC + 'Cond_rewr.sml',
                     audit.SRC + 'Cond_rewr.sig',
                     audit.SRC + 'simpExtLib.sig'):
            with self.subTest(path=path):
                changed = dict(self.sources)
                changed[path] = changed[path].replace(b'\n', b'\r\n')
                self.assertNotEqual(changed[path], self.sources[path])
                with self.assertRaisesRegex(AssertionError, 'bytes'):
                    audit.audit(changed)

    def test_task31_files_are_sealed_by_content_not_by_commit(self):
        self.assertEqual(audit.blob_id(b'hello\n'),
                         'ce013625030ba8dba906f756967f9e9ca394464a')
        self.assertEqual(set(audit.REVIEWED_31), {
            audit.SRC + n for n in ('Cond_rewr.sig', 'Cond_rewrExt.sml',
                                    'simpExtLib.sml', 'simpExtLib.sig')})
        for path, record in audit.REVIEWED_31.items():
            with self.subTest(path=path):
                self.assertTrue(record['reason'])
                self.assertEqual(audit.blob_id(self.sources[path]),
                                 record['blob'])
                self.assertEqual(audit.reference_revision(path),
                                 'blob:' + record['blob'])
                self.reject(path, extra=b'(* drift *)',
                            message='extension/control')

    def test_var_perm_copy_must_match_develop_token_for_token(self):
        path = audit.SRC + 'Cond_rewrExt.sml'
        audit.check_var_perm_copy(self.sources)
        source = self.sources[path]
        relaid = source.replace(b'  case (dest_term tm1',
                                b'      case (dest_term tm1')
        audit.check_var_perm_copy({**self.sources, path: relaid})
        for old, new in ((b'snd v1 = snd v2', b'true'),
                         (b'vperm(fst t1,fst t2) andalso',
                          b'vperm(fst t1,fst t2) orelse'),
                         (b'HOLset.equal(', b'HOLset.isSubset('),
                         (b'FVL [tm2] empty_tmset)',
                          b'FVL [tm1] empty_tmset)')):
            with self.subTest(old=old):
                self.assertEqual(source.count(old), 1)
                with self.assertRaisesRegex(AssertionError,
                                            'differs from develop'):
                    audit.check_var_perm_copy(
                        {**self.sources, path: source.replace(old, new)})
        for old, new in ((b'FVL [tm2] empty_tmset)\n',
                         b'FVL [tm2] empty_tmset) andalso false\n'),
                         (b'FVL [tm2] empty_tmset)\n',
                          b'FVL [tm2] empty_tmset) (* x *) andalso false\n'),
                         (b'FVL [tm2] empty_tmset)\n',
                          b'FVL [tm2] empty_tmset) (* (* x *) *) andalso '
                          b'false\n'),
                         (b'FVL [tm2] empty_tmset)\n',
                          b'FVL [tm2] empty_tmset))\n')):
            with self.subTest(tail=new):
                self.assertEqual(source.count(old), 1)
                # the filter itself refuses the unbalanced parenthesis
                with self.assertRaisesRegex(
                        AssertionError, 'differs from develop|filter failed'):
                    audit.check_var_perm_copy(
                        {**self.sources, path: source.replace(old, new)})

    def test_lexer_strips_comments_and_reads_literals_exactly(self):
        lex = audit.strip_comments
        for text, want in (
                ('a (* x (* y *) z *) b', 'a   b'),
                ('a "q\\"(*" b (* c *) d', 'a "q\\"(*" b   d'),
                ('a "q\\\\" (* c *) d', 'a "q\\\\"   d'),
                ('a "x\\  \\y(*" (* c *) d', 'a "x\\  \\y(*"   d'),
                ('a "x\\ \\" (* c *) d "(*" e',
                 'a "x\\ \\"   d "(*" e'),
                ('a "x\\ \\\\\\" (* c *) d', 'a "x\\ \\\\\\"   d'),
                ('a (*) b *) c', 'a   c'),
                ('a #"(" (* c *) d #"\\"" e', 'a #"("   d #"\\"" e'),
                ('a (* "q *) b', 'a   b')):
            with self.subTest(text=text):
                self.assertEqual(lex(text), want)
        for text, message in (('a (* b (* c *) d', 'unterminated comment'),
                              ('a (* b', 'unterminated comment'),
                              ('a "b (* c *)', 'unterminated string'),
                              ('a "b\\ c', 'string gap'),
                              ('a "b\\ ', 'string gap'),
                              ('a \u2018x\u2019', 'quotation'),
                              ('a \u201cx\u201d', 'quotation'),
                              ('a `x`', 'quotation')):
            with self.subTest(text=text):
                with self.assertRaisesRegex(AssertionError, message):
                    lex(text)
        self.assertEqual(lex('a (* `x` \u2018 *) b'), 'a   b')

    def test_var_perm_copy_accepts_what_the_compiler_reads_the_same(self):
        path = audit.SRC + 'Cond_rewrExt.sml'
        source = self.sources[path]
        for old, new in (
                (b'andalso vperm(snd t1,snd t2)',
                 b'andalso (* a (* nested *) b *) vperm(snd t1,snd t2)'),
                (b'vperm(snd t1, snd t2)',
                 b'vperm(snd t1, (* "unmatched *) snd t2)'),
                (b'fun vperm', b'val _ = "(*"\nval _ = "x\\ \\"\n'
                 b'val _ = "(*"\nfun vperm'),
                # a quotation is a string once filtered
                (b'fun vperm',
                 'val q = \u2018"a" b\u2019\nfun vperm'.encode()),
                (b'fun vperm', b'Quote q = Lib.I:\n  "a" b\nEnd\nfun vperm'),
                # a string that holds the block's opening text
                (b'fun vperm', b'val _ = "fun vperm"\nval _ = '
                 b'"fun is_var_perm"\nfun vperm')):
            with self.subTest(new=new):
                self.assertEqual(source.count(old), 1)
                audit.check_var_perm_copy(
                    {**self.sources, path: source.replace(old, new)})

    def test_var_perm_copy_fails_closed(self):
        path = audit.SRC + 'Cond_rewrExt.sml'
        source = self.sources[path]
        tail = b'FVL [tm2] empty_tmset)\n'
        gap = (b'val _ = "\\ \\"\nval _ = "(*"\n'
               b'fun vperm(tm1,tm2) = true\n'
               b'fun is_var_perm(tm1,tm2) = true\nval _ = "*)"\n'
               b'(*\n' + source[source.index(b'fun vperm'):
                                 source.index(b'type config')] +
               b'val _ = " *)\n')
        for old, new, message in (
                (b'fun vperm', gap + b'fun vperm', 'not bound exactly'),
                (tail, tail + b'(* andalso false\n', 'unclosed comment'),
                (tail, tail + b'"x\n', 'unclosed string'),
                (b'type config',
                 b'fun is_var_perm _ = false\ntype config',
                 'not bound exactly'),
                (b'fun vperm',
                 b'fun aconv _ _ = true\nfun vperm', 'rebound: aconv'),
                (b'fun vperm',
                 b'val (a, FVL) = (1, 2)\nfun vperm', 'rebound: FVL'),
                (b'fun vperm',
                 b'datatype t = VAR | Q\nfun vperm', 'rebound: VAR'),
                (b'fun vperm',
                 b'exception empty_tmset\nfun vperm', 'rebound: empty')):
            with self.subTest(new=new[:40]):
                self.assertEqual(source.count(old), 1)
                with self.assertRaisesRegex(AssertionError, message):
                    audit.check_var_perm_copy(
                        {**self.sources, path: source.replace(old, new)})

    def exploit(self, name, quote):
        """A modified Cond_rewrExt.sml that HOL's quotation filter turns
        into a program with a different is_var_perm, from the review of
        the var_perm check; `quote` is the pair of string brackets."""
        source = self.sources[audit.SRC + 'Cond_rewrExt.sml']
        first = source.index(b'fun vperm')
        last = source.index(b'type config')
        block = source[first:last]
        if name == 'E1':
            # `Quote x = f:` is a val binding of x, with no quote character
            return source[:first] + (
                b'fun always _ = fn (_ : term) => fn (_ : term) => true\n'
                b'Quote aconv = always:\n  x\nEnd\n') + source[first:]
        if name == 'E2':
            # a decoy that the filter makes a string, but an unfiltered
            # scanner reads as code that opens a comment
            opener, closer = (b.encode() for b in quote)
            modified = block.replace(b'snd v1 = snd v2', b'true')
            self.assertNotEqual(modified, block)
            return (source[:first] + b'Quote ignore:\n' + block +
                    b'val _ = ' + opener + b'(*' + closer + b'\nEnd\n' +
                    modified + b'Quote ignore:\n' + opener + b'*)' +
                    closer + b'\nEnd\n' + source[last:])
        if name == 'functor':
            # the parameter rebinds HOLset; the structure applies it
            old = b'structure Cond_rewrExt :> Cond_rewrExt ='
            self.assertEqual(source.count(old), 1)
            return source.replace(
                old, b"functor CondRewrExtF (HOLset : sig val equal : "
                b"'a * 'a -> bool end) =") + (
                b'\nstructure Cond_rewrExt :> Cond_rewrExt = CondRewrExtF '
                b'(struct fun equal _ = true end)\n')
        raise ValueError(name)

    def test_var_perm_copy_reads_what_the_quotation_filter_writes(self):
        path = audit.SRC + 'Cond_rewrExt.sml'
        self.assertTrue(audit.UNQUOTE.is_file(), 'build HOL: no bin/unquote')
        for name, quote, message in (
                ('E1', None, 'rebound: aconv'),
                ('E2', ('\u00ab', '\u00bb'), 'differs from develop'),
                ('E2', ('\u2039', '\u203a'), 'differs from develop'),
                ('functor', None, 'functor or abstype')):
            with self.subTest(name=name, quote=quote):
                changed = self.exploit(name, quote)
                with self.assertRaisesRegex(AssertionError, message):
                    audit.check_var_perm_copy(
                        {**self.sources, path: changed})

    def test_var_perm_copy_refuses_abstype_fixity_and_other_binders(self):
        path = audit.SRC + 'Cond_rewrExt.sml'
        source = self.sources[path]
        for old, new, message in (
                (b'fun vperm', b'abstype u = U with end\nfun vperm',
                 'functor or abstype'),
                (b'fun vperm', b'nonfix aconv\nfun vperm', 'fixity: aconv'),
                (b'fun vperm', b'infix FVL\nfun vperm', 'fixity: FVL'),
                (b'fun vperm', b'infix 3 snd\nfun vperm', 'fixity: snd'),
                (b'fun vperm', b'infixr 0 =\nfun vperm', 'fixity: ='),
                (b'fun vperm',
                 b'structure HOLset = struct open HOLset '
                 b'fun equal _ = true end\nfun vperm', 'rebound: HOLset'),
                (b'fun vperm', b'val x = 1 and aconv = 2\nfun vperm',
                 'rebound: aconv'),
                (b'fun vperm',
                 b'val {a = aconv} = {a = fn _ => fn _ => true}\n'
                 b'fun vperm', 'rebound: aconv'),
                (b'fun vperm',
                 b'val {1 = aconv, 2 = _} = (fn _ => fn _ => true, 0)\n'
                 b'fun vperm', 'rebound: aconv'),
                (b'fun vperm',
                 b'val (_, [{a = snd}]) = (0, [{a = 1}])\nfun vperm',
                 'rebound: snd'),
                (b'type config',
                 b'val {a = is_var_perm} = {a = fn _ => true}\ntype config',
                 'not bound exactly')):
            with self.subTest(new=new[:40]):
                self.assertEqual(source.count(old), 1)
                with self.assertRaisesRegex(AssertionError, message):
                    audit.check_var_perm_copy(
                        {**self.sources, path: source.replace(old, new)})
        # a fixity declaration of a name the block does not use is fine
        audit.check_var_perm_copy({**self.sources, path: source.replace(
            b'fun vperm', b'infix 3 unrelated\nfun vperm')})
        # the filter itself is a parser: it refuses what it cannot read
        for decl in (b'infix aconv', b'nonfix ='):
            with self.assertRaisesRegex(AssertionError, 'filter failed'):
                audit.check_var_perm_copy({**self.sources, path:
                    source.replace(b'fun vperm', decl + b'\nfun vperm')})

    def test_var_perm_copy_fails_closed_without_the_filter(self):
        for tool, message in (
                (audit.ROOT / 'no/such/unquote', 'filter missing'),
                (Path('/bin/false'), 'filter failed'),
                (Path('/bin/true'), 'wrote no output')):
            with self.subTest(tool=str(tool)):
                with patch.object(audit, 'UNQUOTE', tool):
                    with self.assertRaisesRegex(AssertionError, message):
                        audit.check_var_perm_copy(self.sources)

    def test_var_perm_copy_fails_closed_on_filter_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            tool = Path(directory) / 'unquote'
            tool.write_text('#!/bin/sh\ncp "$1" "$2"\n'
                            'echo warning >&2\nexit 0\n')
            tool.chmod(0o755)
            with patch.object(audit, 'UNQUOTE', tool):
                with self.assertRaisesRegex(AssertionError, 'filter failed'):
                    audit.check_var_perm_copy(self.sources)

    def test_task31_overlay_is_applied_to_the_sealed_task16_manifest(self):
        sealed = audit.prior.read_manifest()
        self.assertIn('SimpTracking', sealed['modules'])
        self.assertNotIn('SimpTracking', self.manifest['modules'])
        self.assertEqual(self.manifest['modules']['Cond_rewr']['imports'],
                         sorted(set(sealed['modules']['Cond_rewr']['imports'])
                                - {'SimpTracking'} | {'ThreadLocal'}))
        for broken in ('node', 'edge'):
            changed = copy.deepcopy(sealed)
            if broken == 'node':
                changed['modules']['SimpTracking']['imports'].pop()
            else:
                changed['modules']['Cond_rewr']['imports'].append(
                    'ThreadLocal')
            with self.assertRaisesRegex(AssertionError, 'overlay base'):
                audit.overlay31(changed)

    def test_direct_and_aliased_extension_edges(self):
        for path in (audit.SRC + 'Cond_rewr.sml',
                     'src/1/TypeBase.sml', 'src/marker/markerLib.sml',
                     'src/basicProof/BasicProvers.sml'):
            for extra in (
                    b'open TraverseExt',
                    b'structure Hidden = simpExtLib\nopen Hidden',
                    b'structure Defaults = trackedSimpDefaults\n'
                    b'val hidden = Defaults.initial_recipe []',
                    b'structure Marker = simpMarkerLib',
                    b'structure Split = splitPersistLib'):
                with self.subTest(path=path, extra=extra):
                    self.reject(path, extra=extra)

    def test_computed_dynamic_load_edges_not_just_identifier_grep(self):
        for path in (audit.SRC + 'Cond_rewr.sml',
                     'tools-poly/poly/poly-init2.ML',
                     'src/basicProof/BasicProvers.sml'):
            for extra in (
                    b'val _ = load "simpMarkerTheory"',
                    b'val _ = Meta.load (String.concat '
                    b'["tracked", "SimpDefaults"])',
                    b'val _ = PolyML.use (OS.Path.concat '
                    b'("private", "extension.sml"))',
                    b'val loader = Meta.load\n'
                    b'val _ = loader (String.concat ["Traverse", "Ext"])'):
                with self.subTest(path=path, extra=extra):
                    self.reject(path, extra=extra)

    def test_dynamic_edge_that_analyzer_cannot_resolve_still_rejected(self):
        path = audit.SRC + 'Cond_rewr.sml'
        changed = self.sources[path] + (
            b'\nval _ = Meta.load (String.concat '
            b'["tracked", "SimpDefaults"])\n')
        names = audit.analyze_sources({path: changed})[path]
        self.assertNotIn('trackedSimpDefaults', names)
        self.assertIn('Meta', names)
        with self.assertRaisesRegex(AssertionError, 'ordinary transitive'):
            audit.audit({**self.sources, path: changed})

    def test_duplicate_tracker_and_control_copies(self):
        for path, extra in (
                (audit.SRC + 'Cond_rewr.sml',
                 b'val second = ThreadLocal.new ()'),
                (audit.SRC + 'Cond_rewrExt.sml',
                 b'val slot : thm list option ThreadLocal.t = '
                 b'ThreadLocal.new ()'),
                (audit.SRC + 'Cond_rewrExt.sml',
                 b'val stack_limit = ref (!Cond_rewr.stack_limit)'),
                (audit.SRC + 'TraverseExt.sml',
                 b'structure SimpTracking = struct '
                 b'fun note_rewrite _ = () end'),
                (audit.SRC + 'simpExtLib.sml',
                 b'val trace_level = ref (!Trace.trace_level)'),
                (audit.SRC + 'simpExtLib.sml',
                 b'val trace_hook = Listener.new_listener ()')):
            with self.subTest(path=path, extra=extra):
                self.reject(path, extra=extra)
        self.reject(audit.SRC + 'Cond_rewrExt.sml',
                    old=b'fun bind (shape : runners) control =\n'
                    b'  case control of',
                    new=b'fun bind (shape : runners) control =\n'
                    b'  case (case control of BoundedRewrites.BOUNDED r =>\n'
                    b'    BoundedRewrites.BOUNDED (ref (!r))\n'
                    b'  | other => other) of')

    def test_rewired_private_reporter_is_not_a_shared_tracker(self):
        path = audit.SRC + 'Cond_rewrExt.sml'
        changed = dict(self.sources)
        anchor = b'open HolKernel boolLib liteLib Trace'
        self.assertEqual(changed[path].count(anchor), 1)
        changed[path] = changed[path].replace(anchor, anchor + b'\n'
            b'structure Private = struct\n'
            b'  val slot : thm list option ThreadLocal.t =\n'
            b'    ThreadLocal.new ()\n'
            b'  fun note_rewrite th = case ThreadLocal.get slot of\n'
            b'      SOME (SOME xs) =>\n'
            b'        ThreadLocal.set (slot, SOME (th :: xs))\n'
            b'    | _ => ()\nend')
        self.assertEqual(changed[path].count(
            b'Cond_rewr.note_rewrite th'), 2)
        changed[path] = changed[path].replace(b'Cond_rewr.note_rewrite th',
                                              b'Private.note_rewrite th')
        with self.assertRaisesRegex(AssertionError, 'extension/control'):
            audit.audit(changed)

    def test_duplicate_exception_or_shared_type_rejected(self):
        for extra in (b'exception HOL_ERR of Feedback.hol_error',
                      b'exception UNCHANGED', b'exception Interrupt',
                      b'datatype control = UNBOUNDED | BOUNDED of int ref',
                      b'datatype action = TEXT of string'):
            with self.subTest(extra=extra):
                self.reject(audit.SRC + 'Cond_rewrExt.sml', extra=extra)
        self.reject(audit.SRC + 'TravrulesExt.sml',
                    old=b'type travrules = Travrules.travrules',
                    new=b'datatype travrules = COPY of Travrules.travrules')
        self.reject(audit.SRC + 'OpeningExt.sml',
                    old=b'type congproc = Opening.congproc',
                    new=b'datatype congproc = COPY of Opening.congproc')

    def test_registry_slot_collision_and_hidden_registry(self):
        self.reject(audit.SRC + 'simpExtLib.sml',
                    old=b'name = "simpExtLib.ssfragDB"',
                    new=b'name = "simpLib.ssfragDB"')
        for path in (audit.SRC + 'simpExtLib.sml',
                     'src/boss/trackedSimpDefaults.sml',
                     'src/1/ThmAttribute.sml'):
            with self.subTest(path=path):
                self.reject(path, extra=b'val shadow = Context.Data.new '
                            b'{name="simpLib.ssfragDB", empty=NONE, '
                            b'pp=fn _ => "hidden"}')

    def test_registry_miss_fallback_rejected(self):
        self.reject(audit.SRC + 'simpExtLib.sml',
                    old=b'fun lookup_named_frag n = '
                    b'Symtab.lookup (ssfragDB ()) n',
                    new=b'fun lookup_named_frag n =\n'
                    b'case Symtab.lookup (ssfragDB ()) n of\n'
                    b'  NONE => Option.map (fn _ => empty_ssfrag)\n'
                    b'    (simpLib.lookup_named_frag n)\n| found => found')
        self.reject('src/boss/trackedSimpDefaults.sml',
                    old=b'raise ERR origin\n'
                    b'        "Unprepared tracked default provider; '
                    b'explicitly build and install one"',
                    new=b'build (initial_recipe [])')
        self.reject('src/basicProof/BasicProvers.sml',
                    extra=b'structure Defaults = trackedSimpDefaults\n'
                    b'val fallback = Defaults.build '
                    b'(Defaults.initial_recipe [])')

    def test_missing_extra_and_nonbyte_source_fail_closed(self):
        for path in self.sources:
            with self.subTest(path=path):
                changed = dict(self.sources)
                del changed[path]
                with self.assertRaisesRegex(AssertionError, 'missing'):
                    audit.audit(changed)
        with self.assertRaisesRegex(AssertionError, 'unexpected'):
            audit.audit({**self.sources, 'hidden.sml': b'val slot = ref []'})
        with self.assertRaisesRegex(AssertionError, 'requires bytes'):
            audit.audit({**self.sources, audit.prior.ORDINARY[0]: 'not bytes'})

    def test_default_entry_reads_changed_live_files_not_git_fallback(self):
        # A disposable checkout-shaped tree, never an edit to caller sources.
        with tempfile.TemporaryDirectory(prefix='task27-live-test-') as d:
            root = Path(d)
            for path, data in self.sources.items():
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            path = audit.SRC + 'Cond_rewr.sml'
            (root / path).write_bytes(self.sources[path] +
                                      b'\nopen TraverseExt')
            with patch.object(audit, 'ROOT', root):
                with self.assertRaisesRegex(AssertionError,
                                            'ordinary transitive'):
                    audit.audit()

    def test_manifest_closure_forbidden_unresolved_and_missing_edges(self):
        for resource in ('TraverseExt', 'simpExtLib', 'simpMarkerTheory',
                         'splitLib', 'SplitData', 'splitPersistLib',
                         'trackedSimpDefaults'):
            for kind in ('imports', 'basis_or_local_names'):
                with self.subTest(resource=resource, kind=kind):
                    changed = copy.deepcopy(self.manifest)
                    changed['modules']['ThreadLocal'][kind].append(resource)
                    if kind == 'imports':
                        changed['modules'][resource] = dict(
                            sources=['hidden.sml'], imports=[],
                            basis_or_local_names=[])
                    with self.assertRaisesRegex(AssertionError, 'extension'):
                        audit.validate_manifest(changed)
        changed = copy.deepcopy(self.manifest)
        del changed['modules']['Trace']
        with self.assertRaisesRegex(AssertionError, 'missing transitive'):
            audit.validate_manifest(changed)
        # Tracking is one extent owned by Cond_rewr, which Cond_rewrExt
        # reaches through Cond_rewr.note_rewrite; no SimpTracking module.
        changed = copy.deepcopy(self.manifest)
        changed['modules']['Cond_rewr']['imports'].append('SimpTracking')
        changed['modules']['SimpTracking'] = dict(
            sources=['src/simp/src/SimpTracking.sml'], imports=[],
            basis_or_local_names=[])
        with self.assertRaisesRegex(AssertionError, 'extension'):
            audit.validate_manifest(changed)

    def test_manifest_omission_and_rewrite_cannot_pass_seal(self):
        changed = copy.deepcopy(self.manifest)
        changed['modules']['Cond_rewr']['imports'].remove('Trace')
        with patch.object(audit.prior.Path, 'read_bytes',
                          return_value=json.dumps(changed).encode()):
            with self.assertRaisesRegex(AssertionError, 'manifest changed'):
                audit.audit(self.sources)

    def test_fresh_analyzer_cannot_drop_or_invent_an_edge(self):
        for operation in ('drop', 'invent', 'omit_input'):
            changed = copy.deepcopy(self.observations)
            path = audit.SRC + 'Cond_rewr.sml'
            if operation == 'drop':
                changed[path].remove('Trace')
            elif operation == 'invent':
                changed[path].append('trackedSimpDefaults')
            else:
                del changed[path]
            with self.subTest(operation=operation):
                with self.assertRaisesRegex(AssertionError, 'dependenc'):
                    audit.check_analysis(self.manifest, changed,
                                         self.observations)
        empty = {p: [] for p in self.observations}
        with self.assertRaisesRegex(AssertionError, 'reviewed seal'):
            audit.check_analysis(self.manifest, empty, empty)

    def test_fresh_analysis_checks_manifest_not_just_reference_equality(self):
        changed = copy.deepcopy(self.manifest)
        # Trace remains reachable via other nodes, so graph reachability alone
        # cannot catch this omission of a direct defining-source dependency.
        changed['modules']['Cond_rewr']['imports'].remove('Trace')
        with self.assertRaisesRegex(AssertionError, 'manifest omits'):
            audit.check_analysis(changed, self.observations, self.observations)

    def test_analyzer_failure_no_skip_or_stale_cache_fallback(self):
        failure = subprocess.CalledProcessError(1, ['holdeptool'])
        with patch.object(audit.subprocess, 'run', side_effect=failure):
            with self.assertRaises(subprocess.CalledProcessError):
                audit.analyze_sources({audit.prior.ORDINARY[0]: b'bad input'})
        for stdout, stderr in ((b'Z\nA\n', b''), (b'', b'warning')):
            completed = subprocess.CompletedProcess([], 0, stdout, stderr)
            with patch.object(audit.subprocess, 'run', return_value=completed):
                with self.assertRaises(AssertionError):
                    audit.analyze_sources({audit.prior.ORDINARY[0]: b''})


if __name__ == '__main__':
    unittest.main()
