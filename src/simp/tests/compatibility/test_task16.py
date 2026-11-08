"""TASK_16 fail-closed in-memory mutations; no production/evidence writes."""
import copy
import json
import unittest
from unittest.mock import patch

import audit_task16 as audit


class StructuralAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Preserve the original whole-closure mutation tests on their sealed
        # landing, not on later intentionally changed extension sources.
        # The key set comes from the sealed manifest, not from live files:
        # TASK31 deleted SimpTracking, which that manifest still lists.
        cls.sources = {p: audit.git_source('ba366bcae', p)
                       for p in audit.source_paths(audit.read_manifest())}
        cls.manifest = audit.read_manifest()
        audit.audit(cls.sources)

    def reject(self, path, old, new, diagnostic):
        self.assertNotEqual(old, new)
        source = self.sources[path]
        old, new = old.encode(), new.encode()
        self.assertEqual(source.count(old), 1, old)
        changed = dict(self.sources)
        changed[path] = source.replace(old, new, 1)
        with self.assertRaisesRegex(AssertionError, diagnostic):
            audit.audit(changed)

    def reject_ordinary(self, old, new, index=0):
        self.reject(audit.ORDINARY[index], old, new, 'pinned develop')

    def test_sealed_task16_whole_source_correspondence(self):
        result = audit.audit(self.sources)
        self.assertEqual(result['structural'], 'pass')
        self.assertEqual(result['transitive_modules'], 231)
        self.assertEqual(result['transitive_sources'], 446)
        for path in audit.ORDINARY:
            self.assertEqual(self.sources[path],
                             audit.git_source(audit.BASE, path))
        for path in audit.EXTENSIONS:
            self.assertEqual(self.sources[path],
                             audit.git_source(audit.START, path))

    def test_live_ordinary_sources_stay_pinned(self):
        for path in audit.ORDINARY:
            self.assertEqual((audit.ROOT / path).read_bytes(),
                             audit.git_source(audit.BASE, path))

    def test_starting_mixed_source_and_signature_are_not_restored(self):
        for path in audit.ORDINARY:
            with self.subTest(path=path):
                changed = dict(self.sources)
                changed[path] = audit.git_source(audit.START, path)
                self.assertNotEqual(changed[path], self.sources[path])
                with self.assertRaisesRegex(AssertionError, 'pinned develop'):
                    audit.audit(changed)

    def test_byte_exact_not_token_or_newline_equivalence(self):
        for path in (*audit.ORDINARY, *audit.EXTENSIONS):
            for suffix in (b'\n', b'(* comment *)\n'):
                with self.subTest(path=path, suffix=suffix):
                    changed = dict(self.sources)
                    changed[path] += suffix
                    with self.assertRaises(AssertionError):
                        audit.audit(changed)
            changed = dict(self.sources)
            changed[path] = changed[path].replace(b'\n', b'\r\n')
            with self.assertRaises(AssertionError):
                audit.audit(changed)

    def test_net_simpset_history_and_companions(self):
        for old, new in (
                ('type net_conv_info = {thypart : string option, '
                 'ci : conv_info}',
                 'type net_conv_info = {thypart : string option, '
                 'ci : conv_info, configured : conv_info}'),
                ('datatype history_item = ADDFRAG of ssfrag',
                 'datatype history_item = ADDFRAG of ssfrag * int'),
                ('datatype simpset =', 'val companions = ref []\n'
                 'datatype simpset ='),
                ('initial_net=empty,',
                 'initial_net=(source_token (); empty),'),
                ('fun ssupd_net f', 'val hidden = Symtab.empty\n'
                 'fun ssupd_net f'),
                ('List.mapPartial (fn ADDFRAG sf => SOME sf | _ => NONE)',
                 'List.mapPartial (fn ADDFRAG sf => '
                 'SOME (simpExtLib.promote sf) | _ => NONE)')):
            with self.subTest(old=old):
                self.reject_ordinary(old, new)

    def test_direct_conditional_compilation_and_control(self):
        for old, new in (
                ('appconv (COND_REWR_CONV (nm,th), tag)',
                 'appconv (#legacy (Cond_rewrExt.COND_REWR_CONVS (nm,th)), '
                 'tag)'),
                ('val th = SPEC_ALL thm', 'val th = thm'),
                ('if !r = 0 then failwith "exceeded rewrite bound"',
                 'if false then failwith "exceeded rewrite bound"'),
                ('Portable.dec r', '()')):
            with self.subTest(old=old):
                self.reject_ordinary(old, new)

    def test_installation_decode_ac_all_makers_conversions_collectors(self):
        for old, new in (
                ('if is_excluded ss f then ss else', 'if false then ss else'),
                ('(nmopt, dest_tagged_rewrite th)', '(nmopt, (th,UNBOUNDED))'),
                ('(ac_rewrites ac @ crewrs)', '(crewrs @ ac_rewrites ac)'),
                ("flatten (map (mk_named_rewrs mk_rewrs')",
                 "flatten (map (mk_named_rewrs mk_rewrs)"),
                ("convs @ List.mapPartial mk_rewr_convdata rewrs'",
                 "List.mapPartial mk_rewr_convdata rewrs' @ convs"),
                ('map (Traverse.addctxt (map #2 rewrs)) dprocs\' @ dprocs @',
                 'dprocs @ map (Traverse.addctxt (map #2 rewrs)) dprocs\' @'),
                ('travrules::mk_travrules relations congs::reltravs',
                 'travrules::TravrulesExt.mk_threaded_travrules relations '
                 'congs::reltravs')):
            with self.subTest(old=old):
                self.reject_ordinary(old, new)

    def test_rewriter_traversal_and_marker_routes(self):
        for old, new in (
                ('val new_rwts0 = flatten (map mk_rewrs cthms)',
                 'val new_rwts0 = flatten (map mk_rewrs (rev cthms))'),
                ('in REDUCER {name=SOME"rewriter_for_ss",',
                 'in TraverseExt.LIFTED (REDUCER '
                 '{name=SOME"rewriter_for_ss",'),
                ('rewriters=[rewriter_for_ss ss]',
                 'rewriters=[configured_rewriter_for_ss ss]'),
                ('fun SIMP_QCONV ss = TRAVERSE (traversedata_for_ss ss);',
                 'fun SIMP_QCONV ss = TraverseExt.TRAVERSE '
                 '(traversedata_for_ss ss);'),
                ('val Cong   = markerLib.Cong',
                 'val Cong   = simpMarkerLib.Cong'),
                ('local open markerLib',
                 'local open markerLib simpMarkerLib splitLib')):
            with self.subTest(old=old):
                self.reject_ordinary(old, new)

    def test_tactics_replay_exclusions_and_printing_also_exact(self):
        for old, new in (
                ('List.foldl foldthis empty_ss (List.rev h0)',
                 'List.foldl foldthis empty_ss h0'),
                ("build_from_history history' |> fupdlimit (fn _ => limit)\n"
                 "                                  |> setexcluded excluded'",
                 "build_from_history history'"),
                ('setexcluded excluded\' ss ++ f', 'ss ++ f'),
                ('fun process_tags ss thl =',
                 'fun process_tags ss thl =\n'
                 '  (simpMarkerLib.reject_extended thl; ss)\n'
                 'fun unused ss thl ='),
                ('"Rewrite rules"', '"Rewrite  rules"'),
                ('end (* struct *)', 'val registry = ref []\n'
                 'end (* struct *)')):
            with self.subTest(old=old):
                self.reject_ordinary(old, new)

    def test_signature_cannot_hide_or_reintroduce_extension_apis(self):
        for old, new in (
                ('  type ssfrag', '  type ssfrag = simpExtLib.ssfrag'),
                ('  type simpset', '  type simpset = simpExtLib.simpset'),
                ('  type simpset', '  type rewrite_source\n  type simpset'),
                ('  val empty_ssfrag : ssfrag',
                 '  val looper_ss : string * (simpset -> tactic) -> ssfrag\n'
                 '  val empty_ssfrag : ssfrag'),
                ('dprocs: Traverse.reducer list',
                 'dprocs: TraverseExt.reducer list'),
                ('  val force_add       : simpset -> ssfrag -> simpset', '')):
            with self.subTest(old=old, new=new):
                self.reject_ordinary(old, new, index=1)

    def test_extension_actual_controls_prepared_shapes_and_inventory(self):
        path = audit.SRC + 'simpExtLib.sml'
        for old, new in (
                ('prepared = SOME prepared, bound = bound',
                 'prepared = NONE, bound = bound'),
                ('#rewrite_sources data, map supplied thl',
                 '[], map supplied thl'),
                ("type 'a source_slot = {item : 'a, token : int}",
                 "type 'a source_slot = {item : 'a}"),
                ('fun source_slot item = {item=item, token=source_token ()}',
                 'fun source_slot item = {item=item, token=0}')):
            with self.subTest(old=old):
                self.reject(path, old, new, 'extension compiler')
        self.reject(audit.SRC + 'simpExtLib.sig', '  type ssfrag',
                    '  type ssfrag = simpLib.ssfrag', 'extension compiler')

    def test_all_transitive_source_inputs_pinned(self):
        dependencies = audit.validate_manifest(self.manifest)
        for path in sorted(dependencies - set(audit.ORDINARY)):
            with self.subTest(path=path):
                changed = dict(self.sources)
                changed[path] += b'\n(* unreviewed shared change *)\n'
                with self.assertRaisesRegex(AssertionError, 'transitive'):
                    audit.audit(changed)

    def test_indirect_extension_edges_strings_and_slots_rejected(self):
        for path in (audit.SRC + 'Cond_rewr.sml',
                     audit.SRC + 'SimpTracking.sml',
                     'src/portableML/poly/concurrent/ThreadLocal.sml',
                     'src/1/TypeBase.sml', 'src/marker/markerLib.sml'):
            for extra in (b'open TraverseExt\n',
                          b'val _ = load "simpMarkerTheory"\n',
                          b'val _ = splitPersistLib.init ()\n',
                          b'val slot = Context.Data.new hidden\n'):
                with self.subTest(path=path, extra=extra):
                    self.assertIn(path, self.sources)
                    changed = dict(self.sources)
                    changed[path] += extra
                    with self.assertRaisesRegex(AssertionError, 'transitive'):
                        audit.audit(changed)

    def test_missing_sources_and_wrong_input_type_fail_closed(self):
        for path in self.sources:
            with self.subTest(path=path):
                changed = dict(self.sources)
                del changed[path]
                with self.assertRaisesRegex(AssertionError, 'missing'):
                    audit.audit(changed)
        changed = dict(self.sources)
        changed[audit.ORDINARY[0]] = changed[audit.ORDINARY[0]].decode()
        with self.assertRaisesRegex(AssertionError, 'requires bytes'):
            audit.audit(changed)

    def test_manifest_edges_are_real_transitive_not_direct_only(self):
        for resource in ('TraverseExt', 'Cond_rewrExt', 'simpMarkerTheory',
                         'simpMarkerLib', 'SplitData', 'splitLib',
                         'splitPersistLib'):
            with self.subTest(resource=resource):
                graph = copy.deepcopy(self.manifest)
                graph['modules'][resource] = dict(sources=['hidden.sml'],
                                                 imports=[],
                                                 basis_or_local_names=[])
                graph['modules']['ThreadLocal']['imports'].append(resource)
                with self.assertRaisesRegex(AssertionError,
                                            'extension resource'):
                    audit.validate_manifest(graph)
        graph = copy.deepcopy(self.manifest)
        del graph['modules']['ThreadLocal']
        with self.assertRaisesRegex(AssertionError, 'missing transitive'):
            audit.validate_manifest(graph)

    def test_manifest_omission_or_rewrite_cannot_pass_its_seal(self):
        changed = copy.deepcopy(self.manifest)
        changed['modules']['simpLib']['imports'] = []
        data = json.dumps(changed).encode()
        with patch.object(audit.Path, 'read_bytes', return_value=data):
            with self.assertRaisesRegex(AssertionError, 'manifest changed'):
                audit.audit(self.sources)


if __name__ == '__main__':
    unittest.main()
