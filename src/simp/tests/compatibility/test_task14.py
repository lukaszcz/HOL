"""Fail-closed controls for the bounded TASK_14 structural gate."""
import unittest
from audit_task14 import audit, sources


class TrackedCompilerAudit(unittest.TestCase):
    def test_current(self):
        self.assertTrue(audit(*sources()))

    def test_mutations(self):
        simp, cond, sig = sources()
        mutations = [
            (0, 'fun traversedata_for_ss ss = default_traversedata_for_ss ss',
             'fun traversedata_for_ss ss = source_token ()'),
            (0, 'fun rewrite_sources (SS data) thl =',
             'fun rewrite_sources (SS data) thl =\n'
             '  process_asm_tags (SS data) thl;'),
            (0, '#rewrite_sources data, map supplied thl',
             '#rewrite_sources data, map dest_tagged_rewrite thl'),
            (0, 'legacy_rewriter_for_ss_prepared ss []',
             'legacy_rewriter_for_ss_prepared ss (ssfrags_of ss)'),
            (0, 'prepared = SOME prepared, bound = bound',
             'prepared = NONE, bound = bound'),
            (0, 'val data = rebind_convdata data (current,declared)',
             'val data = mk_rewr_convdata (current,declared)'),
            (0, 'same_rewrite_source (previous,source)', 'true'),
            (0, 'process_tags0 {report=true,preserve=true} ss thl',
             'process_tags0 {report=true,preserve=false} ss thl'),
            (0, 'remove_ssfrags_with_controls preserve exclfrags ss',
             'remove_ssfrags exclfrags ss'),
            (0, 'fun rebind_convdata',
             'val hidden = simpLib.ssfrags_of\nfun rebind_convdata'),
            (0, 'Portable.finally restore run tm', 'run tm'),
            (1, 'if bounded = is_bounded control then', 'if true then'),
            (1, 'fun rebind (Prepared {shape,bounded,...}) control =',
             'fun rebind (Prepared {shape,bounded,...}) control =\n'
             'COND_REWR_CONVS ("again",TRUTH) true;'),
            (1, 'else #configured shape ctxt tm before Portable.dec r',
             'else #configured shape ctxt tm'),
            (2, '  type simpset',
             '  val promote : simpLib.simpset -> simpset\n  type simpset'),
        ]
        for index, old, new in mutations:
            with self.subTest(old=old):
                inputs = [simp, cond, sig]
                self.assertEqual(inputs[index].count(old), 1)
                inputs[index] = inputs[index].replace(old, new)
                with self.assertRaises(AssertionError):
                    audit(*inputs)


if __name__ == '__main__':
    unittest.main()
