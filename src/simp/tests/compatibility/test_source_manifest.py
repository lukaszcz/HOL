"""The reviewed source manifest that audit_task27 builds on."""
import copy
import json
import unittest
from unittest.mock import patch

import source_manifest as sm


class Manifest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = sm.read_manifest()

    def test_the_sealed_manifest_is_closed_and_ordinary(self):
        sources = sm.validate_manifest(self.manifest)
        self.assertEqual(len(self.manifest['modules']), 231)
        self.assertEqual(len(sources), 446)

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
                    sm.validate_manifest(graph)
        graph = copy.deepcopy(self.manifest)
        del graph['modules']['ThreadLocal']
        with self.assertRaisesRegex(AssertionError, 'missing transitive'):
            sm.validate_manifest(graph)

    def test_manifest_omission_or_rewrite_cannot_pass_its_seal(self):
        changed = copy.deepcopy(self.manifest)
        changed['modules']['simpLib']['imports'] = []
        data = json.dumps(changed).encode()
        with patch.object(sm.Path, 'read_bytes', return_value=data):
            with self.assertRaisesRegex(AssertionError, 'manifest changed'):
                sm.read_manifest()


if __name__ == '__main__':
    unittest.main()
