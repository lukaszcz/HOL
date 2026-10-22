"""Protocol controls independent of the SML fixture's success checks."""
import copy
import unittest
import run_behavior as runner


def text(rows):
    return ''.join('@@PAIR\t' + str(i) + '\t' + '\t'.join(row) + '\n'
                   for i, row in enumerate(rows))


class BehaviorTests(unittest.TestCase):
    def test_complete(self):
        rows = runner.schema()
        self.assertEqual(sum(r[0] == 'check' for r in rows), 307)
        self.assertEqual(runner.behavior(text(rows)), rows)

    def rejects(self, rows):
        with self.assertRaises(runner.paired.InvalidRun):
            runner.behavior(text(rows))

    def test_each_missing_observation(self):
        rows = runner.schema()
        for i in range(len(rows)):
            with self.subTest(i=i):
                self.rejects(rows[:i] + rows[i + 1:])

    def test_each_wrong_result(self):
        for i in range(len(runner.schema())):
            rows = copy.deepcopy(runner.schema())
            rows[i][2] = 'wrong'
            with self.subTest(i=i):
                self.rejects(rows)

    def test_extra_result(self):
        self.rejects(runner.schema() + [runner.schema()[-1]])

    def test_reversed_subgoal_check_order(self):
        rows = runner.schema()
        rows[29], rows[30] = rows[30], rows[29]
        self.rejects(rows)

    def test_stage_swapped(self):
        rows = runner.schema()
        i = next(i for i, r in enumerate(rows) if r[1] == 'stage ASM Req0 construct')
        rows[i], rows[i + 1] = rows[i + 1], rows[i]
        self.rejects(rows)

    def test_missing_real_validation(self):
        rows = runner.schema()
        rows[-2][2] = '115'
        self.rejects(rows)

    def test_noncontiguous_sequence(self):
        with self.assertRaises(runner.paired.InvalidRun):
            runner.behavior(text(runner.schema()).replace('@@PAIR\t1\t',
                                                         '@@PAIR\t2\t', 1))

    def test_ordinary_modules(self):
        runner.ordinary_only(['/private/simpLib.sml', '/shared/markerLib.sml'])

    def test_each_extension_module_rejected(self):
        for module in ('simpExtLib', 'TraverseExt', 'Cond_rewrExt', 'congLibExt',
                       'simpMarkerLib', 'simpMarkerTheory', 'SplitData', 'splitLib',
                       'splitPersistLib'):
            with self.subTest(module=module):
                with self.assertRaises(runner.paired.InvalidRun):
                    runner.ordinary_only(['/private/' + module + '.sml'])

    def test_cross_version_difference(self):
        with self.assertRaises(runner.paired.InvalidRun):
            runner.same_behavior(runner.schema(), runner.schema()[:-1])


if __name__ == '__main__':
    unittest.main()
