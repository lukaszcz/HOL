import copy
import unittest

from audit_core_evidence import graph_gate, metric
from schema import SIZES


class EvidenceTests(unittest.TestCase):
    def test_zero_and_improved_slopes(self):
        row = dict(candidate_minus_baseline_words=[0, 0, -9, -99, -999, -9999])
        graph_gate({'compiled': row}, False)
        with self.assertRaisesRegex(ValueError, 'increase'):
            graph_gate({'compiled': row}, True)
        graph_gate({'compiled': dict(candidate_minus_baseline_words=
                                    [0] * len(SIZES))}, True)

    def test_lower_intercept_cannot_hide_worse_slope(self):
        row = dict(candidate_minus_baseline_words=[-10, -9, -8, -7, -6, -5])
        with self.assertRaisesRegex(ValueError, 'slope increase'):
            graph_gate({'compiled': row}, False)

    def test_missing_size_and_point_increase(self):
        row = dict(candidate_minus_baseline_words=[0] * len(SIZES))
        for delta in ([0], [0, 0, 0, 0, 0, 1]):
            changed = copy.deepcopy(row)
            changed['candidate_minus_baseline_words'] = delta
            with self.assertRaises(ValueError):
                graph_gate({'compiled': changed}, False)

    def test_uncertainty_is_not_parity(self):
        rows = [dict(baseline=1, candidate=r)
                for r in [.9, 1.1] * 5]
        self.assertEqual('inconclusive', metric(rows)['numerical_decision'])
        self.assertEqual('slower', metric([dict(baseline=1, candidate=1.01)]
                                          * 10)['numerical_decision'])
        self.assertEqual('undefined', metric([dict(baseline=0, candidate=1)]
                                             * 10)['numerical_decision'])


if __name__ == '__main__':
    unittest.main()
