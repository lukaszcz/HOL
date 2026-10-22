#!/usr/bin/env python3
"""Offline TASK17 receipt/source audit. Never builds, benchmarks or rewrites."""
import argparse
import gzip
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from record_evidence import fingerprint, REPO, HERE
import run_behavior


def load(path):
    return json.loads(gzip.decompress(path.read_bytes())
                      if path.suffix == '.gz' else path.read_bytes())


def audit(root):
    report = load(root / 'validation.json')
    assert report['success'] is True
    for name, seal in report['sources'].items():
        assert fingerprint(REPO / name) == seal, 'stale source: ' + name
    for name, seal in report['artifacts'].items():
        assert fingerprint(root / name) == seal, 'stale artifact: ' + name
    for cmd in report['commands']:
        assert cmd['exit'] == 0 and (root / cmd['receipt']).is_file()
    for group, count in (('paired', 44), ('native', 14), ('behavior', 2)):
        manifest = load(root / group / 'manifest.json.gz')
        assert manifest['success'] is True
        assert len(manifest['runs']) == count
    results = []
    for side in ('baseline', 'candidate'):
        r = load(root / 'behavior' / (side + '-routes.json.gz'))
        assert r['exit'] == 0 and not r['timed_out'] and r['accepted']
        assert r['result']['expected_test_count'] == 42
        observations = r['result']['observations']
        assert observations == run_behavior.schema()
        results.append(observations)
    run_behavior.same_behavior(*results)
    print('TASK17 source seals, 44/14 prior receipts and 42 paired checks: OK')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--evidence', type=Path, default=HERE / 'evidence/task17')
    args = p.parse_args()
    audit(args.evidence.resolve())


if __name__ == '__main__':
    main()
