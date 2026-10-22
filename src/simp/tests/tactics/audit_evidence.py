#!/usr/bin/env python3
"""Offline source-tied TASK18 validation audit; no builds or measurements."""
import argparse
import gzip
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from record_evidence import HERE, REPO, fingerprint, require
import run_behavior


def load(path):
    return json.loads(gzip.decompress(path.read_bytes())
                      if path.suffix == '.gz' else path.read_bytes())


def audit(root):
    report = load(root / 'validation.json')
    require(report['success'], 'failed validation')
    for name, seal in report['sources'].items():
        require(fingerprint(REPO / name) == seal, 'stale source: ' + name)
    for name, seal in report['artifacts'].items():
        require(fingerprint(root / name) == seal, 'changed artifact: ' + name)
    for cmd in report['commands']:
        require(cmd['exit'] == 0 and (root / cmd['receipt']).is_file(),
                'incomplete command receipt')
    for group, count in (('paired', 44), ('native', 14), ('behavior', 2),
                         ('behavior-control', 2)):
        manifest = load(root / group / 'manifest.json.gz')
        require(manifest['success'] and len(manifest['runs']) == count,
                'incomplete receipt inventory: ' + group)
        for run in manifest['runs']:
            receipt = load(root / group / run['receipt'])
            require(not receipt['timed_out'], 'timed out process')
            if group == 'native':
                require(receipt['exit'] == 0, 'failed native process')
            else:
                require(run['accepted'] == run.get('expected_acceptance', True),
                        'unexpected online acceptance')
        if group.startswith('behavior'):
            results = []
            for side in ('baseline', 'candidate'):
                r = load(root / group / (side + '-routes.json.gz'))
                require(r['exit'] == 0 and r['accepted'], 'rejected behavior')
                require(r['result']['expected_test_count'] == 307,
                        'missing native checks')
                observations = r['result']['observations']
                require(observations == run_behavior.schema(),
                        'changed ordered proof/staging observations')
                results.append(observations)
            run_behavior.same_behavior(*results)
    sys.path.insert(0, str(HERE.parent / 'compatibility'))
    import staging_contracts
    paired = load(root / 'paired/manifest.json.gz')
    for side in ('baseline', 'candidate'):
        r = load(root / 'paired' / (side + '-Staging-none.json.gz'))
        expected = staging_contracts.expectation(
            HERE.parent / 'compatibility', 'baseline')
        require(r['exit'] == 0 and r['accepted'], 'rejected strict staging')
        require(r['result']['observations'] == expected['observations'],
                'changed sealed global staging/proof contract')
        require(r['result']['expected_test_count'] == 60,
                'missing original staging checks')
    require(paired['staging_contracts']['candidate_expectation'] == 'baseline',
            'expected-red staging cannot satisfy repair acceptance')
    print('TASK18: source seals; 44/14 prior receipts; 307 checks and 116 '
          'validations per behavior side; strict sealed 60-check staging: OK')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--evidence', type=Path, default=HERE / 'evidence/task18')
    args = p.parse_args()
    audit(args.evidence.resolve())


if __name__ == '__main__':
    main()
