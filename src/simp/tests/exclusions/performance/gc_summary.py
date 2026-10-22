#!/usr/bin/env python3
"""Offline focused GC evidence recheck; no final-campaign edits or gate."""
import gzip
import json
import math
from pathlib import Path
import re
import statistics as st
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import schema
import summarize

TARGETS = ('replay.1000', 'missing.10000', 'matching.10000',
           'qualified.10000')
FIELDS = ('full_gc', 'partial_gc', 'sharing', 'heap_bytes',
          'heap_free_last_full', 'heap_free_last_gc', 'allocation_bytes',
          'allocation_free', 'code_bytes', 'stack_bytes')


def load(name):
    root = HERE / 'evidence' / name
    manifest = summarize.read_json(root / 'manifest.json')
    assert manifest['success']
    assert manifest['ordinary_source_byte_identical'] == {
        'simpLib.sml': True, 'simpLib.sig': True}
    result = {}
    for entry in manifest['runs']:
        r = summarize.read_json(root / entry['receipt'])
        assert entry['accepted'] and r['accepted'] and r['exit'] == 0
        assert not r['timed_out']
        events = r['result']['observations']
        checks = sum(e[0] == 'check' for e in events)
        assert r['result']['events'][0] == [
            'begin', entry['selection'], 'exclusion-performance', 'none']
        assert r['result']['events'][-1] == ['end', 'pass', str(checks)]
        assert r['result']['expected_test_count'] == checks
        assert r['result']['outcome'] == 'pass'
        expected_stats = [f'gcstats.{phase}.{key}.{edge}'
            for key in schema.KEYS
            for phase in ['calibration'] + [f'batch{i}' for i in
                range(manifest['performance']['samples'])]
            for edge in ('before', 'after')]
        assert list(r['gc_statistics']) == expected_stats
        regular = [e for e in events if not (e[0] == 'observation' and
                   e[1].startswith(('gcstats.', 'gctrace.')))]
        _, data = schema.timing_events(regular,
            manifest['performance']['samples'],
            manifest['performance']['fixed_iterations'])
        assert data == r['measurements']
        for e in events:
            if e[0] == 'observation' and e[1].startswith('gcstats.'):
                actual = list(map(int, e[2].split(',')))
                assert actual == r['gc_statistics'][e[1]]
        result[entry['pair'], entry['selection']] = r
    n = manifest['performance']['pairs']
    assert set(result) == {(p, s) for p in range(n)
                           for s in ('baseline', 'candidate')}
    return manifest, result


def diagnostic(name):
    manifest, runs = load(name)
    out = {}
    for key in TARGETS:
        pairs = []
        for pair in range(manifest['performance']['pairs']):
            sides = {}
            for side in ('baseline', 'candidate'):
                r = runs[pair, side]
                stats = r['gc_statistics']
                rows = r['measurements'][key]
                details = []
                for i, row in enumerate(rows):
                    a = stats[f'gcstats.batch{i}.{key}.before']
                    b = stats[f'gcstats.batch{i}.{key}.after']
                    assert b[0] >= a[0] and b[1] >= a[1]
                    details.append(dict(full_gc=b[0]-a[0],
                        partial_gc=b[1]-a[1],
                        before=dict(zip(FIELDS, a)),
                        after=dict(zip(FIELDS, b)),
                        wall=row['raw'][0],
                        cpu=row['cpu']*row['iterations'],
                        gc_cpu=row['gc_cpu']*row['iterations']))
                sides[side] = dict(samples=details,
                    median_cpu=st.median(x['cpu'] for x in details),
                    median_gc=st.median(x['gc_cpu'] for x in details))
            pairs.append(sides)
        ratios = [p['candidate']['median_gc']/p['baseline']['median_gc']
                  for p in pairs]
        cpu_ratios = [p['candidate']['median_cpu']/p['baseline']['median_cpu']
                      for p in pairs]
        out[key] = dict(pairs=pairs, gc_ratios=ratios,
            cpu_ratios=cpu_ratios,
            gc_geomean=math.exp(st.mean(map(math.log, ratios))),
            gc_individual95=summarize.estimate(ratios)['individual95'],
            cpu_geomean=math.exp(st.mean(map(math.log, cpu_ratios))))
    return out


def size(text):
    m = re.fullmatch(r'([0-9.]+)([KMG]?)', text)
    assert m, text
    return float(m[1]) * 1024**(' KMG'.index(m[2]) if m[2] else 0)


def trace():
    manifest, runs = load('gc-trace-current')
    out = {}
    for (_, side), r in runs.items():
        events, positions = [], {(0, 0): 0}
        full, partial = 0, 0
        for line in r['diagnostics']:
            if line.startswith('GC: Beginning quick GC'):
                partial += 1
                events.append(dict(kind='partial'))
                positions[full, partial] = len(events)
            elif line.startswith('GC: Full GC,'):
                full += 1
                events.append(dict(kind='full'))
                positions[full, partial] = len(events)
            elif 'GC (before)' in line:
                m = re.search(r'Alloc space used (\S+) of (\S+)', line)
                assert m
                events[-1]['used_nursery_bytes'] = size(m[1])
                events[-1]['capacity_bytes'] = size(m[2])
            elif 'Adjusting space for allocation area from' in line:
                events[-1].setdefault('adjustments', []).append(line)
        last = r['gc_statistics']['gcstats.batch2.replay.10000.after']
        assert (full, partial) == tuple(last[:2])
        sideout = {}
        for key in TARGETS:
            rows = []
            for i in range(3):
                stats = r['gc_statistics']
                a = stats[f'gcstats.batch{i}.{key}.before']
                b = stats[f'gcstats.batch{i}.{key}.after']
                selected = events[positions[tuple(a[:2])]:
                                  positions[tuple(b[:2])]]
                assert len(selected) == b[0]+b[1]-a[0]-a[1]
                used = [x['used_nursery_bytes'] for x in selected]
                rows.append(dict(full_gc=b[0]-a[0], partial_gc=b[1]-a[1],
                    nursery_used_sum_mib=sum(used)/2**20,
                    nursery_used_range_mib=[min(used)/2**20,
                                             max(used)/2**20],
                    first_gc=selected[0], last_gc=selected[-1]))
            sideout[key] = rows
        out[side] = sideout
    return out


def main():
    a, _ = load('gc-long-current')
    b, _ = load('gc-long-control')
    assert a['tools'] == b['tools']
    assert a['shared_products'] == b['shared_products']
    assert a['performance']['fixed_iterations'] == \
        b['performance']['fixed_iterations']
    for name in ('ExclusionInputs.sml', 'GCPerformance.sml'):
        assert a['inputs'][str(HERE / name)] == b['inputs'][str(HERE / name)]
    result = dict(scope=__doc__, statistics_fields=FIELDS,
        current=diagnostic('gc-long-current'),
        control=diagnostic('gc-long-control'), trace=trace())
    path = HERE / 'evidence' / 'gc-diagnostic-summary.json.gz'
    raw = (json.dumps(result, indent=2)+'\n').encode()
    path.write_bytes(gzip.compress(raw, mtime=0))
    for key in TARGETS:
        a, b = result['current'][key], result['control'][key]
        print(key, 'current_gc', round(a['gc_geomean'], 6),
              a['gc_individual95'], 'control_gc', round(b['gc_geomean'], 6),
              'current_cpu', round(a['cpu_geomean'], 6))
        for side in ('baseline', 'candidate'):
            ds = [s for p in a['pairs'] for s in p[side]['samples']]
            print(' ', side, 'full', sum(s['full_gc'] for s in ds),
                  'partial', sum(s['partial_gc'] for s in ds),
                  'cpu', round(sum(s['cpu'] for s in ds), 6),
                  'gc', round(sum(s['gc_cpu'] for s in ds), 6))
    print(path)


if __name__ == '__main__':
    main()
