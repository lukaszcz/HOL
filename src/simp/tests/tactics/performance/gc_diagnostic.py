#!/usr/bin/env python3
"""TASK18 separate GC trace parser; never feeds timing inference."""
import re
import schema

FIELDS = ('full_gc', 'partial_gc', 'sharing', 'heap_bytes',
          'heap_free_last_full', 'heap_free_last_gc', 'allocation_bytes',
          'allocation_free', 'code_bytes', 'stack_bytes')
require = schema.require


def parse_events(events, samples, fixed, keys):
    keys = schema.selected_keys(keys)
    stats, regular, markers = {}, [], []
    for e in events:
        if e[0] == 'observation' and e[1].startswith('gcstats.'):
            require(e[1] not in stats, 'duplicate GC statistics')
            stats[e[1]] = schema.fragments.integers(e[2], 10)
        elif e[0] == 'observation' and e[1].startswith('gctrace.'):
            markers.append(e)
        else:
            regular.append(e)
    expected = [f'gcstats.{phase}.{key}.{edge}' for key in keys
                for phase in ['calibration'] + [f'batch{i}' for i in
                    range(samples)] for edge in ('before', 'after')]
    require(list(stats) == expected, 'incomplete/reordered GC statistics')
    expected_markers = [['observation', f'gctrace.{edge}.{phase}{i}.{key}',
                         edge] for key in keys
                        for phase, i in [('calibration', 0)] +
                            [('batch', j) for j in range(samples)]
                        for edge in ('begin', 'end')]
    require(markers == expected_markers, 'incomplete/reordered trace markers')
    _, data = schema.timing_events(regular, samples, fixed, keys)
    for key in keys:
        for phase in ['calibration'] + [f'batch{i}' for i in range(samples)]:
            a, b = [stats[f'gcstats.{phase}.{key}.{edge}']
                    for edge in ('before', 'after')]
            require(all(b[i] >= a[i] for i in range(3)),
                    'decreasing GC counters')
    return data, stats


def size(text):
    m = re.fullmatch(r'([0-9.]+)([KMG]?)', text)
    require(m is not None, 'invalid trace size: ' + text)
    return float(m[1]) * 1024**(' KMG'.index(m[2]) if m[2] else 0)


def trace(receipt, keys, samples):
    events, positions = [], {(0, 0): 0}
    full, partial = 0, 0
    for line in receipt['diagnostics']:
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
            require(m is not None and events, 'missing trace allocation size')
            events[-1]['used_nursery_bytes'] = size(m[1])
            events[-1]['capacity_bytes'] = size(m[2])
        elif 'Adjusting space for allocation area from' in line:
            require(events, 'adjustment without GC')
            events[-1].setdefault('adjustments', []).append(line)
    stats = receipt['gc_statistics']
    last = stats[f'gcstats.batch{samples-1}.{keys[-1]}.after']
    require((full, partial) == tuple(last[:2]), 'trace totals mismatch')
    result = {}
    for key in keys:
        rows = []
        for i in range(samples):
            a, b = [stats[f'gcstats.batch{i}.{key}.{edge}']
                    for edge in ('before', 'after')]
            selected = events[positions[tuple(a[:2])]:
                              positions[tuple(b[:2])]]
            require(len(selected) == b[0]+b[1]-a[0]-a[1],
                    'trace batch count mismatch')
            used = [e['used_nursery_bytes'] for e in selected]
            capacity = [e['capacity_bytes'] for e in selected]
            row = receipt['measurements'][key][i]
            rows.append(dict(full_gc=b[0]-a[0], partial_gc=b[1]-a[1],
                before=dict(zip(FIELDS, a)), after=dict(zip(FIELDS, b)),
                measurement=row,
                nursery_used_sum_mib=sum(used)/2**20,
                nursery_used_range_mib=([min(used)/2**20, max(used)/2**20]
                                        if used else []),
                capacity_range_mib=([min(capacity)/2**20,
                                     max(capacity)/2**20] if capacity else []),
                first_gc=selected[0] if selected else None,
                last_gc=selected[-1] if selected else None))
        result[key] = rows
    return dict(total_full=full, total_partial=partial, rows=result)
