#!/usr/bin/env python3
"""Recheck TASK16 receipts, graph slopes and separate timing metrics offline.

No interval-overlaps-one result is interpreted as numerical equivalence.
Bounded compiler work/layout acceptance also requires the source/codegen audit.
"""
import gzip
import hashlib
import json
from pathlib import Path
import statistics
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import schema
sys.path.insert(0, str(HERE.parent / 'performance'))
import summarize

ROOT = HERE.parents[3]
EXPERIMENTS = ('timing', 'timing-control', 'long-timing', 'long-control')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def graph_gate(comparison, control):
    for label, row in comparison.items():
        deltas = row['candidate_minus_baseline_words']
        require(len(deltas) == len(schema.SIZES), 'missing graph sizes')
        require(all(d == 0 if control else d <= 0 for d in deltas),
                'retained graph increase: ' + label)
        # Subtraction cancels the common denominators: a rising delta is
        # a worse adjacent slope even if a lower intercept hides it.
        require(all(b == a if control else b <= a
                    for a, b in zip(deltas, deltas[1:])),
                'retained graph slope increase: ' + label)


def metric(rows):
    ratios = [r['candidate'] / r['baseline'] for r in rows
              if r['baseline'] > 0]
    ci = summarize.interval(ratios) if len(ratios) == len(rows) else None
    return dict(seconds_per_operation_by_pair=rows, paired_ratios=ratios,
        median_paired_ratio=statistics.median(ratios) if ratios else None,
        paired_ratio_bootstrap_95_percent=ci,
        numerical_decision=('undefined' if ci is None else
            'slower' if ci[0] > 1 else 'faster' if ci[1] < 1 else
            'inconclusive'))


def audit(folder):
    m = json.loads((folder / 'manifest.json').read_text())
    require(m['success'], 'failed experiment')
    require(m['performance']['pairs'] == 10, 'missing paired processes')
    # The measurements predate this offline analyzer. Their sealed inputs
    # and all selected production sources must still be unchanged.
    for group in ('inputs', 'tools', 'shared_products'):
        for path, seal in m[group].items():
            p = ROOT / path
            require(p.stat().st_size == seal['bytes'] and
                    digest(p) == seal['sha256'], 'input drift: ' + path)
    for selected in m['selections'].values():
        require(all(selected['compiler_matches_pinned'].values()),
                'compiler differs from pinned develop')
        if selected['reference'] == 'worktree':
            for source in selected['sources']:
                require(digest(ROOT / source['git_path']) == source['sha256'],
                        'production source drift: ' + source['git_path'])
    comparison = schema.comparison(m['selections'])
    require(comparison == m['graph_comparison'], 'altered graph comparison')
    graph_gate(comparison, m['baseline_control'])
    metrics, performance_rows, graphs = {}, {}, {}
    for entry in m['runs']:
        r = json.loads(gzip.decompress((folder / entry['receipt']).read_bytes()))
        require(entry['accepted'] and r['accepted'] and r['exit'] == 0 and
                not r['timed_out'], 'failed/missing receipt')
        if r['fixture'] == 'CoreGraph':
            # Recreate the event stream, not its derived graph fields.
            text = ''.join('@@PAIR\t' + str(i) + '\t' + '\t'.join(e) + '\n'
                           for i, e in enumerate(r['result']['events']))
            _, graph = schema.graph(text)
            graphs[r['selection']] = graph
        if r['fixture'] == 'performance':
            performance_rows.setdefault(r['pair'], {})[r['selection']] = r
    require(graphs == {s: v['graphs'] for s, v in m['selections'].items()},
            'altered graph measurements')
    recomputed = summarize.summarize(folder)
    require(recomputed == json.loads(
        (folder / 'performance-summary.json').read_text()),
        'altered stored performance summary')
    for label, values in recomputed['workloads'].items():
        metrics[label] = {key: metric(v['seconds_per_operation_by_pair'])
                          for key, v in values.items()}
        rows = []
        for pair in range(10):
            row = {}
            for side in ('baseline', 'candidate'):
                batches = performance_rows[pair][side]['measurements'][
                    'workloads'][label]['batches']
                row[side] = statistics.median(
                    (b['nongc_usr'] + b['nongc_sys']) / b['iterations']
                    for b in batches)
            rows.append(row)
        metrics[label]['nongc'] = metric(rows)
    return dict(manifest_sha256=digest(folder / 'manifest.json'),
        graph_comparison=comparison, metrics=metrics,
        interpretation='Intervals are numerical diagnostics, not an '
            'equivalence test. Source/codegen/layout gates independently '
            'resolve bounded local compilation work.')


if __name__ == '__main__':
    output = HERE / 'evidence/analysis.json'
    result = {name: audit(HERE / 'evidence' / name) for name in EXPERIMENTS}
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(output)
