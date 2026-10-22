#!/usr/bin/env python3
"""Offline TASK18 follow-up recheck/compaction. No builds or measurements."""
import argparse
import contextlib
import gzip
import hashlib
import io
import json
import math
from pathlib import Path
import statistics as st
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PERF = HERE.parent
sys.path.insert(0, str(PERF))
import schema
import summarize
import gc_diagnostic as gc
require = schema.require
CAMPAIGNS = ('followup-current', 'followup-control',
             'followup-trace-current', 'followup-trace-control')


def seal(raw):
    return dict(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


def read(path):
    return summarize.read_json(path)


def write_json(path, value):
    raw = (json.dumps(value, indent=2) + '\n').encode()
    if path.suffix == '.gz':
        raw = gzip.compress(raw, mtime=0)
    path.write_bytes(raw)


@contextlib.contextmanager
def recovered(force_archive=False):
    if not force_archive and all((HERE / c).is_dir() for c in CAMPAIGNS):
        yield HERE
        return
    index = read(HERE / 'followup-index.json.gz')
    with tempfile.TemporaryDirectory(prefix='task18-followup-recheck-') as tmp:
        root = Path(tmp)
        with tarfile.open(HERE / 'followup-receipts.tar.xz') as archive:
            require(set(archive.getnames()) == set(index['members']),
                    'follow-up archive inventory drift')
            for member in archive:
                require(member.isfile() and
                        not Path(member.name).is_absolute() and
                        '..' not in Path(member.name).parts, 'unsafe member')
                meta = index['members'][member.name]
                raw = archive.extractfile(member).read()
                require(seal(raw) == meta['stored'], 'stored receipt drift')
                if meta['original_name'].endswith('.gz'):
                    raw = gzip.compress(raw, mtime=0)
                require(seal(raw) == meta['original'], 'original receipt drift')
                dst = root / Path(member.name).parent / meta['original_name']
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(raw)
        yield root


def sources(include_followup=True):
    blobs = {}
    names = ['sources.tar.xz']
    if include_followup:
        names.append('followup-sources.tar.xz')
    for name in names:
        path = HERE / name
        if path.exists():
            with tarfile.open(path) as archive:
                for m in archive:
                    raw = archive.extractfile(m).read()
                    require(seal(raw)['sha256'] == m.name, 'source blob drift')
                    blobs[m.name] = raw
    return blobs


def diagnostic(root, campaign):
    m = read(root / campaign / 'manifest.json')
    require(m['success'] and m['gc_trace'] is True and
            m['baseline_control'] is campaign.endswith('control'),
            'invalid diagnostic manifest')
    keys = schema.selected_keys(m['performance']['rows'])
    pairs, samples = (m['performance'][k] for k in ('pairs', 'samples'))
    fixed = schema.fixed_iterations(m['performance']['fixed_iterations'])
    expected = [(p, s) for p in range(pairs) for s in
                (('baseline', 'candidate') if p % 2 == 0 else
                 ('candidate', 'baseline'))]
    require([(e['pair'], e['selection']) for e in m['runs']] == expected,
            'diagnostic pairs reordered/missing')
    result = {}
    for e in m['runs']:
        require(Path(e['receipt']).name == e['receipt'], 'unsafe receipt')
        r = read(root / campaign / e['receipt'])
        require(e['accepted'] and r['accepted'] and r['exit'] == 0 and
                not r['timed_out'] and r['result']['outcome'] == 'pass',
                'failed diagnostic receipt')
        require((r['pair'], r['selection'], r['fixture']) ==
                (e['pair'], e['selection'], 'tactic-performance'),
                'diagnostic receipt identity mismatch')
        events = r['result']['events']
        obs = [x for x in events if x[0] in
               ('observation', 'check', 'exception')]
        checks = sum(x[0] == 'check' for x in obs)
        require(events[0] == ['begin', e['selection'],
                             'tactic-performance', 'none'] and
                events[-1] == ['end', 'pass', str(checks)] and
                r['result']['expected_test_count'] == checks and
                obs == r['result']['observations'], 'diagnostic protocol drift')
        data, stats = gc.parse_events(obs, samples, fixed, keys)
        require(data == r['measurements'] and stats == r['gc_statistics'],
                'diagnostic measurements/counters drift')
        env = r['environment']
        require(env['PERF_ROWS'] == ','.join(keys) and
                env['PERF_FIXED'] == ','.join(f'{k}={v}' for k, v in
                                            fixed.items()) and
                env['PERF_SAMPLES'] == str(samples), 'diagnostic env drift')
        result[f"{e['pair']}.{e['selection']}"] = gc.trace(r, keys, samples)
    return m, result


def recheck(root):
    current = root / 'followup-current'
    control = root / 'followup-control'
    result = summarize.summarize(current, control)
    require(result == read(root / 'followup-analysis.json'),
            'follow-up inference drift')
    a, b = [read(root / c / 'manifest.json') for c in CAMPAIGNS[:2]]
    keys = schema.selected_keys(a['performance']['rows'])
    old = schema.load_fixed(PERF / 'final-iterations.json')[0]
    expected = {k: v * (16 if k in keys else 1) for k, v in old.items()}
    require(a['performance']['fixed_iterations'] == expected ==
            schema.load_fixed(PERF / 'followup-iterations.json')[0],
            'predeclared 16x schedule drift')
    d, trace_current = diagnostic(root, CAMPAIGNS[2])
    e, trace_control = diagnostic(root, CAMPAIGNS[3])
    for m in (b, d, e):
        require(m['tools'] == a['tools'] and
                m['shared_products'] == a['shared_products'] and
                m['performance']['rows'] == list(keys) and
                m['performance']['samples'] == a['performance']['samples'] and
                m['performance']['fixed_iterations'] == expected,
                'follow-up shared products/schedule mismatch')
    for x, y in ((a, b), (d, e)):
        require(x['inputs'] == y['inputs'], 'paired campaign inputs differ')
    for timing, debug in ((a, d), (b, e)):
        for side in ('baseline', 'candidate'):
            def inventory(m):
                return {s['git_path']: {k: s[k] for k in ('sha256', 'bytes')}
                        for s in m['selections'][side]['sources']}
            require(inventory(timing) == inventory(debug),
                    'timing/diagnostic selected sources differ')
    return dict(fields=list(gc.FIELDS), current=trace_current,
                control=trace_control,
                limits='Separate debug timings; not inference. Nursery sums '
                       'are rounded, omit final tail and include small prefix; '
                       'not exact cumulative allocation.'), result


def pack():
    """Lossless receipt packing; no deletion until caller has rechecked."""
    index = dict(members={}, source_refs=[])
    old_blobs = sources(include_followup=False)
    new_blobs = {}
    paths = [p for c in CAMPAIGNS for p in sorted((HERE / c).iterdir())]
    paths.append(HERE / 'followup-analysis.json')
    with tarfile.open(HERE / 'followup-receipts.tar.xz', 'w:xz') as archive:
        for path in paths:
            require(path.is_file(), 'unexpected campaign directory')
            raw = path.read_bytes()
            stored = gzip.decompress(raw) if path.suffix == '.gz' else raw
            name = str(path.relative_to(HERE))
            if path.suffix == '.gz':
                name = name[:-3]
            index['members'][name] = dict(original_name=path.name,
                original=seal(raw), stored=seal(stored))
            info = tarfile.TarInfo(name)
            info.size = len(stored)
            archive.addfile(info, io.BytesIO(stored))
    for campaign in CAMPAIGNS:
        m = read(HERE / campaign / 'manifest.json')
        refs = [(path, meta) for path, meta in m['inputs'].items()]
        for side, selected in m['selections'].items():
            for source in selected['sources']:
                path = str(Path(m['repo']) / source['git_path'])
                refs.append((path, {k: source[k] for k in ('bytes', 'sha256')}))
        for path, meta in refs:
            digest = meta['sha256']
            if digest not in old_blobs and digest not in new_blobs:
                raw = Path(path).read_bytes()
                require(seal(raw) == meta, 'cannot recover sealed input: '+path)
                new_blobs[digest] = raw
            require(seal(old_blobs.get(digest, new_blobs.get(digest))) == meta,
                    'sealed input mismatch')
            index['source_refs'].append(dict(campaign=campaign,
                                            path=path, **meta))
    with tarfile.open(HERE / 'followup-sources.tar.xz', 'w:xz') as archive:
        for digest, raw in sorted(new_blobs.items()):
            info = tarfile.TarInfo(digest)
            info.size = len(raw)
            archive.addfile(info, io.BytesIO(raw))
    write_json(HERE / 'followup-index.json.gz', index)
    print('packed', len(paths), 'receipts;', len(new_blobs), 'new source blobs')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--pack', action='store_true')
    p.add_argument('--archive', action='store_true',
                   help='verify archived recovery even if originals remain')
    args = p.parse_args()
    if args.pack:
        pack()
    if (HERE / 'followup-index.json.gz').exists():
        blobs = sources()
        for ref in read(HERE / 'followup-index.json.gz')['source_refs']:
            require(seal(blobs[ref['sha256']]) ==
                    {k: ref[k] for k in ('bytes', 'sha256')}, 'source drift')
    with recovered(args.archive) as root:
        diagnostic_result, result = recheck(root)
        path = HERE / 'followup-diagnostic.json.gz'
        if path.exists():
            require(read(path) == diagnostic_result, 'diagnostic summary drift')
        else:
            write_json(path, diagnostic_result)
        for key in result['candidate']:
            print(key)
            for metric in ('cpu', 'nongc_cpu', 'gc_cpu'):
                x = result['candidate'][key][metric]['inference']
                y = result['control'][key][metric]['inference']
                z = result['contrast'][key][metric]
                print(' ', metric, 'current',
                      round(math.exp(x['mean_log']), 6), x['individual95'],
                      x['family95'], 'control',
                      round(math.exp(y['mean_log']), 6),
                      'contrast', z['individual95'], z['family95'])
    print('PASS: 40 timing + 8 diagnostic processes; protocols, counts, '
          'proof gates, 66-row-family inference and independent contrasts')


if __name__ == '__main__':
    main()
