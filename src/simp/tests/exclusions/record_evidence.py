#!/usr/bin/env python3
"""Archive TASK17 receipts after validation; does not execute any tests."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def fingerprint(path):
    data = path.read_bytes()
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def archive(source, dest):
    dest.parent.mkdir(parents=True, exist_ok=True)
    if source.suffix == '.gz':
        shutil.copyfile(source, dest)
    else:
        dest = dest.with_name(dest.name + '.gz')
        dest.write_bytes(gzip.compress(source.read_bytes(), mtime=0))
    return dest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--validation', type=Path, required=True)
    p.add_argument('--behavior', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name, source, count in (
            ('paired', args.validation / 'paired', 44),
            ('native', args.validation / 'native', 14),
            ('behavior', args.behavior, 2)):
        manifest = json.loads((source / 'manifest.json').read_text())
        assert manifest['success'] is True
        assert len(manifest['runs']) == count
        for f in source.iterdir():
            if f.is_file() and f.suffix in ('.json', '.gz'):
                archive(f, out / name / f.name)
    for f in args.validation.glob('*.log'):
        archive(f, out / f.name)
    sources = [REPO / 'src/simp/src/Holmakefile',
               REPO / 'src/simp/src/simpLib.sml',
               REPO / 'src/simp/src/simpLib.sig']
    sources += [f for f in HERE.rglob('*') if f.is_file() and
                'evidence' not in f.relative_to(HERE).parts and
                f.suffix in ('.py', '.sml')]
    sources += [HERE / 'Holmakefile']
    baseline = 'cccaa27d7099cbadc886983020cbe745db7793f3'
    for name in ('simpLib.sml', 'simpLib.sig'):
        f = REPO / 'src/simp/src' / name
        expected = subprocess.check_output(
            ['git', 'show', baseline + ':' + str(f.relative_to(REPO))],
            cwd=REPO)
        assert f.read_bytes() == expected
    result = dict(schema_version=1, evidence_id='TASK17-literal-replay-v1',
        production_head=subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
        baseline=baseline, success=True,
        scope='Bounded TASK17 literal exclusions/replay, not final plan gate',
        commands=[
            dict(command='run_paired.py --candidate HEAD '
                 '--candidate-signature pass --candidate-behavior baseline '
                 '--public-contracts --prior-contracts --staging-contracts '
                 '--negative-controls --output ' +
                 str(args.validation / 'paired'),
                 exit=0, receipt='paired/manifest.json.gz'),
            dict(command='run_prior_native.py '
                 '--output ' + str(args.validation / 'native'),
                 exit=0, receipt='native/manifest.json.gz'),
            dict(command='run_behavior.py '
                 '--output ' + str(args.behavior),
                 exit=0, receipt='behavior/manifest.json.gz'),
            dict(command='bin/build -t '
                 '--seq=tools/sequences/upto-parallel',
                 exit=0, receipt='routine-final.log.gz'),
            dict(command='bin/Holmake --holstate=$PWD/bin/hol.state0 '
                 '--no-project --no-cache -C src/simp/src -j1 '
                 'HOLSELFTESTLEVEL=1 all',
                 exit=0, receipt='holmake-final.log.gz')],
        sources={str(f.relative_to(REPO)): fingerprint(f)
                 for f in sorted(set(sources))},
        artifacts={str(f.relative_to(out)): fingerprint(f)
                   for f in sorted(out.rglob('*')) if f.is_file()})
    (out / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(out / 'validation.json')


if __name__ == '__main__':
    main()
