#!/usr/bin/env python3
"""Archive completed TASK18 validation receipts, never execute tests."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BASE = 'cccaa27d7099cbadc886983020cbe745db7793f3'


def fingerprint(path):
    data = path.read_bytes()
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def require(value, message):
    if not value:
        raise ValueError(message)


def archive(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    if source.suffix == '.gz':
        shutil.copyfile(source, target)
    else:
        target = target.with_name(target.name + '.gz')
        target.write_bytes(gzip.compress(source.read_bytes(), mtime=0))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    source, out = args.input.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for name, directory, count in (
            ('paired', 'paired', 44), ('native', 'native', 14),
            ('behavior', 'behavior-final', 2),
            ('behavior-control', 'behavior-control-final', 2)):
        manifest = json.loads(
            (source / directory / 'manifest.json').read_text())
        require(manifest['success'] and len(manifest['runs']) == count,
                'incomplete validation: ' + name)
        for f in sorted((source / directory).iterdir()):
            if f.is_file() and f.suffix in ('.json', '.gz'):
                archive(f, out / name / f.name)
    for f in sorted(source.glob('*.log')):
        archive(f, out / f.name)
    require('Hol built successfully.' in
            (source / 'routine.log').read_text(), 'incomplete routine build')
    require('ordinary-tactics.log' in
            (source / 'holmake.log').read_text(), 'missing integrated gate')
    sources = [REPO / 'src/simp/src/Holmakefile',
               REPO / 'src/simp/tests/compatibility/Holmakefile']
    for path in ('src/simp/src/simpLib.sml', 'src/simp/src/simpLib.sig',
                 'src/marker/markerLib.sml', 'src/marker/markerLib.sig'):
        f = REPO / path
        expected = subprocess.check_output(['git', 'show', BASE + ':' + path],
                                           cwd=REPO)
        require(f.read_bytes() == expected, 'nonbaseline ordinary path: ' + path)
        sources.append(f)
    sources += [f for f in HERE.rglob('*') if f.is_file() and
                'evidence' not in f.relative_to(HERE).parts and
                (f.suffix in ('.py', '.sml', '.json') or
                 f.name == 'Holmakefile')]
    commands = [dict(command='python3 -B src/simp/tests/compatibility/'
        'run_paired.py --candidate HEAD --candidate-signature pass '
        '--candidate-behavior baseline --public-contracts --prior-contracts '
        '--staging-contracts --negative-controls --output ' +
        str(source / 'paired'), exit=0, receipt='paired/manifest.json.gz'),
        dict(command='python3 -B src/simp/tests/compatibility/'
            'run_prior_native.py --output ' + str(source / 'native'),
            exit=0, receipt='native/manifest.json.gz'),
        dict(command='bin/build -t --seq=tools/sequences/upto-parallel',
            exit=0, receipt='routine.log.gz'),
        dict(command='bin/Holmake --holstate="$PWD/bin/hol.state0" '
            '--no-project --no-cache -C src/simp/src -j1 HOLSELFTESTLEVEL=1 all',
            exit=0, receipt='holmake.log.gz')]
    for name, extra in (('behavior', ''), ('behavior-control',
                                         ' --candidate ' + BASE)):
        commands.append(dict(command='python3 -B src/simp/tests/tactics/'
            'run_behavior.py' + extra + ' --output ' +
            str(source / (name + '-final')),
            exit=0, receipt=name + '/manifest.json.gz'))
    for name, target in (('behavior', 'tactics'),
                         ('performance', 'tactics/performance'),
                         ('assembly', 'tactics/performance/assembly'),
                         ('compatibility', 'compatibility')):
        commands.append(dict(command='python3 -B -m unittest discover -s '
            'src/simp/tests/' + target + " -p 'test_*.py'", exit=0,
            receipt='python-' + name + '.log.gz'))
    commands += [dict(command=cmd, exit=0, receipt=name + '.log.gz') for name,
        cmd in (
        ('performance-recheck', 'python3 -B src/simp/tests/tactics/performance/'
         'evidence/recheck.py'),
        ('immutable', 'python3 -B src/simp/tests/compatibility/verify_evidence.py'),
        ('ledger', 'python3 -B src/simp/tests/compatibility/coverage_ledger.py'),
        ('pedant', 'tools/h4pedant/h4pedant src/simp/tests/tactics'),
        ('diffcheck', 'git diff --check'))]
    result = dict(schema_version=1, evidence_id='TASK18-legacy-tactics-v1',
        production_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
            cwd=REPO, text=True).strip(), baseline=BASE, success=True,
        scope='Bounded TASK18 staging and local cost audit; not numerical '
              'parity, independent clean builds or whole-plan acceptance',
        commands=commands,
        sources={str(f.relative_to(REPO)): fingerprint(f)
                 for f in sorted(set(sources))},
        artifacts={str(f.relative_to(out)): fingerprint(f)
                   for f in sorted(out.rglob('*')) if f.is_file()})
    (out / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(out / 'validation.json')


if __name__ == '__main__':
    main()
