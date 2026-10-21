#!/usr/bin/env python3
"""Reproduce the compatibility probes against pinned simplifier sources.

Uses the supplied repository's built hol.state0 and unchanged shared libraries
for both versions; temporary copied sources are deleted after each run.
Pass --bench for four alternating fresh-process benchmark repetitions.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

BASE = 'cccaa27d7099cbadc886983020cbe745db7793f3'
CANDIDATE = 'cf1f863b4e5a9712ce1b179f18274eb3451f3954'
HERE = Path(__file__).resolve().parent

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, default=Path('/home/lukasz/dev/HOL/worktrees/simplifier'))
    p.add_argument('--output', type=Path, default=HERE / 'reproduced')
    p.add_argument('--bench', action='store_true')
    args = p.parse_args()
    repo = args.repo.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    def git(*cmd):
        return subprocess.check_output(['git', '-C', str(repo), *cmd])
    statuses = {}
    with tempfile.TemporaryDirectory(prefix='simplifier-paired-') as temp:
        root = Path(temp)
        for name, rev in [('develop', BASE), ('candidate', CANDIDATE)]:
            dst = root / name
            dst.mkdir()
            for path in git('ls-tree', '-r', '--name-only', rev, 'src/simp/src').decode().splitlines():
                if path.endswith(('.sml', '.sig')) and '/poly/' not in path and '/mosml/' not in path:
                    (dst / Path(path).name).write_bytes(git('show', rev + ':' + path))
            (dst / 'legacytest.sml').write_bytes(git('show', BASE + ':src/simp/src/selftest.sml'))
            for path in git('ls-tree', '-r', '--name-only', CANDIDATE, 'src/simp/tests/contracts').decode().splitlines():
                if path.endswith('.sml'):
                    (dst / Path(path).name).write_bytes(git('show', CANDIDATE + ':' + path))
            for source in ['bench.sml', 'detail.sml', 'memory.sml', 'staging.sml', 'abicheck.sml']:
                shutil.copyfile(HERE / source, dst / source)
            targets = {'legacytest': 'legacytest', 'traversal': 'RunTraversalContracts',
                       'exclusion': 'RunExclusionContracts', 'staging': 'staging',
                       'abicheck': 'abicheck', 'memory': 'memory', 'bench': 'bench', 'detail': 'detail'}
            hmf = f'HOLHEAP = {repo}/bin/hol.state0\nINCLUDES = {repo}/src/simp/src/poly\n'
            for target, source in targets.items():
                hmf += f'{target}.exe: {source}.uo\n\t$(HOLMOSMLC) -o $@ $<\n'
            (dst / 'Holmakefile').write_text(hmf)
            with (output / f'{name}-build.log').open('w') as log:
                subprocess.run([str(repo / 'bin/Holmake'), '--no-project',
                                f'--holstate={repo}/bin/hol.state0', '-C', str(dst), '-j1',
                                *(target + '.exe' for target in targets)],
                               check=True, stdout=log, stderr=subprocess.STDOUT)
            for test in ['legacytest', 'traversal', 'exclusion', 'staging', 'abicheck', 'memory']:
                with (output / f'{name}-{test}.log').open('w') as log:
                    result = subprocess.run(['./' + test + '.exe'], cwd=dst,
                                            stdout=log, stderr=subprocess.STDOUT)
                statuses[name + '-' + test] = result.returncode
                expected = 1 if (name, test) == ('candidate', 'abicheck') else 0
                if result.returncode != expected:
                    raise RuntimeError(f'{name}/{test}: exit {result.returncode}, expected {expected}')
        if args.bench:
            for test in ['bench', 'detail']:
                for name, i in [('develop', 1), ('candidate', 1), ('candidate', 2), ('develop', 2)]:
                    with (output / f'{name}-{test}-{i}.log').open('w') as log:
                        subprocess.run(['./' + test + '.exe'], cwd=root/name, check=True,
                                       stdout=log, stderr=subprocess.STDOUT)
    (output / 'exit-statuses.json').write_text(json.dumps(statuses, indent=2) + '\n')
    print(output)

if __name__ == '__main__':
    main()
