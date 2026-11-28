#!/usr/bin/env python3
"""Delete what a Lean project's root theorems do not need, round after round, checking each round.

    python3 clean.py --fieldlive BIN [--build CMD] [--wrap CMD] [--rounds N] [--commit]
                     [--work DIR] [-- FIELDLIVE_OPTIONS...]

Run from the root of a project. It builds first, then each round:
  1. runs `fieldlive --mode unreachable` (with the FIELDLIVE_OPTIONS after `--`, such as --root
     or --protect), which writes a prune plan and the root theorems' statements and axioms;
  2. checks the roots against round 0: the same statements (hashes) and the same axioms;
  3. deletes the plan with apply-plan.py;
  4. builds (`lake build`, or --build).
It stops when a round deletes nothing. If a build fails or a root changed, that round's edits are
undone, the reason is reported, and it stops with exit status 1; the earlier rounds stay.

--wrap CMD   prefix for the heavy commands (fieldlive and the build), for example
             "systemd-run --user --scope -p MemoryMax=20G" to cap memory
--commit     commit each round that builds (git), so the rounds are separate commits
--work DIR   where the round outputs go (default .fieldlive-clean)
"""
import argparse
import os
import resource
import shlex
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
APPLY = os.path.join(HERE, 'apply-plan.py')


def run(cmd, log=None, **kw):
    print('+', ' '.join(shlex.quote(c) for c in cmd), flush=True)
    if log:
        with open(log, 'w') as f:
            return subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, **kw).returncode
    return subprocess.run(cmd, **kw).returncode


def read_roots(path):
    out = {}
    with open(path, encoding='utf-8') as f:
        for line in f:
            parts = line.rstrip('\n').split('\t')
            if parts and parts[0]:
                out[parts[0]] = (parts[1] if len(parts) > 1 else '', parts[2] if len(parts) > 2 else '')
    return out


def compare_roots(base, now):
    """the differences between two --roots-out files, as messages"""
    msgs = []
    for n, (h, ax) in base.items():
        if n not in now or now[n][0] == 'MISSING':
            msgs.append(f'{n}: gone')
        elif now[n][0] != h:
            msgs.append(f'{n}: statement changed')
        elif now[n][1] != ax:
            msgs.append(f'{n}: axioms changed from [{ax}] to [{now[n][1]}]')
    return msgs


def plan_files(plan, src):
    files = set()
    with open(plan, encoding='utf-8') as f:
        next(f, None)
        for line in f:
            r = line.rstrip('\n').split('\t')
            if len(r) > 2:
                files.add(r[1] or os.path.join(src, *r[2].split('.')) + '.lean')
    return sorted(files)


def main():
    argv = sys.argv[1:]
    fl_opts = []
    if '--' in argv:
        i = argv.index('--')
        argv, fl_opts = argv[:i], argv[i + 1:]
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--fieldlive', required=True, help='the fieldlive binary')
    ap.add_argument('--build', default='lake build')
    ap.add_argument('--wrap', default='')
    ap.add_argument('--rounds', type=int, default=10)
    ap.add_argument('--commit', action='store_true')
    ap.add_argument('--work', default='.fieldlive-clean')
    ap.add_argument('--src', default='.')
    a = ap.parse_args(argv)

    wrap = shlex.split(a.wrap)
    # fieldlive recurses deeply on big terms
    try:
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    except (ValueError, OSError):
        print('warning: could not raise the stack limit; run `ulimit -s unlimited` first')
    os.makedirs(a.work, exist_ok=True)
    # the analysis reads the .olean files, so they have to match the sources
    if run(wrap + shlex.split(a.build), log=os.path.join(a.work, 'build0.log')) != 0:
        print(f'the project does not build as it is; see {a.work}/build0.log')
        return 1
    base = None
    total = 0
    for k in range(a.rounds + 1):
        out = os.path.join(a.work, f'round{k}')
        roots = os.path.join(out, 'roots.tsv')
        os.makedirs(out, exist_ok=True)
        rc = run(wrap + ['lake', 'env', a.fieldlive, '--mode', 'unreachable', '--roots-out', roots]
                 + fl_opts + [out], log=os.path.join(out, 'fieldlive.log'))
        if rc != 0:
            print(f'round {k}: fieldlive failed ({rc}); see {out}/fieldlive.log')
            return 1
        now = read_roots(roots)
        if base is None:
            base = now
            if not base:
                print('no root theorems found: give --root or --root-module after --')
                return 1
            print(f'round 0: {len(base)} root theorems recorded in {roots}')
        else:
            diff = compare_roots(base, now)
            if diff:
                # the previous round's edits built but changed a root: undo them
                print(f'round {k}: the roots changed after round {k - 1}:')
                for m in diff:
                    print('  ' + m)
                restore(prev_saved)
                print(f'undid round {k - 1}')
                return 1
        if k == a.rounds:
            print(f'stopped after {a.rounds} rounds')
            break
        plan = os.path.join(out, 'prune-plan.tsv')
        saved = {}
        for p in plan_files(plan, a.src):
            if os.path.exists(p):
                with open(p, encoding='utf-8') as f:
                    saved[p] = f.read()
        deleted = os.path.join(out, 'deleted.txt')
        res = subprocess.run([sys.executable, APPLY, plan, '--apply', '--src', a.src, '--out', deleted],
                             capture_output=True, text=True)
        with open(os.path.join(out, 'apply.log'), 'w') as f:
            f.write(res.stdout + res.stderr)
        print(f'round {k}: {res.stdout.strip()}')
        if res.returncode != 0:
            restore(saved)
            print(f'round {k}: apply-plan.py failed; see {out}/apply.log')
            return 1
        with open(deleted, encoding='utf-8') as f:
            n = sum(1 for _ in f)
        if n == 0:
            print(f'done: nothing more to delete after {k} rounds; {total} declarations deleted')
            return 0
        if run(wrap + shlex.split(a.build), log=os.path.join(out, 'build.log')) != 0:
            restore(saved)
            print(f'round {k}: the build failed after deleting {n} declarations; undid them. '
                  f'See {out}/build.log and {deleted}: something there is used in a way the '
                  f'analysis did not see.')
            return 1
        total += n
        if a.commit:
            subprocess.run(['git', 'add', '--'] + list(saved), check=True)
            subprocess.run(['git', 'commit', '-q', '-m',
                            f'Delete {n} declarations the root theorems do not need (round {k})'],
                           check=True)
        prev_saved = saved
    print(f'{total} declarations deleted')
    return 0


def restore(saved):
    for p, text in saved.items():
        with open(p, 'w', encoding='utf-8') as f:
            f.write(text)


if __name__ == '__main__':
    sys.exit(main())
