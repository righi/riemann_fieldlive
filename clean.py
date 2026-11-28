#!/usr/bin/env python3
"""Delete what a Lean project's root theorems do not need, step after step, checking each step.

    python3 clean.py --fieldlive BIN [--fields] [--build CMD] [--wrap CMD] [--rounds N]
                     [--commit] [--work DIR] [-- FIELDLIVE_OPTIONS...]

Run from the root of a project. It builds first. Then, until nothing changes:
  * unreachable rounds: `fieldlive --mode unreachable` writes a prune plan, apply-plan.py deletes
    it, and the project is built, until a round deletes nothing;
  * with --fields, a field round: `fieldlive` (fields mode) finds the dead structure fields,
    `fieldedit` finds every place they are written, remove-fields.py removes them together with
    what only they kept alive, and the project is built. Fields fieldedit cannot remove are left
    alone. If the build fails, the fields are tried again in halves.
Every analysis also writes the root theorems' statement hashes and axioms (FIELDLIVE_OPTIONS
after `--`, such as --root or --protect, choose them); they must stay as in the first one.

If an unreachable round does not build, or a root changed, that step is undone, the reason is
reported, and it stops with exit status 1. The steps before stay.

--fieldedit BIN  the fieldedit binary (default: next to the fieldlive binary)
--wrap CMD       prefix for the heavy commands (fieldlive, fieldedit and the build), for example
                 "systemd-run --user --scope -p MemoryMax=20G" to cap memory
--commit         commit each step that builds (git), so the steps are separate commits
--work DIR       where the step outputs go (default .fieldlive-clean)
"""
import argparse
import os
import resource
import shlex
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
APPLY = os.path.join(HERE, 'apply-plan.py')
REMOVE = os.path.join(HERE, 'remove-fields.py')


class Stop(Exception):
    """stop with exit status 1, after saying why"""


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


def tsv_files(path, file_col, mod_col, src):
    """the source files named in a fieldlive TSV (by path, or by module)"""
    files = set()
    if not os.path.exists(path):
        return files
    with open(path, encoding='utf-8') as f:
        next(f, None)
        for line in f:
            r = line.rstrip('\n').split('\t')
            if len(r) > max(file_col, mod_col):
                files.add(r[file_col] or os.path.join(src, *r[mod_col].split('.')) + '.lean')
    return files


def snapshot(files):
    saved = {}
    for p in files:
        if os.path.exists(p):
            with open(p, encoding='utf-8') as f:
                saved[p] = f.read()
    return saved


def restore(saved):
    for p, text in saved.items():
        with open(p, 'w', encoding='utf-8') as f:
            f.write(text)


def count_lines(path, skip_header=False):
    if not os.path.exists(path):
        return 0
    with open(path, encoding='utf-8') as f:
        return sum(1 for _ in f) - (1 if skip_header else 0)


class Cleaner:
    def __init__(self, a, fl_opts):
        self.a = a
        self.fl_opts = fl_opts
        self.wrap = shlex.split(a.wrap)
        self.base = None
        self.step = 0
        self.last_saved = None  # the files as they were before the last step that built
        self.decls = 0
        self.fields = 0

    def out(self, what):
        self.step += 1
        d = os.path.join(self.a.work, f'{self.step:02d}-{what}')
        os.makedirs(d, exist_ok=True)
        return d

    def build(self, log):
        return run(self.wrap + shlex.split(self.a.build), log=log) == 0

    def analyse(self, out, mode, extra=()):
        """run fieldlive and check the roots against the first analysis"""
        roots = os.path.join(out, 'roots.tsv')
        rc = run(self.wrap + ['lake', 'env', self.a.fieldlive, '--mode', mode, '--roots-out', roots]
                 + list(extra) + self.fl_opts + [out], log=os.path.join(out, 'fieldlive.log'))
        if rc != 0:
            raise Stop(f'fieldlive failed ({rc}); see {out}/fieldlive.log')
        now = read_roots(roots)
        if self.base is None:
            if not now:
                raise Stop('no root theorems found: give --root or --root-module after --')
            self.base = now
            print(f'{len(now)} root theorems recorded in {roots}')
            return
        diff = compare_roots(self.base, now)
        if diff:
            msg = 'the roots changed after the last step:\n' + '\n'.join('  ' + m for m in diff)
            if self.last_saved is not None:
                restore(self.last_saved)
                msg += '\nundid the last step (rebuild before using the tree)'
            raise Stop(msg)

    def accept(self, saved, message):
        self.last_saved = saved
        if self.a.commit:
            subprocess.run(['git', 'add', '--'] + list(saved), check=True)
            subprocess.run(['git', 'commit', '-q', '-m', message], check=True)

    def unreachable_round(self):
        """one round; returns the number of declarations deleted"""
        out = self.out('unreachable')
        self.analyse(out, 'unreachable')
        plan = os.path.join(out, 'prune-plan.tsv')
        saved = snapshot(tsv_files(plan, 1, 2, self.a.src))
        deleted = os.path.join(out, 'deleted.txt')
        res = subprocess.run([sys.executable, APPLY, plan, '--apply', '--src', self.a.src,
                              '--out', deleted], capture_output=True, text=True)
        with open(os.path.join(out, 'apply.log'), 'w') as f:
            f.write(res.stdout + res.stderr)
        print(f'step {self.step}: {res.stdout.strip()}')
        if res.returncode != 0:
            restore(saved)
            raise Stop(f'apply-plan.py failed; see {out}/apply.log')
        n = count_lines(deleted)
        if n == 0:
            return 0
        if not self.build(os.path.join(out, 'build.log')):
            restore(saved)
            raise Stop(f'the build failed after deleting {n} declarations; undid them. See '
                       f'{out}/build.log and {deleted}: something there is used in a way the '
                       f'analysis did not see.')
        self.decls += n
        self.accept(saved, f'Delete {n} declarations the root theorems do not need')
        return n

    def field_round(self, only=None, depth=0):
        """remove dead fields (all, or those in `only`: [(structure, field)]); returns how many"""
        out = self.out('fields')
        extra = []
        if only is not None:
            path = os.path.join(out, 'only.tsv')
            with open(path, 'w', encoding='utf-8') as f:
                for s, fld in only:
                    f.write(f'{s}\t{fld}\n')
            extra = ['--only', path]
        self.analyse(out, 'fields', extra)
        dead = []
        with open(os.path.join(out, 'dead-fields.tsv'), encoding='utf-8') as f:
            next(f, None)
            for line in f:
                r = line.rstrip('\n').split('\t')
                dead.append((r[0], r[1]))
        if not dead:
            print(f'step {self.step}: no dead fields')
            return 0
        sites = os.path.join(out, 'field-sites.tsv')
        rc = run(self.wrap + ['lake', 'env', self.a.fieldedit, sites, os.path.join(out, 'field-edits.tsv')],
                 log=os.path.join(out, 'fieldedit.log'))
        if rc != 0:
            print(f'step {self.step}: fieldedit failed ({rc}); see {out}/fieldedit.log. Fields left alone.')
            return 0
        saved = snapshot(tsv_files(sites, 7, 6, self.a.src) | tsv_files(os.path.join(out, 'field-plan.tsv'), 1, 2, self.a.src))
        res = subprocess.run([sys.executable, REMOVE, out, '--apply', '--src', self.a.src],
                             capture_output=True, text=True)
        with open(os.path.join(out, 'remove.log'), 'w') as f:
            f.write(res.stdout + res.stderr)
        print(f'step {self.step}: {res.stdout.strip()}')
        if res.returncode == 3:
            # some fields cannot be removed here: plan again for the others alone
            removable = []
            with open(os.path.join(out, 'removable-fields.tsv'), encoding='utf-8') as f:
                for line in f:
                    s, fld = line.rstrip('\n').split('\t')
                    removable.append((s, fld))
            if not removable or (only is not None and len(removable) == len(only)):
                return 0
            return self.field_round(removable, depth)
        if res.returncode != 0:
            restore(saved)
            print(f'step {self.step}: remove-fields.py failed; see {out}/remove.log. Fields left alone.')
            return 0
        if self.build(os.path.join(out, 'build.log')):
            self.fields += len(dead)
            self.decls += max(0, count_lines(os.path.join(out, 'field-plan.tsv'), skip_header=True))
            self.accept(saved, f'Remove {len(dead)} structure fields nothing reads')
            return len(dead)
        restore(saved)
        print(f'step {self.step}: the build failed after removing {len(dead)} fields; undid it '
              f'(see {out}/build.log)')
        if len(dead) == 1 or depth >= self.a.field_depth:
            return 0
        half = len(dead) // 2
        return self.field_round(dead[:half], depth + 1) + self.field_round(dead[half:], depth + 1)

    def go(self):
        os.makedirs(self.a.work, exist_ok=True)
        # the analysis reads the .olean files, so they have to match the sources
        if not self.build(os.path.join(self.a.work, 'build0.log')):
            raise Stop(f'the project does not build as it is; see {self.a.work}/build0.log')
        for _ in range(self.a.rounds):
            while self.unreachable_round():
                pass
            if not self.a.fields or self.field_round() == 0:
                break
        print(f'done: {self.decls} declarations deleted, {self.fields} fields removed, '
              f'in {self.step} steps')


def main():
    argv = sys.argv[1:]
    fl_opts = []
    if '--' in argv:
        i = argv.index('--')
        argv, fl_opts = argv[:i], argv[i + 1:]
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--fieldlive', required=True, help='the fieldlive binary')
    ap.add_argument('--fieldedit')
    ap.add_argument('--fields', action='store_true', help='also remove dead structure fields')
    ap.add_argument('--field-depth', type=int, default=4,
                    help='how many times to halve a set of fields whose removal does not build')
    ap.add_argument('--build', default='lake build')
    ap.add_argument('--wrap', default='')
    ap.add_argument('--rounds', type=int, default=10, help='at most this many field rounds')
    ap.add_argument('--commit', action='store_true')
    ap.add_argument('--work', default='.fieldlive-clean')
    ap.add_argument('--src', default='.')
    a = ap.parse_args(argv)
    a.fieldlive = os.path.abspath(a.fieldlive)
    a.fieldedit = os.path.abspath(a.fieldedit or os.path.join(os.path.dirname(a.fieldlive), 'fieldedit'))
    # fieldlive recurses deeply on big terms
    try:
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    except (ValueError, OSError):
        print('warning: could not raise the stack limit; run `ulimit -s unlimited` first')
    try:
        Cleaner(a, fl_opts).go()
    except Stop as e:
        print(f'stopped: {e}')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
