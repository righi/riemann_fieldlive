#!/usr/bin/env python3
"""Delete the declarations listed in fieldlive's prune-plan.tsv from a Lean source tree.

    python3 apply-plan.py PLAN [--src DIR] [--apply] [--out deleted.txt]

PLAN   prune-plan.tsv from a fieldlive run: one row per declaration, with its file, module and
       exact source range (from Lean's declaration ranges, doc comment and attributes included).
--src  where module sources live, for rows whose file fieldlive could not find
       (module `A.B` is read from DIR/A/B.lean)

Rows whose `check` column is `text` hold a theorem proved by `rfl`. `simp only [h]` uses such a
theorem without leaving a trace in the proof, so the kernel cannot tell whether it is used: such a
row is deleted only when no other source text under --src mentions its name (the last component,
as a whole word), outside the rows being deleted.

Without --apply it only reports. For each range it also deletes:
  * the `open … in`, `variable … in`, `set_option … in`, `include … in` and `omit … in` lines
    directly above it, which apply only to that declaration;
  * one of the blank lines the deletion leaves next to each other.
A range that shares a line with other code is skipped and reported, never cut mid-line.
Build afterwards: the plan is exact about kernel references, but not about what elaboration does
with names alone.
"""
import argparse
import collections
import csv
import os
import re
import sys

IN_PREFIX = re.compile(r'^\s*(open|variable|set_option|include|omit|attribute|local\s+notation|'
                       r'notation|universe)\b.*\bin\s*$')


IDENT = re.compile(r"[A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2080-\u209c\u2100-\u214f][\w'!?\u2080-\u209c\u1d62-\u1d6a]*")


def short(decl):
    """the last component of a declaration name as fieldlive writes it (`private A.b` -> `b`)"""
    return decl.removeprefix('private ').rsplit('.', 1)[-1]


def text_check(rows, src):
    """rows marked `text` whose name is written somewhere outside the rows being deleted:
    {(path, start_line): 'file:line'}. Repeats until stable, since a kept row's text counts."""
    names = {}
    for path, rs in rows.items():
        for r in rs:
            if r[6] == 'text':
                for d in r[5].split(';'):
                    if d:
                        names.setdefault(short(d), set()).add((path, r[0]))
    if not names:
        return {}
    hits = collections.defaultdict(list)  # name -> [(path, line)]
    for root, _, files in os.walk(src):
        if '/.lake' in root or root.endswith('.lake'):
            continue
        for fn in files:
            if not fn.endswith('.lean'):
                continue
            path = os.path.join(root, fn)
            with open(path, encoding='utf-8') as f:
                for i, line in enumerate(f, 1):
                    for w in IDENT.findall(line):
                        part = w.rsplit('.', 1)[-1]
                        if part in names:
                            hits[part].append((os.path.realpath(path), i))
    spans = {}  # realpath -> [(start, end, key)]
    for path, rs in rows.items():
        for r in rs:
            spans.setdefault(os.path.realpath(path), []).append((r[0], r[2], (path, r[0])))
    skip = {}
    while True:
        changed = False
        for name, keys in names.items():
            for key in keys:
                if key in skip:
                    continue
                for p, ln in hits.get(name, []):
                    inside = [k for s, e, k in spans.get(p, []) if s <= ln <= e]
                    if not inside or any(k in skip for k in inside):
                        skip[key] = f'{p}:{ln}'
                        changed = True
                        break
        if not changed:
            return skip


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('plan')
    ap.add_argument('--src', default='.')
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--out', default='prune-deleted.txt')
    a = ap.parse_args()

    rows = collections.defaultdict(list)
    with open(a.plan, encoding='utf-8') as f:
        for r in csv.DictReader(f, delimiter='\t'):
            path = r['file'] or os.path.join(a.src, *r['module'].split('.')) + '.lean'
            rows[path].append((int(r['start_line']), int(r['start_col']), int(r['end_line']),
                               int(r['end_col']), r['module'], r['declarations'],
                               r.get('check') or 'exact'))
    text_skip = text_check(rows, a.src)

    deleted, skipped, lines_removed = [], [], 0
    for path, rs in sorted(rows.items()):
        if not os.path.exists(path):
            skipped += [(path, r[0], 'file not found', r[5]) for r in rs]
            continue
        with open(path, encoding='utf-8') as f:
            text = f.read()
        lines = text.split('\n')
        cut = set()
        for sl, sc, el, ec, mod, names, check in rs:
            if (path, sl) in text_skip:
                skipped.append((path, sl, f'name written in {text_skip[(path, sl)]}', names))
                continue
            # Lean lines are 1-based; columns count code points, as Python strings do
            if sl < 1 or el > len(lines):
                skipped.append((path, sl, 'range outside the file', names))
                continue
            if lines[sl - 1][:sc].strip() or lines[el - 1][ec:].strip():
                skipped.append((path, sl, 'shares a line with other code', names))
                continue
            span = set(range(sl - 1, el))
            k = sl - 2
            while k >= 0 and IN_PREFIX.match(lines[k]):
                span.add(k)
                k -= 1
            cut |= span
            deleted.append((path, sl, mod, names))
        kept = [l for i, l in enumerate(lines) if i not in cut]
        # collapse the blank lines a deletion leaves behind
        out = []
        for l in kept:
            if not l.strip() and out and not out[-1].strip():
                continue
            out.append(l)
        lines_removed += len(lines) - len(out)
        if a.apply:
            with open(path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(out))

    with open(a.out, 'w', encoding='utf-8') as f:
        for path, sl, mod, names in deleted:
            f.write(f'{mod}\t{sl}\t{names}\n')
    verb = 'deleted' if a.apply else 'would delete'
    print(f'{verb} {len(deleted)} declarations ({lines_removed} lines) in {len(rows)} files; '
          f'list in {a.out}')
    for path, sl, why, names in skipped:
        print(f'skipped {path}:{sl} ({why}): {names}', file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
