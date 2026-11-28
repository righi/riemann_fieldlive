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
A range that shares a line with other code is skipped and reported, never cut mid-line. A row that
is skipped keeps the rows it mentions (the plan's `needs` column), and so on.
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


def code_lines(text):
    """the lines of a Lean source with comments (nested `/- -/`, `--`) and string literals blanked"""
    out, i, n, depth = [], 0, len(text), 0
    buf = []
    while i < n:
        c = text[i]
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2; buf.append('  '); continue
            if text.startswith('-/', i):
                depth -= 1; i += 2; buf.append('  '); continue
            buf.append('\n' if c == '\n' else ' '); i += 1; continue
        if text.startswith('/-', i):
            depth = 1; i += 2; buf.append('  '); continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            buf.append(' ' * (j - i)); i = j; continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"' and text[j] != '\n':
                j += 2 if text[j] == '\\' else 1
            buf.append(' ' * (min(j + 1, n) - i)); i = j + 1; continue
        buf.append(c); i += 1
    return ''.join(buf).split('\n')


def read_decl_ranges(path):
    """{realpath: sorted [(start, end)]} from fieldlive's decl-ranges.tsv"""
    out = collections.defaultdict(list)
    with open(path, encoding='utf-8') as f:
        for r in csv.DictReader(f, delimiter='\t'):
            out[os.path.realpath(r['file'])].append((int(r['start_line']), int(r['end_line'])))
    for v in out.values():
        v.sort()
    return out


def inside(spans, ln):
    """whether line `ln` is in one of the (start, end) spans"""
    return any(s <= ln <= e for s, e in spans)


def text_check(rows, src, decls=None):
    """rows whose name is written somewhere it counts, outside the rows being deleted:
    {(path, start_line): 'file:line'}. For a `text` row (a theorem proved by `rfl`, which
    `simp only [h]` uses without a trace) that is anywhere. For an `exact` row it is only outside
    every declaration (`decls`, from decl-ranges.tsv): uses inside declarations are in the kernel
    terms, but `variable`, `attribute` and the like are not. Comments and strings do not count.
    Repeats until stable, since a kept row's text counts."""
    names = {}  # short name -> {(key, check)}
    for path, rs in rows.items():
        for r in rs:
            if r[6] == 'text' or decls is not None:
                for d in r[5].split(';'):
                    if d:
                        names.setdefault(short(d), set()).add(((path, r[0]), r[6]))
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
                text = f.read()
            for i, line in enumerate(code_lines(text), 1):
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
            for key, check in keys:
                if key in skip:
                    continue
                for p, ln in hits.get(name, []):
                    if check != 'text':
                        # inside any declaration, kept or deleted, the kernel terms tell
                        if inside(decls.get(p, []), ln):
                            continue
                    else:
                        within = [k for s, e, k in spans.get(p, []) if s <= ln <= e]
                        if within and not any(k in skip for k in within):
                            continue
                    skip[key] = f'{p}:{ln}'
                    changed = True
                    break
        if not changed:
            return skip


def read_plan(plan, src):
    rows = collections.defaultdict(list)
    with open(plan, encoding='utf-8') as f:
        for r in csv.DictReader(f, delimiter='\t'):
            path = r['file'] or os.path.join(src, *r['module'].split('.')) + '.lean'
            needs = [int(x) for x in (r.get('needs') or '').split(',') if x]
            rows[path].append((int(r['start_line']), int(r['start_col']), int(r['end_line']),
                               int(r['end_col']), r['module'], r['declarations'],
                               r.get('check') or 'exact', r.get('id') or f'{path}:{r["start_line"]}',
                               needs))
    return rows


def plan_cuts(plan, src):
    """what to delete: (texts {path: lines}, cut {path: set of 0-based line indices},
    deleted [(path, line, module, names)], skipped [(path, line, why, names)])"""
    rows = read_plan(plan, src)
    dr = os.path.join(os.path.dirname(os.path.abspath(plan)), 'decl-ranges.tsv')
    text_skip = text_check(rows, src, read_decl_ranges(dr) if os.path.exists(dr) else None)

    # first, which rows cannot be deleted, and why
    texts, why = {}, {}
    for path, rs in rows.items():
        if not os.path.exists(path):
            for r in rs:
                why[r[7]] = 'file not found'
            continue
        with open(path, encoding='utf-8') as f:
            texts[path] = f.read().split('\n')
        lines = texts[path]
        for sl, sc, el, ec, mod, names, check, rid, needs in rs:
            if (path, sl) in text_skip:
                why[rid] = f'name written in {text_skip[(path, sl)]}'
            # Lean lines are 1-based; columns count code points, as Python strings do
            elif sl < 1 or el > len(lines):
                why[rid] = 'range outside the file'
            elif lines[sl - 1][:sc].strip() or lines[el - 1][ec:].strip():
                why[rid] = 'shares a line with other code'
    # a row that stays keeps every row it mentions
    needs_of = {r[7]: r[8] for rs in rows.values() for r in rs}
    work = list(why)
    while work:
        rid = work.pop()
        for n in needs_of.get(rid, []):
            n = str(n)
            if n not in why:
                why[n] = f'needed by row {rid}, which stays'
                work.append(n)

    deleted, skipped, cuts = [], [], {}
    for path, rs in sorted(rows.items()):
        cut = set()
        for sl, sc, el, ec, mod, names, check, rid, needs in rs:
            if rid in why:
                skipped.append((path, sl, why[rid], names))
                continue
            lines = texts[path]
            span = set(range(sl - 1, el))
            k = sl - 2
            while k >= 0 and IN_PREFIX.match(lines[k]):
                span.add(k)
                k -= 1
            cut |= span
            deleted.append((path, sl, mod, names))
        if cut:
            cuts[path] = cut
    return texts, cuts, deleted, skipped


def collapse_blank(lines):
    """drop one of two blank lines next to each other"""
    out = []
    for l in lines:
        if not l.strip() and out and not out[-1].strip():
            continue
        out.append(l)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('plan')
    ap.add_argument('--src', default='.')
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--out', default='prune-deleted.txt')
    a = ap.parse_args()

    texts, cuts, deleted, skipped = plan_cuts(a.plan, a.src)
    lines_removed = 0
    for path, cut in cuts.items():
        lines = texts[path]
        out = collapse_blank([l for i, l in enumerate(lines) if i not in cut])
        lines_removed += len(lines) - len(out)
        if a.apply:
            with open(path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(out))

    with open(a.out, 'w', encoding='utf-8') as f:
        for path, sl, mod, names in deleted:
            f.write(f'{mod}\t{sl}\t{names}\n')
    verb = 'deleted' if a.apply else 'would delete'
    print(f'{verb} {len(deleted)} declarations ({lines_removed} lines); {len(skipped)} kept; '
          f'list in {a.out}')
    for path, sl, w, names in skipped:
        print(f'kept {path}:{sl} ({w}): {names}', file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
