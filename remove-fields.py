#!/usr/bin/env python3
"""Remove dead structure fields, and the declarations only they kept alive, in one edit.

    python3 remove-fields.py OUTDIR [--src DIR] [--apply] [--blocked FILE]

OUTDIR holds the output of `fieldlive` (fields mode, without --before) and of `fieldedit`:
  field-plan.tsv    the declarations to delete once the fields are gone
  field-edits.tsv   the source edits that remove the fields (fieldedit OUTDIR/field-sites.tsv ...)
  dead-fields.tsv   the dead fields

Edits inside a declaration the plan deletes are dropped, since that code goes anyway. A field is
blocked when the projection is read (`reader`), or the constructor is used in a way fieldedit
cannot edit (`unknown`), outside the code the plan deletes. Blocked fields are listed in --blocked
(default OUTDIR/blocked-fields.tsv) and nothing is changed: the plan was computed for removing
every dead field, so run fieldlive again with `--only` set to the fields not blocked (the list in
OUTDIR/removable-fields.tsv), then fieldedit and this script. Exit status: 0 done (or nothing to
do), 3 some fields blocked.

Build afterwards. Some uses leave no trace this tool sees: `refine ⟨?_, ?_⟩` followed by one
tactic block per field, the `constructor` tactic, or a field filled by `by exact …` elsewhere.
"""
import argparse
import collections
import csv
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('apply_plan', os.path.join(HERE, 'apply-plan.py'))
apply_plan = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(apply_plan)


def offsets(lines):
    """start offset of each line in '\\n'.join(lines)"""
    out, o = [], 0
    for l in lines:
        out.append(o)
        o += len(l) + 1
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('outdir')
    ap.add_argument('--src', default='.')
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--blocked')
    a = ap.parse_args()
    blocked_file = a.blocked or os.path.join(a.outdir, 'blocked-fields.tsv')

    texts, cuts, deleted, skipped = apply_plan.plan_cuts(os.path.join(a.outdir, 'field-plan.tsv'), a.src)
    edits = collections.defaultdict(list)  # path -> [(sl, sc, el, ec, kind, proj, detail)]
    with open(os.path.join(a.outdir, 'field-edits.tsv'), encoding='utf-8') as f:
        for r in csv.DictReader(f, delimiter='\t'):
            edits[r['file']].append((int(r['start_line']), int(r['start_col']), int(r['end_line']),
                                     int(r['end_col']), r['kind'], r['projection'], r['detail']))
    fields = {}
    with open(os.path.join(a.outdir, 'dead-fields.tsv'), encoding='utf-8') as f:
        for r in csv.DictReader(f, delimiter='\t'):
            fields[f"{r['structure']}.{r['field']}"] = (r['structure'], r['field'])

    def in_cut(path, line):
        return line - 1 in cuts.get(path, ())

    # which fields cannot go yet
    blocked = collections.defaultdict(list)
    has_decl = set()
    for path, es in edits.items():
        for sl, sc, el, ec, kind, proj, detail in es:
            if kind == 'decl':
                has_decl.add(proj)
            if kind in ('reader', 'unknown') and not (sl > 0 and in_cut(path, sl) and in_cut(path, el)):
                blocked[proj].append(f'{kind} {path}:{sl}:{sc} {detail}'.rstrip())
    for proj in fields:
        if proj not in has_decl and proj not in blocked:
            blocked[proj].append('field declaration not found')
    if blocked:
        with open(blocked_file, 'w', encoding='utf-8') as f:
            for proj, why in sorted(blocked.items()):
                for w in why:
                    f.write(f'{proj}\t{w}\n')
        with open(os.path.join(a.outdir, 'removable-fields.tsv'), 'w', encoding='utf-8') as f:
            for proj, (s, fld) in sorted(fields.items()):
                if proj not in blocked:
                    f.write(f'{s}\t{fld}\n')
        n = len(fields) - len(blocked)
        print(f'{len(blocked)} of {len(fields)} dead fields blocked (see {blocked_file}); '
              f'{n} removable, listed in {a.outdir}/removable-fields.tsv')
        return 3
    if not fields:
        print('no dead fields')
        return 0

    # everything to delete, as character ranges of the original text
    changed = 0
    for path in sorted(set(edits) | set(cuts)):
        if path not in texts:
            with open(path, encoding='utf-8') as f:
                texts[path] = f.read().split('\n')
        lines = texts[path]
        off = offsets(lines)
        text = '\n'.join(lines)
        cut = cuts.get(path, set())
        rs = []
        for i in cut:
            rs.append((off[i], off[i] + len(lines[i]) + 1))
        touched = []  # offsets where a field edit joined text: the line there may now be empty
        for sl, sc, el, ec, kind, proj, detail in edits.get(path, []):
            if kind not in ('decl', 'value', 'arg') or (in_cut(path, sl) or in_cut(path, el)):
                continue
            rs.append((off[sl - 1] + sc, off[el - 1] + ec))
            touched.append(off[sl - 1] + sc)
        if not rs:
            continue
        rs.sort()
        merged = []
        for s, e in rs:
            if merged and s <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(merged[-1][1], e))
            else:
                merged.append((s, e))
        out, last, marks = [], 0, set()
        for s, e in merged:
            out.append(text[last:s])
            last = e
        out.append(text[last:])
        # map the touched offsets into the new text, to find lines left empty
        pos = 0
        newpos = {}
        for (s, e), piece in zip(merged + [(len(text), len(text))], out):
            pos += len(piece)
            newpos[s] = pos
        for t in touched:
            for s, e in merged:
                if s <= t <= e:
                    marks.add(newpos[s])
                    break
        new = ''.join(out)
        nl = new.split('\n')
        noff = offsets(nl)
        drop = set()
        for m in marks:
            # the line holding the join point
            i = max(j for j, o in enumerate(noff) if o <= m)
            if not nl[i].strip():
                drop.add(i)
        nl = apply_plan.collapse_blank([l for j, l in enumerate(nl) if j not in drop])
        changed += 1
        if a.apply:
            with open(path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(nl))
    verb = 'removed' if a.apply else 'would remove'
    print(f'{verb} {len(fields)} fields and {len(deleted)} declarations in {changed} files; '
          f'{len(skipped)} plan rows kept')
    for path, sl, w, names in skipped:
        print(f'kept {path}:{sl} ({w}): {names}', file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
