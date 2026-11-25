#!/usr/bin/env python3
"""Group a fieldlive run's dead fields by structure.

Usage: by-structure.py OUT [CLAIMS] > by-structure.tsv
  OUT     a fieldlive output directory (dead-fields.tsv, field-reach.tsv, constants-info.tsv)
  CLAIMS  optional TSV: structure-name-suffix <TAB> claim text (who / PR). A structure matches a
          line when its full name ends with the suffix at a name-component boundary.

For each structure with dead fields: its module, the dead fields (of how many), and the number of
constants that removing all of them frees (the union over its fields in field-reach.tsv, so shared
constants are counted once). Sorted by constants freed.
"""
import os
import sys


def main():
    out = sys.argv[1]
    claims = []
    if len(sys.argv) > 2:
        for line in open(sys.argv[2]):
            if line.strip() and not line.startswith("#"):
                k, v = line.rstrip("\n").split("\t", 1)
                claims.append((k, v))
    nf, dead = {}, {}
    with open(os.path.join(out, "dead-fields.tsv")) as f:
        next(f)
        for line in f:
            s, fld, _prop, _k, n, _held = line.rstrip("\n").split("\t")
            nf[s] = int(n)
            dead.setdefault(s, []).append(fld)
    freed = {}
    with open(os.path.join(out, "field-reach.tsv")) as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            s = p[0]
            cs = p[3].split(";") if len(p) > 3 and p[3] else []
            freed.setdefault(s, set()).update(cs)
    mod = {}
    want = set(dead)
    ci = os.path.join(out, "constants-info.tsv")
    if os.path.exists(ci):
        with open(ci) as f:
            next(f)
            for line in f:
                c, m = line.split("\t", 2)[:2]
                if c in want:
                    mod[c] = m

    def claim(s):
        return "; ".join(v for k, v in claims if s == k or s.endswith("." + k))

    rows = sorted(dead, key=lambda s: (-len(freed.get(s, ())), s))
    print("structure\tmodule\tdead_fields\tnum_fields\tfreed\tclaimed\tfields")
    for s in rows:
        print(f"{s}\t{mod.get(s, '')}\t{len(dead[s])}\t{nf[s]}\t{len(freed.get(s, ()))}\t{claim(s)}\t{','.join(dead[s])}")


if __name__ == "__main__":
    main()
