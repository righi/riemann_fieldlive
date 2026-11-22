# riemann_fieldlive: hypothesis fields the RH proof never reads

Reachability-based pruning keeps every declaration that a used constructor call mentions.
But many of the proof's hypothesis bundles (structures) have fields that are proved and then
never read by anything downstream. Each such field drags in its whole proof.
`fieldlive` finds them at the kernel level, over the public `lean4export` dump.

**How it decides.** It walks the proof from the root theorems. For a candidate structure
(a project inductive with one constructor, no indices, not recursive), the arguments of a
fully applied constructor are *held back*, one per field, until something reads that field:

- a `proj` on that field;
- the structure's recursor or `casesOn` (counts as reading every field);
- a partially applied or bare constructor (counts as reading every field);
- a later field's type that depends on the field.

Fields still held back at the end are dead. Constants reached only through dead fields drop
out. A baseline run, with every field counted as read, gives the ordinary closure to compare against.

## Files

| File | What it is |
|---|---|
| `fieldlive.cpp` | The analyzer: one C++ file, standard library only. |
| `project-inductives.txt` | The 5,569 inductive types defined in the project, one per line. It limits the analysis to project structures rather than Mathlib's. Derived from `decls.csv` in the rh-proof-dependencies v0.2.1 release. |
| `run-fieldlive.sh` | One-step wrapper: downloads the export (resumable), checks its sha256, builds `fieldlive` and runs it. |
| `prune436.py` | Applies the removals directly to a source tree (see below). The two field edits are hard-coded. |
| `results/v4.33/` | Output of a full run on the Lean v4.33 export (see below). Later runs go in sibling folders. |

## Build and run

One step (downloads the 7.7 GB export into `./export` on first use, results go to `./out`):

```bash
./run-fieldlive.sh [EXPORT_DIR] [OUT_DIR] [ROOT...]
```

Or by hand:

```bash
g++ -O2 -o fieldlive fieldlive.cpp
curl -LO https://math.mit.edu/~drew/grh/solution.ndjson.zst
# sha256 61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381
ulimit -s unlimited
zstd -dc --long=30 solution.ndjson.zst | ./fieldlive project-inductives.txt OUT [ROOT...]
```

The export is streamed, never unpacked to disk. The full run took 4 minutes and 10 GB RAM.
Without ROOT arguments it starts from the five theorems in `Main`: `riemannHypothesis`,
`riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re` and
`LFunction_eq_zero_re_of_isPrimitive`.

## Outputs (`results/v4.33/`)

| File | Columns |
|---|---|
| `dead-fields.tsv` | structure, field, is-Prop, field index, number of fields, constructor sites held back. There are 2,656 dead fields in 898 structures. |
| `dropped-constants.txt` | The 11,840 constants that stop being used when all dead fields go. |
| `field-reach.tsv` | structure, field, count, then the `;`-separated dropped constants reachable from what that field holds back. |
| `field-lines.tsv` | source lines freed, declarations freed, structure, field. Ranked; computed separately from the declaration line spans in `decls.csv`. |

Top entries: `GlobalTheory.FunPr.ThetaLocalInputs.kudlaSplittingSplitUnitary` (13,489 lines),
`GlobalTheory.CovTop.PublishedHodgeBundleTheorems.q8` (9,485 lines; it only becomes dead once
other fields are removed), and `LiteratureCMHypothesis.st` (8,452 lines).

**Caveat:** these numbers come from the Lean v4.33 export, before the v4.36 port (rh#66) and
later trims, so on the current tree they will be smaller. Re-run on a fresh export of that tree.

## Applying removals: `prune436.py`

```bash
python3 prune436.py TREE/src results/v4.33/dropped-constants.txt decl_edges.csv.gz [--apply]
```

`decl_edges.csv.gz` comes from the rh-proof-dependencies release.

1. Deletes the dead fields and their assignments. These are hard-coded for the two
   largest fields; edit `FIELD_EDITS` for others.
2. Finds top-level declarations by tracking namespaces. A declaration is deleted only if its
   exact kernel name is in the dropped set, and the name is defined in only one place.
   Doc comments, attributes and command prefixes ending in ` in` (`variable … in`,
   `open … in`, `set_option … in`) go with the declaration they introduce.
3. Repeats until nothing changes. A declaration is kept if any surviving text in its file, or
   in a file that imports it (directly or transitively; `import`, `public import`, `meta import`
   and `import all` all count), mentions any dotted suffix of its name. Dropped constants that
   can't be found by name (such as anonymous instances) are kept too, together with their
   dropped dependencies.

On the rh#66 tree, the two largest fields free 1,631 declarations (about 22.5k lines in 411 files).
That figure is not final: a build check of this result is still running.
Removing a field can only weaken an assumption, so the worst outcome is a compile error,
never an unsound proof. Still, build the result and check axioms.
