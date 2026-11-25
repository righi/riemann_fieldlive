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
| `prune.py` | Deletes the declarations a run found unreachable, after you have made the structural edits yourself (see below). |
| `prune436.py` | The earlier version used for the first #431, with its two field edits hard-coded. Kept for the record. |
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

## Applying removals: `prune.py`

For one PR:

1. Run the Lean version (below) with `FIELDLIVE_ONLY` set to just the fields you are removing.
2. Make the structural edits by hand: delete the fields, their assignments at every construction
   site, and any signature that passed them on.
3. Run `prune.py` on the edited tree:

```bash
python3 prune.py src OUT/dropped-constants.txt OUT/dead-edges.csv [--apply] [--out deleted.txt]
```

Without `--apply` it only reports. The list of deleted declarations goes to `--out`
(default `prune-deleted.txt`), ready for the PR description.

How it decides:

1. Finds top-level declarations by tracking namespaces. A declaration is deleted only if its
   exact kernel name is in the dropped set, and the name is defined in only one place.
   Doc comments, attributes and command prefixes ending in ` in` (`variable … in`,
   `open … in`, `set_option … in`) go with the declaration they introduce.
2. Repeats until nothing changes. A declaration is kept if any surviving text in its file, or
   in a file that imports it (directly or transitively; `import`, `public import`, `meta import`
   and `import all` all count), mentions any dotted suffix of its name. Dropped constants that
   can't be found by name (such as anonymous instances) are kept too, together with their
   dropped dependencies.

Code that is already unreachable from `Main` is still compiled, so always build the result.
On current main this produced #431 (457 declarations) and #1783 (43 declarations), both merged.

Earlier, with `prune436.py` on the rh#66 tree (Lean v4.36), the two largest fields free 1,631 declarations (about 22.5k lines
in 411 files). The pruned tree builds with no errors (all 149,395 modules; 69,429 rebuilt), `Main.lean`
and `Challenge.lean` are unchanged, and the five `Main` theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`. The same holds after rebasing onto upstream main at `fb085fff5bf`.
Removing a field can only weaken an assumption, so the worst outcome is a compile error,
never an unsound proof. Still, build the result and check axioms.

## In-process version (`lean/`), no export needed

`lean4export` on the v4.37 tree needs more than 90 GB and did not finish. `lean/Fieldlive.lean` is a port
of `fieldlive.cpp` that runs on the built project directly: it imports `Main` (the `.olean` files are
memory-mapped) and walks the kernel terms in place. Same rules, same output files.

```bash
cd lean && lake build                      # toolchain must match the project's
cd /path/to/riemann-hypothesis             # built tree (or oleans from the CI cache)
ulimit -s unlimited
lake env /path/to/lean/.lake/build/bin/fieldlive OUTDIR /path/to/lean/project-roots.txt [ROOT...]
```

`project-roots.txt` lists the project's top-level module names; a structure is a candidate if it is
defined under one of them (this replaces `project-inductives.txt`). On cc10d0dd2 it took 45 minutes
and peaked at about 35 GB of working memory (RSS reads higher because it counts the mapped oleans).
Small subterms (depth ≤ 4) are not memoised, so the `constructor_sites_held` column can count a site
more than once; dead fields and dropped constants are unaffected.

It also writes `dead-edges.csv` (`src,,dst`: kernel references between dropped constants), and,
like `fieldlive.cpp`, honours `FIELDLIVE_ONLY=FILE` (lines `Structure<TAB>field`) so that only
those fields may drop, which gives the exact removal set for one PR.

No local build is needed: clone the project, run `lake exe cache get` (about 20 minutes, 82 GB),
then run the command above in that tree.

Results: `results/v4.37-cc10d0d/` (#431's old head) and `results/v4.37-94779230/` (main on
2026-11-24, from the CI cache: 2,670 dead fields in 896 structures, 5,942 constants dropped).
On cc10d0dd2 it reports every field removed for being unread in the merged #151 PRs (#458, #459,
#474, #478, #489's `DivT.loc`, #490), and the same 28 dead `DivX` fields as the v4.33 run.
