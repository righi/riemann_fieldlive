# fieldlive on the Riemann Hypothesis proof

These are the notes, scripts and results from using fieldlive on
leanprover-community/riemann-hypothesis, kept as they were when the tool was RH-specific. The
general tool and its options are described in the top-level README; in the commands below,
`project-inductives.txt`, `run-fieldlive.sh`, `fieldlive.cpp` and the claims scripts now live in
this `rh/` folder. With the new command line, the RH run is

```bash
lake env /path/to/lean/.lake/build/bin/fieldlive --import Main --protect Statements --protect Challenge OUT
```


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
| `by-structure.py` | Groups a run's dead fields by structure, with constants freed per structure and optional claim notes (`claims-151.tsv`). |
| `claims-151.tsv` | Who has claimed which structure on rh#151 or in an open PR, as a snapshot (2026-11-25). |
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

The walk does not go into constants from Lean, Std, Batteries or Mathlib: libraries cannot import the
project, so nothing in them can read a project field. The outputs list project constants only.
On main a18a350c3e this gave the same results as the full walk (`FIELDLIVE_DEEP=1` restores it), and was
about 6% faster. Each pass logs its time.

**When an edit changes signatures,** not just fields (an argument or hypothesis is dropped), the code it frees
is not visible as a dead field. Compare reachability before and after instead:

```bash
FIELDLIVE_LIVE_OUT=live-before.txt lake env …/fieldlive OUT-before roots.txt   # on the tree before the edit
# make the edits, build
FIELDLIVE_BEFORE=live-before.txt lake env …/fieldlive OUT-after roots.txt      # on the edited, built tree
```

The snapshot is the baseline set (every field counted as read), so the second run's
`dropped-constants.txt` and `dead-edges.csv` list everything the change frees: what the removed fields
held and what the signature changes cut off. They are ready for `prune.py` on their own. Use the same
`FIELDLIVE_ONLY` in both runs if you set one. #3624 (`GeoLaws` and `GeoTie.ThetaTie`) was made this way,
with an earlier version that snapshotted the field-mode set; there the first run's dropped list was
added to the second's to get the same result.

No local build is needed: clone the project, run `lake exe cache get` (about 20 minutes, 82 GB),
then run the command above in that tree.

Results: `results/v4.37-cc10d0d/` (#431's old head) and `results/v4.37-94779230/` (main on
2026-11-24, from the CI cache: 2,670 dead fields in 896 structures, 5,942 constants dropped).
On cc10d0dd2 it reports every field removed for being unread in the merged #151 PRs (#458, #459,
#474, #478, #489's `DivT.loc`, #490), and the same 28 dead `DivX` fields as the v4.33 run.
`results/v4.37-fcb6eac753/` is main on 2026-11-25 (after batch 12): 2,449 dead fields in 862 structures,
4,063 constants dropped. It adds `by-structure.tsv` (`python3 by-structure.py OUT claims-151.tsv`).

### Other options (environment variables)

- `FIELDLIVE_PATHS=1`: also write `parents.tsv` (`constant, depth, parent`), a shortest-path tree of
  references from the roots in the field-mode walk, so you can see why a constant is still live.
  The run also writes `live-constants.txt` and `constants-info.tsv` (every project constant with its
  module, kind, whether its type ends in `Prop`, and whether it is live in the baseline and in field mode).
- `FIELDLIVE_LIVE_ONLY=1`: skip the baseline; write only the field-mode live set (and the tree).
- `FIELDLIVE_MODULE=M`: import `M` instead of `Main` (for testing on a small module).
- `FIELDLIVE_MODE=args` (experimental): unused theorem arguments instead of dead fields. Candidates are
  explicit, Prop-typed arguments of reachable project theorems (not in `Main`, `Statements` or
  `Challenge`) whose variable occurs neither in the proof nor in a later binder type nor the statement.
  The walk holds back such an argument at every full call; a bare or partial use of the theorem counts
  as using all its arguments. Fields all count as read. Writes `unused-args.tsv` (theorem, argument
  index and name, type, call sites held, constants freed and their list) plus `dropped-constants.txt`
  and `dead-edges.csv` for `prune.py`. `FIELDLIVE_ONLY` then takes `theorem<TAB>argument_index` lines.
