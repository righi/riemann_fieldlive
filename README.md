# fieldlive: find and delete what a Lean project's main theorems do not need

`fieldlive` loads a built Lean project, walks the kernel terms of everything its root theorems
depend on, and reports what they do not need:

- **unreachable declarations**: project declarations nothing reachable from the roots mentions;
- **dead fields**: fields of the project's structures that are filled in but never read, so that
  each one keeps alive whatever proves it;
- **unused arguments**: explicit `Prop` arguments of theorems that their proofs never use.

For each of them it can write a **prune plan**: the exact source ranges to delete, which
`apply-plan.py` then deletes.

It suits projects built towards a few target theorems (a formalised proof, a blueprint project).
In a library, where every public declaration is the product, "not needed by the roots" means
little; there only the unused-argument mode is of much use.

It was first written for the Riemann Hypothesis proof
(leanprover-community/riemann-hypothesis); the notes, scripts and results from that work are in
[`rh/`](rh/README.md).

## Build

The analyzer has to be built with the same Lean version as the project it analyses: set
`lean/lean-toolchain` to the project's toolchain, then

```bash
cd lean && lake build          # builds lean/.lake/build/bin/fieldlive
```

## Run

From the root of the built project (so `lake env` points Lean at its `.olean` files; a project
whose cache you downloaded with `lake exe cache get` works without a local build):

```bash
ulimit -s unlimited
lake env /path/to/fieldlive/lean/.lake/build/bin/fieldlive [OPTIONS] OUTDIR
```

| Option | Meaning |
|---|---|
| `--mode MODE` | `fields` (default), `args` or `unreachable` |
| `--import MOD` | module to load (repeatable). Default: the root modules, or `Main`. |
| `--root NAME` | a root declaration (repeatable) |
| `--root-module MOD` | every declaration of `MOD` is a root (repeatable) |
| `--roots-file FILE` | root declarations, one per line |
| `--project MOD` | top-level module name of the project (repeatable). By default a module belongs to the project when its `.olean` is neither in the toolchain nor in a Lake dependency (`.lake/packages/`). |
| `--protect MOD` | keep every declaration of `MOD` and of the modules under it, and never edit them; in `args` mode its theorems are not candidates (repeatable) |
| `--only FILE` | only these fields (`Structure<TAB>field`) or arguments (`theorem<TAB>index`) may be dropped |
| `--live-out FILE` | write the live project declarations: a snapshot to compare against after an edit |
| `--before FILE` | such a snapshot: report what an edit freed (see below) |
| `--roots-out FILE` | write each root theorem (the `--root` names and the declarations of the root modules) with a hash of its statement and the axioms it depends on |
| `--no-plan` | do not write `prune-plan.tsv` |
| `--no-import-all` | load only the `--import` modules. By default every module the project has built (`.lake/build/lib/lean`) is loaded too, since code outside the roots' imports still has to compile. |
| `--prune-instances` | let the plan delete unused instances (see below) |
| `--paths` | write `parents.tsv`, a shortest chain of references from a root to every live declaration |
| `--deep` | also walk into library declarations (slower; the project results are the same) |
| `--live-only` | skip the baseline pass; write only the live set |

Without `--root`, `--root-module` or `--roots-file`, the roots are the declarations of the
`--import` modules. The root modules are always protected.

Some declarations are used in ways kernel terms do not show, so they are kept as roots too:

- meta code (syntax, notations, macros, elaborators, unexpanders), and the declarations meta code
  names by literal (the target of a `notation`, for example);
- `implemented_by` targets;
- simp lemmas proved by `rfl` and definitions marked for simp to unfold, since `dsimp` uses them by
  unfolding;
- instances, global, scoped or local. Elaboration can unfold an instance away, so that a proof
  found by it leaves no trace in the term (seen on the RH proof with a local `DecidableEq`
  instance). `--prune-instances` lets the plan delete unused ones anyway, except coercions
  (`Coe`, `CoeFun`, `CoeSort`, …), which coercion insertion always unfolds.

Any other theorem proved by `rfl` can be used by `simp only [h]` or `dsimp only [h]` without a
trace in the proof term. The plan marks such rows `text`, and `apply-plan.py` deletes them only if
their name is written nowhere else in the sources.

Loading the simp sets and instances runs the imported modules' initializers, as building the
project does. Delete only what the plan lists and build afterwards; anything the build then
rejects is a case the analysis missed and should be reported.

## Deleting unreachable declarations

```bash
lake env …/fieldlive --mode unreachable --import Main OUT
python3 apply-plan.py OUT/prune-plan.tsv            # report only
python3 apply-plan.py OUT/prune-plan.tsv --apply    # delete
lake build
```

A plan row is a whole declaration as it is written in the source, from its doc comment to its
last line, together with everything Lean generated from it (equation lemmas, `match_` and
`_proof_` auxiliaries, `where` helpers, structure projections). A row is in the plan only when
the declaration holds something unreachable and nothing reachable, and no declaration that stays
mentions any part of it; the rows held back for that last reason, and what mentions them, are in
`plan-kept.tsv`. If `apply-plan.py` keeps a row (a text-check hit, or a range sharing a line
with other code), it keeps every row that row mentions too (the `needs` column). Run `apply-plan.py` from the project root (or pass `--src`), so the text check
sees all the sources. It also removes the `open … in`-style lines that apply only to a
deleted declaration, and skips (and reports) any range that shares a line with other code.

### In rounds, checked: `clean.py`

```bash
python3 clean.py --fieldlive …/fieldlive [--build CMD] [--wrap CMD] [--commit] -- --import Main --protect Statements
```

builds the project, then repeats: analyse, check the root theorems, delete the plan, build. It
stops when a round deletes nothing. Before each deletion it compares the roots (`--roots-out`)
with round 0: same statements, same axioms. If a build fails or a root changed, it undoes that
round's edits, says why, and stops with status 1. `--commit` commits each round that builds, and
`--wrap` prefixes the analysis and the build (to cap their memory, for example). Options after
`--` go to fieldlive.

## Removing dead fields and unused arguments

A dead field's value is still written at every place the structure is built, so the code it
frees cannot be deleted until the field itself is gone. The flow is:

1. Find them: `lake env …/fieldlive --live-out before.txt OUT` writes `dead-fields.tsv` and
   `field-reach.tsv` (what each field frees). Use `--only` to look at a chosen few.
2. Remove the fields by hand: the field, its value at every construction site, and anything that
   only passed it on. Build.
3. `lake env …/fieldlive --before before.txt OUT2`: now `OUT2/prune-plan.tsv` lists what the edit
   freed, checked against the edited tree. Apply it with `apply-plan.py` and build.

Removing a field or an argument only weakens what is assumed, so the worst outcome is a build
error, never an unsound proof. Unused arguments (`--mode args`, output `unused-args.tsv`) go the
same way.

## Outputs

| File | What it is |
|---|---|
| `prune-plan.tsv` | id, file, module, start line and column, end line and column, declarations, check (`exact`, or `text` for theorems proved by `rfl`), needs (ids of the rows it mentions): the ranges to delete |
| `unused-modules.txt` | (unreachable mode) project modules that declare something but nothing live: candidates for deleting the whole file |
| `plan-kept.tsv` | declarations left out of the plan, and the declaration that stays and mentions them |
| `dead-fields.tsv` | structure, field, is-Prop, field index, number of fields, construction sites held back |
| `field-reach.tsv` | structure, field, count, then the declarations only that field keeps alive |
| `unused-args.tsv` | theorem, argument index and name, type, call sites held back, declarations freed |
| `dropped-constants.txt`, `dead-edges.csv` | the dropped kernel constants and the references among them (input for the older, text-based `prune.py`) |
| `live-constants.txt`, `constants-info.tsv` | the live set; every project constant with its module, kind and liveness |

## Tests

```bash
cd lean && lake build && cd .. && tests/run.sh
```

runs both flows on the small project in `tests/fixture` and checks the plans and that the pruned
tree still builds.

## Other tools

`prune.py` is the earlier, text-based version of `apply-plan.py`: it takes
`dropped-constants.txt` and guesses declarations from the source text. `by-structure.py` groups
a run's dead fields by structure. For unused imports use Mathlib's `shake`; for unused arguments
of library declarations, Batteries' `#lint`.
