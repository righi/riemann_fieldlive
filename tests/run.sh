#!/bin/bash
# End-to-end test on tests/fixture: unreachable mode, the prune plan and apply-plan.py, and the
# dead-field flow (snapshot, edit, --before). Needs the fieldlive binary: cd lean && lake build.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="$HERE/../lean/.lake/build/bin/fieldlive"
APPLY="$HERE/../apply-plan.py"
FIX="$HERE/fixture"
TMP="$(mktemp -d)"
trap 'rm -rf "$FIX/Fix" && cp -r "$TMP/Fix" "$FIX/Fix"; rm -rf "$TMP"' EXIT
ulimit -s unlimited 2>/dev/null || true
cd "$FIX"
cp -r Fix "$TMP/Fix"
lake build -q
fl() { lake env "$BIN" --import Fix --root fix_root --protect Fix.Keep --protect Fix.Orphan "$@" 2>/dev/null; }
fail=0
expect() {  # expect NAME EXPECTED ACTUAL
  if [ "$2" == "$3" ]; then echo "ok   $1"; else echo "FAIL $1"; echo "  expected: $2"; echo "  actual:   $3"; fail=1; fi
}
decls() { tail -n +2 "$1" | cut -f8 | tr ';' '\n' | grep -v "^$" | LC_ALL=C sort | tr '\n' ' '; }

# 1. unreachable mode
fl --mode unreachable "$TMP/u" >/dev/null
expect "unreachable: plan" \
  "$(printf "%s\n" Fix.onlyForSimp Fix.onlyForSimp_def Fix.twice_def Fix.unusedDef_spec Fix.unusedRec Fix.unusedRec.go Fix.unused_open Fix.uses_mentioned "private Fix.private_unused" lonely | LC_ALL=C sort | tr "\n" " ")" \
  "$(decls "$TMP/u/prune-plan.tsv")"
expect "unreachable: unused modules" "Fix.Unused" "$(cat "$TMP/u/unused-modules.txt")"
fl --mode unreachable --no-import-all "$TMP/un" >/dev/null
expect "unreachable: use in an unimported module seen only with import-all" "1 0" \
  "$(cut -f8 "$TMP/un/prune-plan.tsv" | grep -c '^Fix.orphanNeeds$') $(cut -f8 "$TMP/u/prune-plan.tsv" | grep -c '^Fix.orphanNeeds$')"
fl --mode unreachable --prune-instances "$TMP/ui" >/dev/null
expect "unreachable --prune-instances: instance in plan" "1" "$(cut -f8 "$TMP/ui/prune-plan.tsv" | grep -c '^Fix.instUnused$')"
python3 "$APPLY" "$TMP/u/prune-plan.tsv" --apply --out "$TMP/del.txt" >/dev/null 2>&1
expect "unreachable: what a kept row needs is kept" "1" "$(grep -c '^def onlyForSimp' Fix/Basic.lean)"
expect "unreachable: rfl theorem used by simp only kept" "1" "$(grep -c '^theorem twice_def' Fix/Basic.lean)"
expect "unreachable: open … in prefix removed" "0" "$(grep -c '^open Nat in' Fix/Basic.lean || true)"
expect "unreachable: notation and its target kept" "1" "$(grep -c '^scoped notation' Fix/Basic.lean)"
expect "unreachable: rfl simp lemma, coercion and DecidableEq instance kept" "3" "$(grep -cE '^(@\[simp\] theorem unusedDef_zero|instance instCoeBoolNat|local instance instDecEqUnit)' Fix/Basic.lean)"
expect "unreachable: pruned tree builds" "0" "$(lake build -q >/dev/null 2>&1; echo $?)"
rm -rf Fix && cp -r "$TMP/Fix" Fix

# 2. dead fields, then the edit, then --before
fl --live-out "$TMP/before.txt" "$TMP/f1" >/dev/null
expect "fields: dead field" "Fix.Facts big" "$(tail -n +2 "$TMP/f1/dead-fields.tsv" | cut -f1,2 | tr '\t' ' ')"
sed -i '/^  big : n ≠ 1000$/d; s/⟨by decide, helper_for_big⟩/⟨by decide⟩/' Fix/Basic.lean
lake build -q
fl --before "$TMP/before.txt" "$TMP/f2" >/dev/null
expect "fields --before: plan" "Fix.helper_for_big " "$(decls "$TMP/f2/prune-plan.tsv")"
python3 "$APPLY" "$TMP/f2/prune-plan.tsv" --apply --out "$TMP/del.txt" >/dev/null 2>&1
expect "fields --before: pruned tree builds" "0" "$(lake build -q >/dev/null 2>&1; echo $?)"
rm -rf Fix && cp -r "$TMP/Fix" Fix

# 3. clean.py: rounds of delete and build until nothing is left, roots checked each round
lake build -q
python3 "$HERE/../clean.py" --fieldlive "$BIN" --work "$TMP/c" -- --import Fix --root fix_root \
  --protect Fix.Keep --protect Fix.Orphan >"$TMP/clean.log" 2>&1 && rc=0 || rc=$?
expect "clean: finishes" "0 1" "$rc $(grep -c '^done: nothing more to delete after 1 rounds; 6 declarations' "$TMP/clean.log")"
expect "clean: tree builds" "0" "$(lake build -q >/dev/null 2>&1; echo $?)"
rm -rf Fix && cp -r "$TMP/Fix" Fix
# --roots-out sees a changed statement and changed axioms
sed -i 's/^theorem fix_root : 0 < (5 : Nat) ∧ Fix.twice 2 = 4 := ⟨Fix.five_pos, by simp only \[Fix.twice_def\]⟩$/theorem fix_root : 0 < (5 : Nat) ∧ Fix.twice 2 = 4 ∧ (True ∨ ¬True) := ⟨Fix.five_pos, by simp only [Fix.twice_def], Classical.em True⟩/' Fix/Main.lean
lake build -q
fl --mode unreachable --no-plan --roots-out "$TMP/roots2.tsv" "$TMP/r2" >/dev/null
expect "roots-out: statement and axioms" "different Classical.choice,Quot.sound,propext" \
  "$([ "$(cut -f2 "$TMP/c/round0/roots.tsv")" != "$(cut -f2 "$TMP/roots2.tsv")" ] && echo different) $(cut -f3 "$TMP/roots2.tsv")"
exit $fail
