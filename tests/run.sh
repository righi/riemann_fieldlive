#!/bin/bash
# End-to-end test on tests/fixture: unreachable mode, the prune plan and apply-plan.py, and the
# dead-field flow (snapshot, edit, --before). Needs the fieldlive binary: cd lean && lake build.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="$HERE/../lean/.lake/build/bin/fieldlive"
APPLY="$HERE/../apply-plan.py"
FIX="$HERE/fixture"
TMP="$(mktemp -d)"
trap 'cp "$TMP/Basic.lean" "$FIX/Fix/Basic.lean" 2>/dev/null || true; rm -rf "$TMP"' EXIT
ulimit -s unlimited 2>/dev/null || true
cd "$FIX"
cp Fix/Basic.lean "$TMP/Basic.lean"
lake build -q
fl() { lake env "$BIN" --import Fix --root fix_root --protect Fix.Keep "$@" 2>/dev/null; }
fail=0
expect() {  # expect NAME EXPECTED ACTUAL
  if [ "$2" == "$3" ]; then echo "ok   $1"; else echo "FAIL $1"; echo "  expected: $2"; echo "  actual:   $3"; fail=1; fi
}
decls() { tail -n +2 "$1" | cut -f7 | tr ';' '\n' | grep -v "^$" | LC_ALL=C sort | tr '\n' ' '; }

# 1. unreachable mode
fl --mode unreachable "$TMP/u" >/dev/null
expect "unreachable: plan" \
  "$(printf "%s\n" Fix.instUnused Fix.unusedDef_spec Fix.unusedRec Fix.unusedRec.go Fix.unused_open Fix.uses_mentioned "private Fix.private_unused" | LC_ALL=C sort | tr "\n" " ")" \
  "$(decls "$TMP/u/prune-plan.tsv")"
python3 "$APPLY" "$TMP/u/prune-plan.tsv" --apply --out "$TMP/del.txt" >/dev/null
expect "unreachable: open … in prefix removed" "0" "$(grep -c '^open Nat in' Fix/Basic.lean || true)"
expect "unreachable: notation and its target kept" "2" "$(grep -c 'unusedDef' Fix/Basic.lean)"
expect "unreachable: pruned tree builds" "0" "$(lake build -q >/dev/null 2>&1; echo $?)"
cp "$TMP/Basic.lean" Fix/Basic.lean

# 2. dead fields, then the edit, then --before
fl --live-out "$TMP/before.txt" "$TMP/f1" >/dev/null
expect "fields: dead field" "Fix.Facts big" "$(tail -n +2 "$TMP/f1/dead-fields.tsv" | cut -f1,2 | tr '\t' ' ')"
sed -i '/^  big : n ≠ 1000$/d; s/⟨by decide, helper_for_big⟩/⟨by decide⟩/' Fix/Basic.lean
lake build -q
fl --before "$TMP/before.txt" "$TMP/f2" >/dev/null
expect "fields --before: plan" "Fix.helper_for_big " "$(decls "$TMP/f2/prune-plan.tsv")"
python3 "$APPLY" "$TMP/f2/prune-plan.tsv" --apply --out "$TMP/del.txt" >/dev/null
expect "fields --before: pruned tree builds" "0" "$(lake build -q >/dev/null 2>&1; echo $?)"
exit $fail
