#!/bin/bash
# Download the lean4export dump (if needed), verify it, build fieldlive (if needed), and run it.
#
# Usage: ./run-fieldlive.sh [EXPORT_DIR] [OUT_DIR] [ROOT...]
#   EXPORT_DIR  where solution.ndjson.zst is (or will be downloaded to)   default: ./export
#   OUT_DIR     where the results are written                              default: ./out
#   ROOT...     root theorems (default: the five theorems in Main)
#
# Needs: curl, zstd, sha256sum, g++. The run streams the 7.7 GB dump and uses about 10 GB RAM.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
EXPORT_DIR="$(mkdir -p "${1:-export}" && cd "${1:-export}" && pwd)"
OUT_DIR="${2:-out}"
shift $(( $# < 2 ? $# : 2 ))

URL=https://math.mit.edu/~drew/grh/solution.ndjson.zst
SIZE=7699933588
SHA=61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381
DUMP="$EXPORT_DIR/solution.ndjson.zst"

# 1. download (resumable)
for i in 1 2 3 4 5; do
  have=$(stat -c %s "$DUMP" 2>/dev/null || echo 0)
  [ "$have" -ge "$SIZE" ] && break
  echo "== downloading ($have of $SIZE bytes), attempt $i"
  curl -sSL -C - -o "$DUMP" "$URL" || sleep 30
done
[ "$(stat -c %s "$DUMP" 2>/dev/null || echo 0)" -ge "$SIZE" ] || { echo "download incomplete" >&2; exit 1; }

# 2. verify
echo "== checking sha256"
echo "$SHA  $DUMP" | sha256sum -c --quiet - || { echo "sha256 mismatch: $DUMP" >&2; exit 1; }

# 3. build
if [ ! -x "$HERE/fieldlive" ] || [ "$HERE/fieldlive.cpp" -nt "$HERE/fieldlive" ]; then
  echo "== building fieldlive"
  g++ -O2 -o "$HERE/fieldlive" "$HERE/fieldlive.cpp"
fi

# 4. run
mkdir -p "$OUT_DIR"
ulimit -s unlimited 2>/dev/null || echo "warning: could not raise the stack limit" >&2
echo "== running fieldlive -> $OUT_DIR"
zstd -dc --long=30 "$DUMP" | "$HERE/fieldlive" "$HERE/project-inductives.txt" "$OUT_DIR" "$@"
echo "== done: $OUT_DIR"
