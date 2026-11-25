#!/bin/sh
# Compare the Lean model of Bismuth (2020-07-15) with the Python port.
#
# usage: tools/1y-bismuth-2020-07-15/difftest.sh [COUNT]
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
TMP=$(mktemp)
python3 "$ROOT/tools/1y-bismuth-2020-07-15/gen-difftest.py" "$TMP" "${1:-4000}"
(cd "$ROOT/lean" && lake build >/dev/null && DIFFTEST="$TMP" lake env lean Explore/Bismuth2020Diff.lean)
rm -f "$TMP"
