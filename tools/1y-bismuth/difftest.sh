#!/bin/sh
# Compare the Lean model of Bismuth (2019-09-29) with the Python port.
#
# usage: tools/1y-bismuth/difftest.sh [COUNT]
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
TMP=$(mktemp)
python3 "$ROOT/tools/1y-bismuth/gen-difftest.py" "$TMP" "${1:-4000}"
(cd "$ROOT/lean" && lake build >/dev/null && DIFFTEST="$TMP" lake env lean Explore/BismuthDiff.lean)
rm -f "$TMP"
