#!/bin/sh
# Cross-check the expansions of this project with yaBMS.
#
# usage: tools/crosscheck.sh BMS
#   BMS: the yaBMS binary, built from https://github.com/koteitan/yaBMS (c/bms)
#
# 1. lean/Explore/States.lean prints the matrices on the standardness paths and
#    on the loops of BM1.1 and BM2.
# 2. tools/gen-yabms-test.py expands each of them with yaBMS and writes
#    lean/Test/YaBMS.lean.
# 3. Building lean/Test/YaBMS.lean checks that the expansions agree.
set -eu
BMS=$1
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TMP=$(mktemp)
(cd "$ROOT/lean" && lake build >/dev/null && lake env lean Explore/States.lean) | grep -E '^(1\.1|2) ' > "$TMP"
python3 "$ROOT/tools/gen-yabms-test.py" "$BMS" "$TMP" "$ROOT/lean/Test/YaBMS.lean"
rm -f "$TMP"
(cd "$ROOT/lean" && lake build Test.YaBMS)
