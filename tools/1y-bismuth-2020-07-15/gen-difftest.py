#!/usr/bin/env python3
"""Generate test cases for lean/Explore/Bismuth2020Diff.lean with the Python port.

usage: gen-difftest.py OUT [COUNT]

Visits COUNT (default 4000) sequences reachable from (1,2), ..., (1,5) by
expansions with brackets 0, 1, 2, 3 (shortest first, length <= 10) and writes, for
each of them and each bracket 0, 1, 2, 3, the line
    "<sequence> <bracket> <output sequence> <output bracket>"
or "<sequence> <bracket> LOOP" when copyOffset loops forever,
or "<sequence> <bracket> ERR" when the Kotlin program would throw.
It also writes the brackets 0, ..., 5 of the 59 sequences of the path from (1,5)
to (1,4,12,9,12,20) (lean/1y-bismuth-2020-07-15/Standard.lean), of
(1,2,4,7,5,4,5,10) and of (1,4,12,11,14,22).
"""
import heapq
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bismuth as B  # noqa: E402

sys.setrecursionlimit(20000)
out = sys.argv[1]
count = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
brackets = (0, 1, 2, 3)
start = [(1, m) for m in range(2, 6)]
seen = set(start)
heap = [(len(s), s) for s in start]
heapq.heapify(heap)
order = []
while heap and len(order) < count:
    _, s = heapq.heappop(heap)
    order.append(s)
    for b in brackets:
        try:
            o, _ = B.run(list(s), b, budget=3_000_000)
        except Exception:
            continue
        t = tuple(o)
        if 0 < len(t) <= 10 and t not in seen:
            seen.add(t)
            heapq.heappush(heap, (len(t), t))
path = ([[1, 5], [1, 4, 16], [1, 4, 15], [1, 4, 14], [1, 4, 13], [1, 4, 12, 32]]
        + [[1, 4, 12, k] for k in range(31, 15, -1)]
        + [[1, 4, 12, 15, k] for k in (23, 22, 21, 20, 19)] + [[1, 4, 12, 15]]
        + [[1, 4, 12, k] for k in (14, 13, 12, 11, 10)]
        + [[1, 4, 12, 9, 21, 55, k] for k in (49, 48, 47, 46)] + [[1, 4, 12, 9, 21, 55]]
        + [[1, 4, 12, 9, 21, k] for k in range(54, 45, -1)] + [[1, 4, 12, 9, 21]]
        + [[1, 4, 12, 9, k] for k in range(20, 12, -1)]
        + [[1, 4, 12, 9, 12, 20, 17], [1, 4, 12, 9, 12, 20, 16], [1, 4, 12, 9, 12, 20]])
extra = path + [[1, 2, 4, 7, 5, 4, 5, 10], [1, 4, 12, 11, 14, 22]]
cases = [(s, b) for s in order for b in brackets] + [(tuple(s), b) for s in extra for b in range(6)]
with open(out, "w") as f:
    for s, b in cases:
        try:
            o, nb = B.run(list(s), b, budget=3_000_000)
            r = ",".join(map(str, o)) + f" {nb}"
        except B.InfiniteLoop:
            r = "LOOP"
        except B.Hang:
            r = "BUDGET"
        except Exception:
            r = "ERR"
        f.write(f"{','.join(map(str, s))} {b} {r}\n")
print(f"{len(cases)} cases written to {out}")
