#!/usr/bin/env python3
"""Generate test cases for lean/Explore/BismuthDiff.lean with the Python port.

usage: gen-difftest.py OUT [COUNT]

Visits COUNT (default 4000) sequences reachable from (1,2), ..., (1,5) by
expansions with brackets 1, 2, 3 (shortest first, length <= 10) and writes, for
each of them and each bracket 1, 2, 3, the line
    "<sequence> <bracket> <output sequence> <output bracket>"
or "<sequence> <bracket> LOOP" when copyOffset loops forever.
"""
import heapq
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bismuth as B  # noqa: E402

sys.setrecursionlimit(10000)
out = sys.argv[1]
count = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
start = [(1, m) for m in range(2, 6)]
seen = set(start)
heap = [(len(s), s) for s in start]
heapq.heapify(heap)
order = []
while heap and len(order) < count:
    _, s = heapq.heappop(heap)
    order.append(s)
    for b in (1, 2, 3):
        try:
            o, _ = B.run(list(s), b, 1, budget=3_000_000)
        except Exception:
            continue
        t = tuple(o)
        if 0 < len(t) <= 10 and t not in seen:
            seen.add(t)
            heapq.heappush(heap, (len(t), t))
with open(out, "w") as f:
    for s in order:
        for b in (1, 2, 3):
            try:
                o, nb = B.run(list(s), b, 1, budget=3_000_000)
                r = ",".join(map(str, o)) + f" {nb}"
            except B.InfiniteLoop:
                r = "LOOP"
            except B.Hang:
                r = "BUDGET"
            except Exception:
                r = "ERR"
            f.write(f"{','.join(map(str, s))} {b} {r}\n")
print(f"{len(order) * 3} cases written to {out}")
