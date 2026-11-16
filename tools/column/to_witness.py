#!/usr/bin/env python3
"""Print one witness position per shape of a col_shapes.cpp DUMP file, as `MODE CELLS` lines.

Shapes use the col_shapes.cpp string format (runs with exact lengths, `D` for a dead run of
length >= 2, `a`, `b`, ... for the ranks of long live runs; after `|` the capped sorted gaps from
the anchor K). Each long live run gets the smallest realisation of its gaps.

Usage: to_witness.py SHAPES K > witnesses.txt
"""
import sys

file, K = sys.argv[1], int(sys.argv[2])
for line in open(file):
    x = line.strip()
    if not x:
        continue
    mode, s = x[0], x[1:]
    sk, gs = s.split('|')
    lens, cur = [], K
    for c in gs:
        cur += int(c); lens.append(cur)
    p = ''
    for i in range(0, len(sk), 2):
        c, v = sk[i], sk[i + 1]
        n = 2 if v == 'D' else lens[ord(v) - 97] if v >= 'a' else int(v)
        p += c * n
    print(mode, p)
