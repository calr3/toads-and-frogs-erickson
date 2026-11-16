#!/usr/bin/env python3
"""Independent check of a closed set of run shapes (the DUMP output of col_shapes.cpp).

Re-implements, separately from the C++ search: moves, maximal runs, dead regions, the shape (class)
of a position and the witnesses of a shape. Then checks exactly what a kernel check would:

* every witness w of a U shape: Left's pass and every Left move q from w can be answered, by
  Right's pass (shape(q) is an N shape) or a reply r with shape(r) a U shape;
* every witness w of an N shape: every Left move q from w has a reply r with shape(r) an N shape;
* the start T^a .^B F^a has a U shape for every a from AMIN to AMAX (beyond a = K + M + 4 the
  shape only depends on the parity of a).

Usage: verify_shapes.py SHAPES B K M [AMIN AMAX]
"""
import sys

def lm(s):
    out = []
    for i, c in enumerate(s):
        if c == 'T':
            if i + 1 < len(s) and s[i + 1] == '.': out.append(s[:i] + '.T' + s[i + 2:])
            elif i + 2 < len(s) and s[i + 1] == 'F' and s[i + 2] == '.': out.append(s[:i] + '.FT' + s[i + 3:])
    return out

def rm(s):
    out = []
    for i, c in enumerate(s):
        if c == 'F':
            if i >= 1 and s[i - 1] == '.': out.append(s[:i - 1] + 'F.' + s[i + 1:])
            elif i >= 2 and s[i - 1] == 'T' and s[i - 2] == '.': out.append(s[:i - 2] + 'FT.' + s[i + 1:])
    return out

def runs(s):
    r = []
    for c in s:
        if r and r[-1][0] == c: r[-1][1] += 1
        else: r.append([c, 1])
    return r

def dead(rs):
    """Runs in a dead region: in a block without empty squares, from the first TT to the last FF."""
    d = [False] * len(rs)
    i = 0
    while i < len(rs):
        if rs[i][0] == '.': i += 1; continue
        j = i
        while j < len(rs) and rs[j][0] != '.': j += 1
        st = next((k for k in range(i, j) if rs[k][0] == 'T' and rs[k][1] >= 2), None)
        en = None if st is None else next((k for k in range(j - 1, st, -1) if rs[k][0] == 'F' and rs[k][1] >= 2), None)
        if st is not None and en is not None:
            for k in range(st, en + 1): d[k] = True
        i = j
    return d

def shape(p):
    rs = runs(p); d = dead(rs)
    lv = sorted((l, i) for i, (c, l) in enumerate(rs) if l >= K and not d[i])   # stable: ties by index
    rank = {i: k for k, (l, i) in enumerate(lv)}
    sk = ''
    for i, (c, l) in enumerate(rs):
        if d[i]:
            if i == 0 or not d[i - 1]: sk += 'XD'
            continue
        sk += c + (chr(97 + rank[i]) if i in rank else str(l))
    gs, prev = '', K
    for l, i in lv:
        g = l - prev; prev = l
        gs += str(g if g <= M else M + 1 + (g - M - 1) % 2)
    return sk + '|' + gs

def wit(s):
    sk, gs = s.split('|')
    far = [k for k, c in enumerate(gs) if int(c) > M]
    for mask in range(1 << len(far)):
        g = [int(c) for c in gs]
        for j, k in enumerate(far):
            if mask >> j & 1: g[k] += 2
        lens, cur = [], K
        for x in g: cur += x; lens.append(cur)
        p = ''
        for i in range(0, len(sk), 2):
            c, v = sk[i], sk[i + 1]
            p += 'TTFF' if c == 'X' else c * (lens[ord(v) - 97] if v >= 'a' else int(v))
        yield p

file, B, K, M = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
amin, amax = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else (K, K + M + 12)
L = [l.strip() for l in open(file) if l.strip()]
U = {x[1:] for x in L if x[0] == 'U'}
N = {x[1:] for x in L if x[0] == 'N'}

nq = 0
def lf(q):
    global nq; nq += 1
    return shape(q) in N or any(shape(r) in U for r in rm(q))

bad = []
nwit = 0
for s in U:
    for w in wit(s):
        nwit += 1
        assert shape(w) == s, (s, w, shape(w))
        if not (lf(w) and all(lf(q) for q in lm(w))): bad.append(('U', s, w))
for s in N:
    for w in wit(s):
        nwit += 1
        assert shape(w) == s, (s, w, shape(w))
        nq += len(lm(w))
        if not all(any(shape(r) in N for r in rm(q)) for q in lm(w)): bad.append(('N', s, w))
missing = [a for a in range(amin, amax + 1) if shape('T' * a + '.' * B + 'F' * a) not in U]
print(f'{len(U)} U + {len(N)} N shapes, {nwit} witnesses, {nq} Left moves and passes: {len(bad)} failing witnesses; starts a = {amin}..{amax} missing: {missing}')
for b in bad[:5]: print('  ', b)
sys.exit(1 if bad or missing else 0)
