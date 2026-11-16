#!/usr/bin/env python3
"""Generate `Cgt/RowA2Data.lean`: the set of shapes for the `a = 2` row.

Mirrors the definitions of `Cgt/Four.lean` and `Cgt/Shape4.lean` exactly (pieces as booleans,
moves `lm1..lm4` / `rm1..rm4`, `shape`, `key`, `decodeKey`, `wit`) and computes a set of shapes
containing the shapes of `T□T□ᵐFF` (all m >= 1) that passes `checkAll`: every Left move from
every witness of a shape in the set has a Right reply whose shape is in the set.  Right's
replies are chosen by the exact solver, preferring shapes already in the set and then replies
close to mirror symmetry.

Usage: gen_row2.py > Cgt/RowA2Data.lean
"""
import sys
from collections import deque
from functools import lru_cache

sys.setrecursionlimit(10 ** 6)
K = 4


# ---------------------------------------------------------------- the game (for choosing replies)
def lm_s(s):
    n = len(s); out = []
    for i, c in enumerate(s):
        if c == 'T':
            if i + 1 < n and s[i + 1] == '.':
                out.append(s[:i] + '.T' + s[i + 2:])
            elif i + 2 < n and s[i + 1] == 'F' and s[i + 2] == '.':
                out.append(s[:i] + '.FT' + s[i + 3:])
    return out


def rm_s(s):
    out = []
    for i, c in enumerate(s):
        if c == 'F':
            if i >= 1 and s[i - 1] == '.':
                out.append(s[:i - 1] + 'F.' + s[i + 1:])
            elif i >= 2 and s[i - 1] == 'T' and s[i - 2] == '.':
                out.append(s[:i - 2] + 'FT.' + s[i + 1:])
    return out


@lru_cache(None)
def LF(s):
    return any(not RF(t) for t in lm_s(s))


@lru_cache(None)
def RF(s):
    return any(not LF(t) for t in rm_s(s))


def le0(s):
    return not LF(s)


# ---------------------------------------------------------------- Lean mirror: P4 = (c1..c4, g0..g4)
def to_str(p):
    c, g = p[:4], p[4:]
    s = '.' * g[0]
    for k in range(4):
        s += ('T' if c[k] else 'F') + '.' * g[k + 1]
    return s


def upd(p, **kw):
    names = ['c1', 'c2', 'c3', 'c4', 'g0', 'g1', 'g2', 'g3', 'g4']
    d = dict(zip(names, p)); d.update(kw)
    return tuple(d[n] for n in names)


def lms(p):
    c1, c2, c3, c4, g0, g1, g2, g3, g4 = p
    out = []
    if c1:
        if g1 != 0: out.append(upd(p, g0=g0 + 1, g1=g1 - 1))
        elif (not c2) and g2 != 0: out.append(upd(p, c1=False, c2=True, g0=g0 + 1, g2=g2 - 1))
    if c2:
        if g2 != 0: out.append(upd(p, g1=g1 + 1, g2=g2 - 1))
        elif (not c3) and g3 != 0: out.append(upd(p, c2=False, c3=True, g1=g1 + 1, g3=g3 - 1))
    if c3:
        if g3 != 0: out.append(upd(p, g2=g2 + 1, g3=g3 - 1))
        elif (not c4) and g4 != 0: out.append(upd(p, c3=False, c4=True, g2=g2 + 1, g4=g4 - 1))
    if c4 and g4 != 0:
        out.append(upd(p, g3=g3 + 1, g4=g4 - 1))
    return out


def rms(p):
    c1, c2, c3, c4, g0, g1, g2, g3, g4 = p
    out = []
    if (not c1) and g0 != 0: out.append(upd(p, g0=g0 - 1, g1=g1 + 1))
    if not c2:
        if g1 != 0: out.append(upd(p, g1=g1 - 1, g2=g2 + 1))
        elif c1 and g0 != 0: out.append(upd(p, c1=False, c2=True, g0=g0 - 1, g2=g2 + 1))
    if not c3:
        if g2 != 0: out.append(upd(p, g2=g2 - 1, g3=g3 + 1))
        elif c2 and g1 != 0: out.append(upd(p, c2=False, c3=True, g1=g1 - 1, g3=g3 + 1))
    if not c4:
        if g3 != 0: out.append(upd(p, g3=g3 - 1, g4=g4 + 1))
        elif c3 and g2 != 0: out.append(upd(p, c3=False, c4=True, g2=g2 - 1, g4=g4 + 1))
    return out


def cap(x):
    return x if x < K else K + x % 2


def code(p):
    cc = lambda b: 1 if b else 2
    return 27 * cc(p[0]) + 9 * cc(p[1]) + 3 * cc(p[2]) + cc(p[3])


def shape(p):
    c1, c2, c3, c4, g0, g1, g2, g3, g4 = p
    return (code(p), g4 - g0, g3 - g1, cap(min(g0, g4)), cap(min(g1, g3)), cap(g2))


def in_range(s):
    return s[0] < 81 and -32 <= s[1] < 32 and -32 <= s[2] < 32 and s[3] < 8 and s[4] < 8 and s[5] < 8


def key(s):
    return s[0] * 2097152 + (s[1] + 32) * 32768 + (s[2] + 32) * 512 + s[3] * 64 + s[4] * 8 + s[5]


def cap_vals(c):
    return [c] if c < K else [c, c + 2]


def gaps_of(m, d):
    return (m, m + d) if d >= 0 else (m - d, m)


def mkP(s, a, b, c):
    cd = s[0]
    cells = [cd // 27 % 3 == 1, cd // 9 % 3 == 1, cd // 3 % 3 == 1, cd % 3 == 1]
    g0, g4 = gaps_of(a, s[1]); g1, g3 = gaps_of(b, s[2])
    return tuple(cells) + (g0, g1, c, g3, g4)


def wit(s):
    return [mkP(s, a, b, c) for a in cap_vals(s[3]) for b in cap_vals(s[4]) for c in cap_vals(s[5])]


def asym(p):
    return abs(p[8] - p[4]) + abs(p[7] - p[5])


D = 2


def gaps_s(s):
    import re
    return [len(x) for x in re.split(r'[TF]', s)]


def bounded(s):
    g = gaps_s(s)
    return abs(g[4] - g[0]) <= D and abs(g[3] - g[1]) <= D


@lru_cache(None)
def win_bounded(z):
    """Left to move at z: Right can keep every later position <= 0 with mirrored gap
    differences at most D."""
    return all(any(le0(r) and bounded(r) and win_bounded(r) for r in rm_s(q)) for q in lm_s(z))


def main():
    start = [(True, True, False, False, 0, 1, m, 0, 0) for m in range(1, K + 2)]
    for p in start:
        assert le0(to_str(p))
    seen = {shape(p) for p in start}
    todo = deque(seen)
    while todo:
        s = todo.popleft()
        for w in wit(s):
            for q in lms(w):
                good = [r for r in rms(q) if le0(to_str(r))]
                assert good, (s, w, q)
                known = [r for r in good if shape(r) in seen]
                if known:
                    r = known[0]
                else:
                    safe = [r for r in good if bounded(to_str(r)) and win_bounded(to_str(r))]
                    assert safe, (s, to_str(w), to_str(q))
                    r = min(safe, key=lambda r: (asym(r), to_str(r)))
                sr = shape(r)
                assert in_range(sr)
                if sr not in seen:
                    seen.add(sr); todo.append(sr)
    # verify checkAll exactly as Lean computes it
    keys = sorted(key(s) for s in seen)
    kset = set(keys)
    for s in seen:
        for w in wit(s):
            for q in lms(w):
                assert any(in_range(shape(r)) and key(shape(r)) in kset for r in rms(q))

    def tree(lo, hi):
        if lo >= hi:
            return 'KTree.leaf'
        mid = (lo + hi) // 2
        return f'(KTree.node {tree(lo, mid)} {keys[mid]} {tree(mid + 1, hi)})'

    print('import Cgt.Shape4\n')
    print('/-! Machine-generated by `scripts/gen_row2.py`: the shapes used for the `a = 2` row. -/\n')
    print('namespace Cgt\n')
    print(f'/-- {len(keys)} shapes, as a balanced search tree of keys. -/')
    print(f'def treeA2 : KTree :=\n  {tree(0, len(keys))}\n')
    print('end Cgt')
    print(f'-- {len(keys)} shapes', file=sys.stderr)


if __name__ == '__main__':
    main()
