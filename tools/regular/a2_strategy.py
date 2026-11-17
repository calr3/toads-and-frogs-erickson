"""Right's normal-play strategy from T.T .^m FF (the a = 2 row), and its abstract shapes.

A two-toad two-frog position is a piece order plus five gaps g0..g4.  Its *shape* records the
order, the differences of mirrored gaps (g4 - g0, g3 - g1), the smaller gap of each mirrored
pair and the centre gap (capped at K, with parity when capped).  Right picks, among replies
that keep the position <= 0, one closest to mirror symmetry.
"""
import re
import sys
from collections import defaultdict
from functools import lru_cache
from folded import lm, rm, le0

sys.setrecursionlimit(10 ** 6)


def gaps(s):
    order = ''.join(c for c in s if c != '.')
    g = [len(x) for x in re.split(r'[TF]', s)]
    return order, tuple(g)


def asym(s):
    o, g = gaps(s)
    return abs(g[4] - g[0]) + abs(g[3] - g[1])


def shape(s, K):
    o, g = gaps(s)
    cap = lambda x: x if x < K else (K, x % 2)
    return (o, g[4] - g[0], g[3] - g[1], cap(min(g[0], g[4])), cap(min(g[1], g[3])), cap(g[2]))


D = 2


def bounded(s):
    o, g = gaps(s)
    return abs(g[4] - g[0]) <= D and abs(g[3] - g[1]) <= D


@lru_cache(None)
def win(z):
    """Left to move at z: Right can keep every later position <= 0 and within the bound."""
    return all(any(le0(r) and bounded(r) and win(r) for r in rm(q)) for q in lm(z))


def reply(q):
    good = [r for r in rm(q) if le0(r) and bounded(r) and win(r)]
    return min(good, key=lambda r: (asym(r), r)) if good else None


def move_type(q, r):
    """Which frog moved (1 = front/left one, 2 = rear) and how."""
    fq = [i for i, c in enumerate(q) if c == 'F']
    fr = [i for i, c in enumerate(r) if c == 'F']
    k = [j for j in range(2) if fq[j] != fr[j]][0]
    return (k + 1, fq[k] - fr[k])


def reachable(m):
    seen = set(); stack = ['T.T' + '.' * m + 'FF']
    choices = []
    while stack:
        z = stack.pop()
        if z in seen:
            continue
        seen.add(z)
        for q in lm(z):
            r = reply(q)
            assert r is not None, (z, q)
            choices.append((q, r))
            stack.append(r)
    return seen, choices


if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    shapes_all = set()
    conflict = defaultdict(set)
    for m in range(1, int(sys.argv[2]) if len(sys.argv) > 2 else 31):
        Z, ch = reachable(m)
        new = {shape(z, K) for z in Z} - shapes_all
        shapes_all |= new
        for q, r in ch:
            conflict[shape(q, K)].add(move_type(q, r))
        bad = sum(1 for v in conflict.values() if len(v) > 1)
        print(f'm={m}: {len(Z)} positions, {len(shapes_all)} shapes (+{len(new)}), '
              f'shapes where the reply type is not unique: {bad}', flush=True)
