"""Closure of the a = 2 pass positions under a fixed, local Right strategy (normal play), and a
lower bound on the number of DFA states needed to separate it from positions that are not <= 0.

Right answers each Left move with the reply <= 0 whose folded window is nearest to Left's move
(ties broken by the folded word), hoping this keeps the set regular.

Usage: canonical_z.py N1 N2 ...   (largest board sizes)
"""
import sys
from folded import fold, unfold, lm, rm, le0, ORIENT


def fidx(p, q):
    n = len(p)
    return {min(c, n - 1 - c) for c in range(n) if p[c] != q[c]}


def reply(z, q):
    cands = [r for r in rm(q) if le0(r)]
    if not cands:
        return None
    mv = fidx(z, q)
    return min(cands, key=lambda r: (min(abs(i - j) for i in mv for j in fidx(q, r)), fold(r)))


def pass_positions(nmax):
    out = []
    for i in range(nmax):
        for j in range(1, nmax):
            for w in ('.' * i + 'T' + '.' * (j + 1) + 'TF' + '.' * j + 'F' + '.' * i,
                      '.' * i + 'T' + '.' * (j + 1) + 'FT' + '.' * (j - 1) + 'F' + '.' * i):
                if len(w) <= nmax:
                    out.append(w)
        w = '.' * (i + 1) + 'TT.F.F' + '.' * i
        if len(w) <= nmax:
            out.append(w)
    return out


def closure(nmax):
    C = set(); stack = pass_positions(nmax)
    while stack:
        z = stack.pop()
        if z in C:
            continue
        assert le0(z), z
        C.add(z)
        for q in lm(z):
            r = reply(z, q)
            assert r is not None, (z, q)
            stack.append(r)
    return C


def all_2t2f(n):
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(n):
                for l in range(k + 1, n):
                    if len({i, j, k, l}) == 4:
                        w = ['.'] * n
                        w[i] = w[j] = 'T'; w[k] = w[l] = 'F'
                        yield ''.join(w)


def bound(nmax, C):
    sig = {}
    def add(f, lab):
        for i in range(len(f) + 1):
            sig.setdefault(f[:i], {}).setdefault(f[i:], set()).add(lab)
    for z in C:
        add(fold(z), '+')
    for n in range(0, nmax + 1):
        for w in all_2t2f(n):
            if not le0(w):
                add(fold(w), '-')
    def distinct(u, v):
        su, sv = sig[u], sig[v]
        if len(su) > len(sv):
            su, sv = sv, su
        return any(lv and (('+' in ls and '-' in lv) or ('-' in ls and '+' in lv))
                   for suf, ls in su.items() for lv in [sv.get(suf)])
    clique = []
    for u in sorted(sig, key=lambda u: -len(sig[u])):
        if all(distinct(u, v) for v in clique):
            clique.append(u)
    return len(clique)


if __name__ == '__main__':
    for nmax in map(int, sys.argv[1:]):
        C = closure(nmax)
        print(f'[{ORIENT}] boards <= {nmax}: closure has {len(C)} positions; '
              f'any DFA for it needs >= {bound(nmax, C)} states', flush=True)
