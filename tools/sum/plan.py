"""Find a proof tree for `p <= n` / `p <= {n | n}` on one concrete position.

Inner nodes use the one-step rules; a leaf is a position with at most one frog or at most one toad
(its bound is a library fact), or a Blocking Rule split X FF Y into two such positions whose least
integer upper bounds add up to at most n. The smallest tree is printed. Run it on a generic member
of a family (reservoirs of 4 or 5 pieces) and read off the family's proof.

Usage: python3 plan.py POSITION star|int N
"""
import sys
from functools import lru_cache
from explore import lm, rm, le_int, le_star, ub

def library(p): return p.count('F') <= 1 or p.count('T') <= 1
def br(p, N):
    best = None
    for i in range(len(p) - 1):
        if p[i] == 'F' and p[i+1] == 'F':
            X, Y = p[:i], p[i+2:]
            if library(X) and library(Y) and ub(X) + ub(Y) <= N:
                best = (X, ub(X), Y, ub(Y)); break
    return best
BIG = 10**9
@lru_cache(maxsize=None)
def cost(p, kind, N):
    """(size, plan) of the smallest proof, or (BIG, None)."""
    if kind == 'int':
        if not le_int(p, N): return (BIG, None)
        if library(p): return (1, ('LIB',))
        s = br(p, N)
        if s: return (1, ('BR', s))
        total = 1; steps = []
        for q in lm(p):
            c1 = cost(q, 'int', N - 1)
            best = (c1[0], ('direct', q)) if c1[0] < BIG else (BIG, None)
            for r in rm(q):
                c = cost(r, 'int', N)
                if c[0] < best[0]: best = (c[0], ('reply', q, r))
            if best[0] >= BIG: return (BIG, None)
            total += best[0]; steps.append(best[1])
        ropt = None
        if N < 0:
            b = (BIG, None)
            for r in rm(p):
                c = cost(r, 'int', N + 1)
                if c[0] < b[0]: b = (c[0], r)
            if b[0] >= BIG: return (BIG, None)
            total += b[0]; ropt = b[1]
        return (total, ('NODE', steps, ropt))
    else:
        if not le_star(p, N): return (BIG, None)
        total = 1; steps = []
        for q in lm(p):
            c1 = cost(q, 'int', N)
            best = (c1[0], ('direct', q)) if c1[0] < BIG else (BIG, None)
            for r in rm(q):
                c = cost(r, 'star', N)
                if c[0] < best[0]: best = (c[0], ('reply', q, r))
            if best[0] >= BIG: return (BIG, None)
            total += best[0]; steps.append(best[1])
        b = (BIG, None)
        for r in rm(p):
            c = cost(r, 'int', N)
            if c[0] < b[0]: b = (c[0], r)
        if b[0] >= BIG: return (BIG, None)
        return (total + b[0], ('NODE', steps, b[1]))

seen = set()
def show(p, kind, N, d=0):
    ind = '  ' * d; c = cost(p, kind, N)
    tag = f'{p} <= {N}{"*" if kind == "star" else ""}'
    if (p, kind, N) in seen: print(f'{ind}{tag}  (above)'); return
    seen.add((p, kind, N))
    plan = c[1]
    if plan[0] == 'LIB': print(f'{ind}{tag}  LIBRARY (least bound {ub(p)})'); return
    if plan[0] == 'BR': X, a, Y, b = plan[1]; print(f'{ind}{tag}  BR: {X} <= {a}, {Y} <= {b}'); return
    print(f'{ind}{tag}')
    for st in plan[1]:
        if st[0] == 'direct':
            print(f'{ind}  Left {st[1]}: direct'); show(st[1], 'int', N - 1 if kind == 'int' else N, d + 2)
        else:
            print(f'{ind}  Left {st[1]}: reply'); show(st[2], kind, N, d + 2)
    if plan[2]:
        print(f'{ind}  Right option:'); show(plan[2], 'int', N + 1 if kind == 'int' else N, d + 2)

if __name__ == '__main__':
    p, kind, N = sys.argv[1], sys.argv[2], int(sys.argv[3])
    c = cost(p, kind, N)
    print('size', c[0] if c[0] < BIG else 'NO PROOF')
    if c[0] < BIG: show(p, kind, N)
