"""Planning aid for proofs of `position <= n` and `position <= {n | n}` by Conway's one-step rules.

le_int(p, n) and le_star(p, n) are exact, for integers n of either sign and any Toads and Frogs
position p (a string over "TF."). `node` prints, for a family of positions with parameters x, y,
how each Left move can be answered, on a grid of parameter values; `leaf` looks for a Blocking Rule
split X FF Y with (least integer >= X) + (least integer >= Y) <= n.

Usage: see the calls at the end of the file, or import it.
"""
import sys
from functools import lru_cache
sys.setrecursionlimit(1000000)

def lm(s):
    o = []
    for i, c in enumerate(s):
        if c == 'T':
            if i + 1 < len(s) and s[i+1] == '.': o.append(s[:i] + '.T' + s[i+2:])
            elif i + 2 < len(s) and s[i+1] == 'F' and s[i+2] == '.': o.append(s[:i] + '.FT' + s[i+3:])
    return o
def rm(s):
    o = []
    for i, c in enumerate(s):
        if c == 'F':
            if i >= 1 and s[i-1] == '.': o.append(s[:i-1] + 'F.' + s[i+1:])
            elif i >= 2 and s[i-1] == 'T' and s[i-2] == '.': o.append(s[:i-2] + 'FT.' + s[i+1:])
    return o

@lru_cache(maxsize=None)
def le_int(p, n):
    """value(p) <= n"""
    for q in lm(p):
        if n >= 1 and le_int(q, n - 1): continue
        if any(le_int(r, n) for r in rm(q)): continue
        return False
    if n < 0: return any(le_int(r, n + 1) for r in rm(p))
    return True
@lru_cache(maxsize=None)
def ge_int(p, n):
    """n <= value(p)"""
    for q in rm(p):
        if n <= -1 and ge_int(q, n + 1): continue
        if any(ge_int(r, n) for r in lm(q)): continue
        return False
    if n > 0: return any(ge_int(r, n - 1) for r in lm(p))
    return True
@lru_cache(maxsize=None)
def le_star(p, n):
    """value(p) <= {n | n}"""
    if ge_int(p, n): return False
    return all(le_int(q, n) or any(le_star(r, n) for r in rm(q)) for q in lm(p))
def ub(p):
    n = -60
    while not le_int(p, n): n += 1
    return n
def lb(p):
    n = 60
    while not ge_int(p, n): n -= 1
    return n

def node(name, f, kind, n, grid):
    """f(x, y) -> position; kind 'star' or 'int'; n(x, y) -> the bound."""
    print(f'== {name}: {kind}')
    for (x, y) in grid:
        p = f(x, y); N = n(x, y)
        ok = le_star(p, N) if kind == 'star' else le_int(p, N)
        line = f'  x={x} y={y} {p} bound {N}: {"TRUE" if ok else "FALSE"}'
        print(line)
        for q in lm(p):
            if kind == 'star':
                direct = le_int(q, N); reps = [r for r in rm(q) if le_star(r, N)]
                print(f'     L {q}: {"direct <= n" if direct else ""} replies {reps}')
            else:
                direct = le_int(q, N - 1); reps = [r for r in rm(q) if le_int(r, N)]
                print(f'     L {q}: {"direct <= n-1" if direct else ""} replies {reps}')
        if kind == 'star': print(f'     R options <= n: {[r for r in rm(p) if le_int(r, N)]}')
        elif N < 0: print(f'     n < 0, R options <= n+1: {[r for r in rm(p) if le_int(r, N + 1)]}')

def leaf(p, N):
    out = []
    for i in range(len(p) - 1):
        if p[i] == 'F' and p[i+1] == 'F':
            X, Y = p[:i], p[i+2:]
            if ub(X) + ub(Y) <= N: out.append((X, ub(X), Y, ub(Y)))
    return out
