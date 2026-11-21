"""Integer bounds for one-frog Toads and Frogs positions, without canonical forms.

Right (the frog) has at most one move, so for an integer n >= 0:
  G <= 0  iff every Left move q has a Right reply r with G(r) <= 0
  G <= n  iff every Left move q has G(q) <= n-1 or a Right reply r with G(r) <= n   (n >= 1)
  G >= 0  iff the Right move r (if any) has a Left reply s with G(s) >= 0
  G >= n  iff (same with n) and some Left move q has G(q) >= n-1                     (n >= 1)
U(p) = least n >= 0 with G <= n;  Lw(p) = greatest n >= 0 with G >= n, or -1.
"""
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)

def lmoves(s):
    n = len(s); out = []
    for i, c in enumerate(s):
        if c == 'T':
            if i + 1 < n and s[i+1] == '.': out.append(s[:i] + '.T' + s[i+2:])
            elif i + 2 < n and s[i+1] == 'F' and s[i+2] == '.': out.append(s[:i] + '.FT' + s[i+3:])
    return out

def rmove(s):
    i = s.index('F')
    if i >= 1 and s[i-1] == '.': return s[:i-1] + 'F.' + s[i+1:]
    if i >= 2 and s[i-1] == 'T' and s[i-2] == '.': return s[:i-2] + 'FT.' + s[i+1:]
    return None

BIG = 10**6
@lru_cache(maxsize=None)
def U(s):
    best = 0
    for q in lmoves(s):
        r = rmove(q)
        v = U(q) + 1
        if r is not None: v = min(v, U(r))
        best = max(best, v)
    return best

@lru_cache(maxsize=None)
def Lw(s):
    # threshold from the Right move
    r = rmove(s)
    cap = BIG if r is None else max((Lw(x) for x in lmoves(r)), default=-1)
    if cap < 0: return -1
    best = max((Lw(q) for q in lmoves(s) if Lw(q) >= 0), default=-1) + 1  # some q >= n-1
    return min(cap, max(best, 0))

def phi(s):
    n = len(s); f = s.index('F')
    xs = [i for i, c in enumerate(s) if c == 'T']
    k = len(xs); m = sum(1 for x in xs if x < f)
    return sum((n - k + i) - x for i, x in enumerate(xs)) - m - f
