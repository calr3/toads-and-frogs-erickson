"""Canonical values of Toads and Frogs positions (a small combinatorial game calculator).

Positions are strings over 'T' (toad, Left, moves right), 'F' (frog, Right, moves left) and '.'
(empty). `value(p)` returns the canonical form of `p` as an interned game id, and `name(g)` prints
it: a number such as `3/2`, a number plus star such as `1*`, or `{L|R}` for anything else.

Used for `docs/RESEARCH_NOTES.md` §15: after the first jump, positions with two toads and two
frogs are almost always numbers or numbers plus star, which is why their outcome is a threshold in
the race count.

Usage:
  python3 cgt.py 'TT..FF' 'T.T....F.F'     values of the given positions
  python3 cgt.py --one                       one toad against one frog, by surrounding space
  python3 cgt.py --kinds [MAXSUM]            how many four-piece positions per order are numbers,
                                             numbers plus star, or other (gaps < 5, sum <= MAXSUM)
"""
import sys, itertools
from functools import lru_cache
from fractions import Fraction
sys.setrecursionlimit(100000)

# canonical games interned: id -> (L tuple of ids, R tuple of ids)
G = []; idx = {}
def mk(L, R):
    key = (tuple(sorted(set(L))), tuple(sorted(set(R))))
    if key in idx: return idx[key]
    idx[key] = len(G); G.append(key); return idx[key]
ZERO = mk((), ())
le_memo = {}
def le(a, b):  # a <= b
    k = (a, b)
    if k in le_memo: return le_memo[k]
    r = all(not le(b, x) for x in G[a][0]) and all(not le(y, a) for y in G[b][1])
    le_memo[k] = r; return r
def canon(L, R):
    L = list(set(L)); R = list(set(R))
    changed = True
    while changed:
        changed = False
        # remove dominated
        L2 = [x for x in L if not any(y != x and le(x, y) for y in L)]
        # keep one of equal ones
        L3 = []
        for x in L2:
            if not any(le(x, y) and le(y, x) for y in L3): L3.append(x)
        R2 = [x for x in R if not any(y != x and le(y, x) for y in R)]
        R3 = []
        for x in R2:
            if not any(le(x, y) and le(y, x) for y in R3): R3.append(x)
        L, R = L3, R3
        g = mk(L, R)
        # reversible Left options: x in L with some x^R <= g -> replace x by x^{RL}
        for x in L:
            for xr in G[x][1]:
                if le(xr, g):
                    L = [y for y in L if y != x] + list(G[xr][0]); changed = True; break
            if changed: break
        if changed: continue
        for x in R:
            for xl in G[x][0]:
                if le(g, xl):
                    R = [y for y in R if y != x] + list(G[xl][1]); changed = True; break
            if changed: break
    return mk(L, R)
# naming
name_memo = {}
def isnum(g):
    v = numval(g); return v is not None
num_memo = {}
def numval(g):
    if g in num_memo: return num_memo[g]
    L, R = G[g]; r = None
    if not L and not R: r = Fraction(0)
    else:
        lv = [numval(x) for x in L]; rv = [numval(x) for x in R]
        if all(v is not None for v in lv + rv) and (not lv or not rv or max(lv) < min(rv)):
            lo = max(lv) if lv else None; hi = min(rv) if rv else None
            # simplest number between
            if lo is None: r = Fraction(min(0, int(hi) - 1 if hi == int(hi) else int(hi // 1))) if hi <= 0 else Fraction(0)
            elif hi is None: r = Fraction(max(0, int(lo) + 1 if lo == int(lo) else int(lo // 1) + 1)) if lo >= 0 else Fraction(0)
            else:
                if lo < 0 < hi: r = Fraction(0)
                else:
                    # simplest dyadic in (lo, hi)
                    import math
                    n = math.floor(lo) + 1
                    if n < hi and (lo >= 0): r = Fraction(n)
                    elif hi <= 0 and math.ceil(hi) - 1 > lo: r = Fraction(math.ceil(hi) - 1)
                    else:
                        d = 1
                        while True:
                            d *= 2; k = math.floor(lo * d) + 1
                            if Fraction(k, d) < hi: r = Fraction(k, d); break
    num_memo[g] = r; return r
def name(g):
    if g in name_memo: return name_memo[g]
    v = numval(g)
    if v is not None: s = str(v)
    else:
        L, R = G[g]
        if len(L) == 1 and len(R) == 1 and L[0] == R[0] and numval(L[0]) is not None: s = (str(numval(L[0])) if numval(L[0]) != 0 else "") + "*"
        else: s = "{" + ",".join(name(x) for x in L) + "|" + ",".join(name(x) for x in R) + "}"
    name_memo[g] = s; return s
# toads and frogs positions as strings
@lru_cache(maxsize=None)
def value(p):
    L = []; R = []
    n = len(p)
    for i, ch in enumerate(p):
        if ch == 'T':
            if i + 1 < n and p[i+1] == '.': L.append(p[:i] + '.T' + p[i+2:])
            elif i + 2 < n and p[i+1] == 'F' and p[i+2] == '.': L.append(p[:i] + '.FT' + p[i+3:])
        elif ch == 'F':
            if i - 1 >= 0 and p[i-1] == '.': R.append(p[:i-1] + 'F.' + p[i+1:])
            elif i - 2 >= 0 and p[i-1] == 'T' and p[i-2] == '.': R.append(p[:i-2] + 'FT.' + p[i+1:])
    return canon([value(x) for x in L], [value(x) for x in R])
def pos(order, g):
    """The position with pieces `order` (e.g. 'TFTF') and gaps g[0..len(order)]."""
    s = '.' * g[0]
    for i, ch in enumerate(order): s += ch + '.' * g[i + 1]
    return s

def kind(p):
    v = value(p)
    if numval(v) is not None: return "number"
    L, R = G[v]
    if len(L) == 1 and len(R) == 1 and L[0] == R[0] and numval(L[0]) is not None: return "number+*"
    return "other"

if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "--one":
        for a in range(4):
            for b in range(4):
                print(f"a={a} b={b}:", "  ".join(name(value('.' * a + 'T' + '.' * n + 'F' + '.' * b)) for n in range(11)))
    elif args and args[0] == "--kinds":
        mx = int(args[1]) if len(args) > 1 else 12
        for order in ["TTFF", "TFTF", "FTTF", "TFFT", "FTFT", "FFTT"]:
            cnt = {}; ex = []
            for g in itertools.product(range(5), repeat=5):
                if sum(g) > mx: continue
                k = kind(pos(order, list(g))); cnt[k] = cnt.get(k, 0) + 1
                if k == "other" and len(ex) < 4: ex.append((g, name(value(pos(order, list(g))))))
            print(order, cnt, ex)
    else:
        for p in args: print(p, name(value(p)))
