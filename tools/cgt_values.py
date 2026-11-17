"""Minimal canonical-form engine for short partizan games + Toads and Frogs."""
import sys
from functools import lru_cache
sys.setrecursionlimit(1000000)

# Games are interned: id -> (lefts tuple of ids, rights tuple of ids), canonical.
_games = []
_index = {}

def mk(lefts, rights):
    key = (tuple(sorted(set(lefts))), tuple(sorted(set(rights))))
    g = _index.get(key)
    if g is None:
        g = len(_games)
        _games.append(key)
        _index[key] = g
    return g

ZERO = mk((), ())

def L(g): return _games[g][0]
def R(g): return _games[g][1]

_le = {}
def le(g, h):
    """g <= h"""
    if g == h:
        return True
    k = (g, h)
    r = _le.get(k)
    if r is not None:
        return r
    r = True
    for gl in L(g):
        if le(h, gl):
            r = False
            break
    if r:
        for hr in R(h):
            if le(hr, g):
                r = False
                break
    _le[k] = r
    return r

def eq(g, h): return le(g, h) and le(h, g)
def lf(g, h): return not le(h, g)  # g <| h

def canon(lefts, rights):
    """Build canonical form from canonical options."""
    lefts = list(set(lefts)); rights = list(set(rights))
    changed = True
    while changed:
        changed = False
        # remove dominated
        lefts = [a for a in lefts if not any(b != a and le(a, b) and not (le(b, a) and b < a) for b in lefts)]
        rights = [a for a in rights if not any(b != a and le(b, a) and not (le(a, b) and b < a) for b in rights)]
        G = mk(lefts, rights)
        # reversible left options
        newl = []
        for a in lefts:
            rev = None
            for ar in R(a):
                if le(ar, G):
                    rev = ar
                    break
            if rev is not None:
                newl.extend(L(rev)); changed = True
            else:
                newl.append(a)
        newr = []
        for a in rights:
            rev = None
            for al in L(a):
                if le(G, al):
                    rev = al
                    break
            if rev is not None:
                newr.extend(R(rev)); changed = True
            else:
                newr.append(a)
        lefts = list(set(newl)); rights = list(set(newr))
    return mk(lefts, rights)

def neg(g):
    return _neg(g)
@lru_cache(maxsize=None)
def _neg(g):
    return canon([_neg(x) for x in R(g)], [_neg(x) for x in L(g)])

@lru_cache(maxsize=None)
def add(g, h):
    if g == ZERO: return h
    if h == ZERO: return g
    if g > h: g, h = h, g
    lefts = [add(x, h) for x in L(g)] + [add(g, y) for y in L(h)]
    rights = [add(x, h) for x in R(g)] + [add(g, y) for y in R(h)]
    return canon(lefts, rights)

# numbers
from fractions import Fraction
@lru_cache(maxsize=None)
def num(q):
    q = Fraction(q)
    if q == 0: return ZERO
    if q.denominator == 1:
        if q > 0: return canon([num(q - 1)], [])
        return canon([], [num(q + 1)])
    # dyadic
    d = q.denominator
    lo = Fraction(q.numerator - 1, d); hi = Fraction(q.numerator + 1, d)
    return canon([num(lo)], [num(hi)])

def is_number(g):
    return _isnum(g)
@lru_cache(maxsize=None)
def _isnum(g):
    if not all(_isnum(x) for x in L(g)) or not all(_isnum(x) for x in R(g)):
        return False
    for a in L(g):
        for b in R(g):
            if le(b, a):
                return False
    return True

@lru_cache(maxsize=None)
def numval(g):
    # canonical number value
    if not L(g) and not R(g): return Fraction(0)
    assert len(L(g)) <= 1 and len(R(g)) <= 1
    if not R(g): return numval(L(g)[0]) + 1
    if not L(g): return numval(R(g)[0]) - 1
    a = numval(L(g)[0]); b = numval(R(g)[0])
    return (a + b) / 2

def simplest(a, b):
    # simplest dyadic strictly between a and b
    if a < 0 < b: return Fraction(0)
    if b <= 0:
        return -simplest(-b, -a)
    n = int(a) + 1 if a >= 0 else 0
    if n < b:
        # smallest integer > a
        import math
        n = math.floor(a) + 1
        if n < b: return Fraction(n)
    d = 1
    while True:
        d *= 2
        import math
        k = math.floor(a * d) + 1
        if Fraction(k, d) < b: return Fraction(k, d)

@lru_cache(maxsize=None)
def lstop(g):
    if is_number(g): return numval(g)
    return max(rstop(x) for x in L(g))
@lru_cache(maxsize=None)
def rstop(g):
    if is_number(g): return numval(g)
    return min(lstop(x) for x in R(g))

STAR = canon([ZERO], [ZERO])
UP = canon([ZERO], [STAR])

def infinitesimal(g):
    return lstop(g) == 0 and rstop(g) == 0

def show(g, depth=0):
    if is_number(g):
        v = numval(g)
        return str(v)
    if g == STAR: return '*'
    if g == UP: return '^'
    if g == neg(UP): return 'v'
    if depth > 6: return '...'
    return '{' + ','.join(show(x, depth+1) for x in L(g)) + '|' + ','.join(show(x, depth+1) for x in R(g)) + '}'

# ---------------- Toads and Frogs -----------------
def tf_left(s):
    n = len(s)
    out = []
    for i, c in enumerate(s):
        if c == 'T':
            if i + 1 < n and s[i+1] == '.':
                out.append(s[:i] + '.T' + s[i+2:])
            elif i + 2 < n and s[i+1] == 'F' and s[i+2] == '.':
                out.append(s[:i] + '.FT' + s[i+3:])
    return out

def tf_right(s):
    out = []
    for i, c in enumerate(s):
        if c == 'F':
            if i - 1 >= 0 and s[i-1] == '.':
                out.append(s[:i-1] + 'F.' + s[i+1:])
            elif i - 2 >= 0 and s[i-1] == 'T' and s[i-2] == '.':
                out.append(s[:i-2] + 'FT.' + s[i+1:])
    return out

_tfmemo = {}
def tf(s):
    g = _tfmemo.get(s)
    if g is not None: return g
    g = canon([tf(x) for x in tf_left(s)], [tf(x) for x in tf_right(s)])
    _tfmemo[s] = g
    return g

def pos(a, b, c=None):
    if c is None: c = a
    return 'T' * a + '.' * b + 'F' * c

if __name__ == '__main__':
    for a in range(1, 5):
        row = []
        for b in range(0, 9):
            g = tf(pos(a, b))
            row.append(f"{show(g)}[{lstop(g)},{rstop(g)}]")
        print(a, row)
