"""Check the inductive proof of the one-frog theorem on every position of small boards.

Each claim about a position must follow, by one step of Conway's recursion for comparing with
n, n + 1/2 or n*, from claims about positions one or two moves later.  Nothing here uses the
true values: if this passes for every board size, the induction is a proof.

Usage: python3 check_rules.py MAXLEN
"""
import sys
from bounds import lmoves, rmove, phi

def feat(s):
    f = s.index('F'); left = s[:f]
    m = left.count('T'); rho = s[f+1:].count('.')
    if m == 0: return 0, None, None
    xm = left.rindex('T')
    return m, rho - left[:xm].count('.'), f - 1 - xm

def packed(s):
    """No Left move except possibly a jump by the front toad: the unpassed toads are contiguous
    and the passed toads are packed against the right end."""
    f = s.index('F'); left = s[:f].lstrip('.'); right = s[f+1:]
    return 'T.' not in right and '.' not in left.rstrip('.')

def upper(s):
    """Claimed upper bounds: ('int', n) is G <= n, ('half', n) is G <= n + 1/2, ('star', n) is G <= n*."""
    m, D, d = feat(s); p = phi(s); out = []
    if m == 0: out.append(('int', max(p, 0)))
    elif D >= 2: out.append(('int', p))
    elif D == 1 and d % 2 == 0: out.append(('int', p))
    elif D == 1: out.append(('half', p))
    elif D == 0 and d % 2 == 0: out.append(('int', max(p + 1, 0)))
    elif D == 0 and p >= 0: out.append(('star', p + 1))
    elif D == 0 and m == 1 and packed(s): out.append(('star', 0))
    elif D == -1 and d == 0 and p + 2 >= 1: out.append(('int', p + 2))
    elif D == -1 and d == 0 and packed(s) and (m == 1 or s[s.index('F')+1:].count('.') == 1):
        out.append(('int', 0))
    return out

def lower(s):
    m, D, d = feat(s); p = phi(s); out = []
    if p >= 0: out.append(('int', p))
    if m >= 1:
        if (D <= -1 or (D == 0 and d % 2 == 0)) and p + 1 >= 0: out.append(('int', p + 1))
        if (D <= -2 or (D == -1 and d % 2 == 0)) and p + 2 >= 0: out.append(('int', p + 2))
        if D == 1 and d % 2 == 1: out.append(('half', p))
        if D == 0 and d % 2 == 1 and p + 1 >= 0: out.append(('star', p + 1))
    return out

def le_int(x, k):  return k >= 0 and any(j <= k if t == 'int' else j + 1 <= k for t, j in upper(x))
def le_half(x, n): return any(j <= n for t, j in upper(x))
def le_star(x, n): return any(j <= n if t == 'star' else j <= n - 1 for t, j in upper(x))
def ge_int(x, k):  return any(j >= k + 1 if t == 'star' else j >= k for t, j in lower(x))
def ge_half(x, n): return any(j >= n if t == 'half' else j >= n + 1 for t, j in lower(x))
def ge_star(x, n): return any(j >= n + 1 if t == 'int' else j >= n for t, j in lower(x))

def ok_upper(s, t, n):
    R = rmove(s)
    for q in lmoves(s):
        r = rmove(q)
        if t == 'int':
            if n >= 1 and le_int(q, n - 1): continue
            if r is not None and le_int(r, n): continue
        elif t == 'half':
            if le_int(q, n): continue
            if r is not None and le_half(r, n): continue
        else:
            if le_int(q, n): continue
            if r is not None and le_star(r, n): continue
        return False
    if t == 'half': return R is not None and le_int(R, n + 1)
    if t == 'star': return R is not None and le_int(R, n)
    return True

def ok_lower(s, t, n):
    R = rmove(s)
    if R is not None:
        good = False
        if t == 'half' and ge_int(R, n + 1): good = True
        if t == 'star' and ge_int(R, n): good = True
        for x in lmoves(R):
            if t == 'int' and ge_int(x, n): good = True
            if t == 'half' and ge_half(x, n): good = True
            if t == 'star' and ge_star(x, n): good = True
        if not good: return False
    if t == 'int': return n == 0 or any(ge_int(q, n - 1) for q in lmoves(s))
    return any(ge_int(q, n) for q in lmoves(s))

def allpos(n):
    for f in range(n):
        cells = [i for i in range(n) if i != f]
        for mask in range(1 << (n - 1)):
            s = ['.'] * n; s[f] = 'F'
            for j, c in enumerate(cells):
                if mask >> j & 1: s[c] = 'T'
            yield ''.join(s)

if __name__ == '__main__':
    N = int(sys.argv[1]); bad = 0; claims = 0
    for n in range(1, N + 1):
        for s in allpos(n):
            for t, k in upper(s):
                claims += 1
                if k < 0 or not ok_upper(s, t, k):
                    bad += 1
                    if bad <= 30: print('UPPER fails', s, t, k, 'phi', phi(s), feat(s))
            for t, k in lower(s):
                claims += 1
                if k < 0 or not ok_lower(s, t, k):
                    bad += 1
                    if bad <= 30: print('LOWER fails', s, t, k, 'phi', phi(s), feat(s))
        print('length', n, 'claims so far', claims, 'failures', bad, flush=True)
