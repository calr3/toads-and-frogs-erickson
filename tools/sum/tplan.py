"""Proof plans for families of positions T^(x+c) M F^(y+d), uniform in x, y >= 0.

A template is (c, M, d); c or d is None when that side has no symbolic reservoir. A claim is
(template, kind, (sx, sy, k), conds): for all x, y >= 0 satisfying conds, the position is
<= sx*x - sy*y + k (kind 'int') or <= {n | n} for that n (kind 'star'). conds is a tuple of
(sx, sy, k) meaning sx*x - sy*y + k < 0. Claims are tested on a grid of (x, y). A plan is built from

  NODE  the one-step rule: each Left move is 'direct' (the result is <= n - 1, or <= n for a star
        claim) or has a Right 'reply' with the same claim; a star claim also needs a Right option
        <= n, and an int claim whose bound can be negative a Right option <= n + 1;
  BR    the Blocking Rule: M = Ml FF Mr, and the parts T^(x+c) Ml and Mr F^(y+d) have bounds that
        add up to at most n (the parts are claims of their own);
  PURE  no frog, or no toad: the value is the number of moves;
  DEAD  one frog that can never move (TT in front of it and no empty square behind it);
  T1U   one frog: an upper bound of the one-frog theorem (Cgt/OneFrog);
  T1L   one toad: the mirror image of a lower bound of the one-frog theorem;
  HAND  a claim listed in HAND below, proved by hand.

Moves are described on templates, so a plan is the same for every x, y; reservoirs must keep at
least one piece (c, d >= 1), otherwise there is no plan and a larger c or d is needed.

Usage: python3 tplan.py C M D star|int K [GRID]     (C, D: an integer or '-')
"""
import sys, pickle
from functools import lru_cache
sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/onefrog')
from explore import le_int, le_star, ub, lb
from bounds import phi
sys.setrecursionlimit(1000000)
GRID = 3
NEED = False  # NEED=1 in the environment: accept uncovered one-frog / one-toad claims with a reservoir, at a high cost, and list them
HAND = set()      # (template, (sx, sy, k)) accepted without a plan

def inst(t, x, y):
    c, M, d = t
    return ('T' * (x + c) if c is not None else '') + M + ('F' * (y + d) if d is not None else '')
def params(t, conds=()):
    c, M, d = t
    out = []
    # conditions sx*x - sy*y + k < 0 push y up (or x down): widen the grid so that they can be met
    ext = max([k + 1 for sx, sy, k in conds if sy > 0] + [0])
    for x in (range(GRID + 1) if c is not None else [0]):
        for y in (range(GRID + 1 + ext) if d is not None else [0]):
            if all(sx * x - sy * y + k < 0 for sx, sy, k in conds): out.append((x, y))
    return out
def val(b, x, y): return b[0] * x - b[1] * y + b[2]
def shift(b, e): return (b[0], b[1], b[2] + e)

def lmoves(t):
    c, M, d = t; out = []
    if c is not None:
        if M[:1] == '.': out.append(('res', (c - 1, '.T' + M[1:], d)))
        elif M[:2] == 'F.': out.append(('res', (c - 1, '.FT' + M[2:], d)))
    for i, ch in enumerate(M):
        if ch == 'T':
            if i + 1 < len(M) and M[i+1] == '.': out.append((i, (c, M[:i] + '.T' + M[i+2:], d)))
            elif i + 2 < len(M) and M[i+1] == 'F' and M[i+2] == '.': out.append((i, (c, M[:i] + '.FT' + M[i+3:], d)))
    return out
def rmoves(t):
    c, M, d = t; out = []
    if d is not None:
        if M[-1:] == '.': out.append(('res', (c, M[:-1] + 'F.', d - 1)))
        elif M[-2:] == '.T': out.append(('res', (c, M[:-2] + 'FT.', d - 1)))
    for i, ch in enumerate(M):
        if ch == 'F':
            if i >= 1 and M[i-1] == '.': out.append((i, (c, M[:i-1] + 'F.' + M[i+1:], d)))
            elif i >= 2 and M[i-1] == 'T' and M[i-2] == '.': out.append((i, (c, M[:i-2] + 'FT.' + M[i+1:], d)))
    return out
def valid(t):
    c, M, d = t
    if c is not None and (c < 1 or M[:1] == 'T'): return False
    if d is not None and (d < 1 or M[-1:] == 'F'): return False
    return True

def holds(t, kind, b, conds):
    for x, y in params(t, conds):
        p = inst(t, x, y); n = val(b, x, y)
        if not (le_star(p, n) if kind == 'star' else le_int(p, n)): return False
    return True

def mirror(s): return ''.join({'T': 'F', 'F': 'T', '.': '.'}[ch] for ch in reversed(s))
def feat(s):
    f = s.index('F'); left = s[:f]
    m = left.count('T'); rho = s[f+1:].count('.')
    if m == 0: return 0, None, None
    xm = left.rindex('T')
    return m, rho - left[:xm].count('.'), f - 1 - xm
def t1_upper(s):
    """(name, bound) of the one-frog theorem's upper bound for s, or None."""
    m, room, gap = feat(s); p = phi(s)
    if m == 0: return ('u0', max(p, 0))
    if room >= 2 or (room == 1 and gap % 2 == 0): return ('u1', p)
    if room == 1: return ('u3', p + 1)
    if room == 0 and gap % 2 == 0: return ('u4', max(p + 1, 0))
    if room == 0 and p >= 0: return ('u5', p + 2)
    if room == -1 and gap == 0 and p >= -1: return ('u6', p + 2)
    return None
def t1_lower(s):
    m, room, gap = feat(s); p = phi(s)
    if m >= 1 and (room <= -2 or (room == -1 and gap % 2 == 0)) and p + 2 >= 0: return ('lower2', p + 2)
    if m >= 1 and (room <= -1 or (room == 0 and gap % 2 == 0)) and p + 1 >= 0: return ('lower1', p + 1)
    if p >= 0: return ('lower0', p)
    return None
def dead(s):
    f = s.index('F')
    return f >= 2 and s[f-1] == 'T' and s[f-2] == 'T' and '.' not in s[f+1:]

def leaf(t, b, conds):
    """A leaf justification for the int claim, or None."""
    c, M, d = t
    if (t, b) in HAND: return ('HAND',)
    ps = params(t, conds)
    if not ps: return ('EMPTY',)
    if c is not None and d is not None: return None
    s1 = inst(t, 1, 1)
    if s1.count('F') == 0 or s1.count('T') == 0: return ('PURE',)
    if s1.count('F') == 1 and d is None:
        if all(dead(inst(t, x, y)) for x, y in ps): return ('DEAD',)
        names = set(); good = True
        for x, y in ps:
            r = t1_upper(inst(t, x, y))
            if r is None or r[1] > val(b, x, y): good = False; break
            names.add(r[0])
        if good and len(names) == 1: return ('T1U', sorted(names)[0])
        return ('NEED',) if NEED and c is not None else None
    if s1.count('T') == 1 and c is None:
        names = set(); good = True
        for x, y in ps:
            r = t1_lower(mirror(inst(t, x, y)))
            if r is None or r[1] < -val(b, x, y): good = False; break
            names.add(r[0])
        if good and len(names) == 1: return ('T1L', sorted(names)[0])
        return ('NEED',) if NEED and d is not None else None
    return None

def fit(f, has):
    if not has: return (0, f(0))
    pts = [(v, f(v)) for v in range(GRID + 1)]
    a = pts[1][1] - pts[0][1]; b0 = pts[0][1]
    return (a, b0) if all(w == a * v + b0 for v, w in pts) else None
def splits(t):
    c, M, d = t; out = []
    for i in range(len(M) - 1):
        if M[i] == 'F' and M[i+1] == 'F': out.append(((c, M[:i], None), (None, M[i+2:], d)))
    return out

BIG = 10**9
@lru_cache(maxsize=None)
def cost(t, kind, b, conds):
    if not valid(t): return (BIG, None)
    if not holds(t, kind, b, conds): return (BIG, None)
    c, M, d = t
    if kind == 'int':
        lf = leaf(t, b, conds)
        if lf and lf[0] != 'NEED': return (1, lf)
        if lf: return (40, lf)
        best = (BIG, None)
        for Xt, Yt in splits(t):
            fx = fit(lambda x: ub(inst(Xt, x, 0)), c is not None)
            fy = fit(lambda y: ub(inst(Yt, 0, y)), d is not None)
            if fx is None or fy is None or fy[0] > 0: continue
            bx = (fx[0], 0, fx[1]); by = (0, -fy[0], fy[1])
            if not all(val(bx, x, y) + val(by, x, y) <= val(b, x, y) for x, y in params(t, conds)): continue
            if fx[0] > b[0] or -fy[0] < b[1]: continue      # the inequality must hold for all x, y, not only on the grid
            cx = cost(Xt, 'int', bx, ()); cy = cost(Yt, 'int', by, ())
            if cx[0] + cy[0] + 1 < best[0]: best = (cx[0] + cy[0] + 1, ('BR', Xt, bx, Yt, by))
        if best[0] < BIG and best[0] <= 3: return best
    else: best = (BIG, None)
    total = 1; steps = []
    for name, q in lmoves(t):
        bst = (BIG, None)
        c1 = cost(q, 'int', shift(b, -1) if kind == 'int' else b, conds)
        if c1[0] < bst[0]: bst = (c1[0], ('direct', name, q))
        for rn, r in rmoves(q):
            cc = cost(r, kind, b, conds)
            if cc[0] < bst[0]: bst = (cc[0], ('reply', name, q, rn, r))
        if bst[0] >= BIG: total = BIG; break
        total += bst[0]; steps.append(bst[1])
    ropt = None
    if total < BIG:
        if kind == 'star':
            bb = (BIG, None)
            for rn, r in rmoves(t):
                cc = cost(r, 'int', b, conds)
                if cc[0] < bb[0]: bb = (cc[0], (rn, r, b, conds))
            if bb[0] >= BIG: total = BIG
            else: total += bb[0]; ropt = bb[1]
        else:
            c2 = conds + (b,) if b not in conds else conds
            if (b[1] > 0 and d is not None) or b[2] < 0 or (b[0] == 0 and b[2] < 0):
                if params(t, c2) or (b[1] > 0 and d is not None):
                    bb = (BIG, None)
                    for rn, r in rmoves(t):
                        cc = cost(r, 'int', shift(b, 1), c2)
                        if cc[0] < bb[0]: bb = (cc[0], (rn, r, shift(b, 1), c2))
                    if bb[0] >= BIG: total = BIG
                    else: total += bb[0]; ropt = bb[1]
    if total < best[0]: return (total, ('NODE', steps, ropt))
    return best

def tname(t):
    c, M, d = t
    return ('' if c is None else f'T^(x+{c}) ') + (M or '-') + ('' if d is None else f' F^(y+{d})')
def bname(b): return f'{b[0]}x-{b[1]}y+{b[2]}'
nodes = {}
def collect(t, kind, b, conds):
    key = (t, kind, b, conds)
    if key in nodes: return
    plan = cost(t, kind, b, conds)[1]; nodes[key] = plan
    if plan[0] == 'BR':
        collect(plan[1], 'int', plan[2], ()); collect(plan[3], 'int', plan[4], ())
    if plan[0] != 'NODE': return
    for st in plan[1]:
        if st[0] == 'direct': collect(st[2], 'int', shift(b, -1) if kind == 'int' else b, conds)
        else: collect(st[4], kind, b, conds)
    if plan[2]: collect(plan[2][1], 'int', plan[2][2], plan[2][3])

def failures(t, kind, b, conds, depth=0, seen=None, out=None):
    """True claims without a plan that have no smaller such claim below them."""
    if seen is None: seen, out = set(), []
    key = (t, kind, b, conds)
    if key in seen or not valid(t) or not holds(t, kind, b, conds) or cost(*key)[0] < BIG: return out
    seen.add(key); sub = False
    for name, q in lmoves(t):
        for cl in [(q, 'int', shift(b, -1) if kind == 'int' else b, conds)] + [(r, kind, b, conds) for rn, r in rmoves(q)]:
            if valid(cl[0]) and holds(*cl) and cost(*cl)[0] >= BIG:
                sub = True; failures(*cl, depth + 1, seen, out)
    if not sub: out.append(key)
    return out

if __name__ == '__main__':
    import os
    NEED = bool(os.environ.get('NEED'))
    a = sys.argv[1:]
    c = None if a[0] == '-' else int(a[0]); M = a[1]; d = None if a[2] == '-' else int(a[2])
    kind = a[3]; k = int(a[4])
    if len(a) > 5: GRID = int(a[5])
    t = (c, M, d); b = (1 if c is not None else 0, 1 if d is not None else 0, k)
    r = cost(t, kind, b, ())
    if r[0] >= BIG:
        print('NO PLAN. Claims that hold on the grid but have no plan (deepest):')
        for key in failures(t, kind, b, ())[:25]: print('  ', tname(key[0]), key[1], bname(key[2]), key[3])
        sys.exit(1)
    collect(t, kind, b, ())
    kinds = {}
    for p in nodes.values(): kinds[p[0]] = kinds.get(p[0], 0) + 1
    print(f'plan size {r[0]}; distinct claims {len(nodes)}: {kinds}')
    for key, p in nodes.items():
        if p[0] in ('NEED', 'HAND'): print('  leaf', p, tname(key[0]), '<=', bname(key[2]))
    pickle.dump(nodes, open('/tmp/t3/plan.pkl', 'wb'))
