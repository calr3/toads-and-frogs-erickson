# Z3 check that an invariant written by cegar6 (one tree per piece order and race count, with a box on every
# "in" leaf) is closed: from every position of the invariant, every Left move has a Right reply in the invariant.
# The gaps are unbounded integers.   Usage: python3 z3check6.py INV [NMIN [NMAX]]
import sys, z3, collections, time
def toad(c, i): return (c >> i) & 1
def coef(c, k): return sum(1 for i in range(k) if toad(c, i)) - sum(1 for i in range(k, 6) if not toad(c, i))
def name(c): return ''.join('T' if toad(c, i) else 'F' for i in range(6))
def load(fn):
    sl = {}; cur = None
    for l in open(fn):
        p = l.split()
        if not p: continue
        if p[0] == 'slice': cur = {}; sl[(int(p[1]), int(p[2]))] = cur
        elif p[1] == 'leaf': cur[int(p[0])] = ('leaf', int(p[2]), list(map(int, p[3:])))
        else: cur[int(p[0])] = ('test', int(p[2]), list(map(int, p[3:10])), int(p[10]), int(p[11]), int(p[12]), int(p[13]))
    return sl
def cases(nodes):
    """the "in" leaves as lists of literals (f, op, v) / (f, 'mod', m, r, positive)"""
    out = []
    def rec(i, path):
        nd = nodes[i]
        if nd[0] == 'leaf':
            if nd[1] == 0:
                box = []
                for k in range(7):
                    lo, hi = nd[2][2 * k], nd[2][2 * k + 1]; e = [0] * 7; e[k] = 1
                    if lo > 0: box.append((e, '>=', lo))
                    if hi < 127: box.append((e, '<=', hi))
                out.append(path + box)
            return
        _, kind, f, m, v, y, n = nd
        if kind == 0: rec(y, path + [(f, '>=', v)]); rec(n, path + [(f, '<=', v - 1)])
        else: rec(y, path + [(f, 'mod', m, v, True)]); rec(n, path + [(f, 'mod', m, v, False)])
    rec(0, []); return out
def lit(l, g):
    F = sum(l[0][k] * g[k] for k in range(7) if l[0][k])
    if l[1] == '>=': return F >= l[2]
    if l[1] == '<=': return F <= l[2]
    return (F % l[2] == l[3]) if l[4] else (F % l[2] != l[3])
def ab(c, g): return sum(coef(c, k) * g[k] for k in range(7))
def member(SL, c, a, g):
    """g in the invariant, for piece order c and race count a (a constant)"""
    cs = SL.get((c, a))
    if not cs: return z3.BoolVal(False)
    return z3.Or([z3.And([lit(l, g) for l in case]) for case in cs])
def lmoves(c, g):
    out = []
    for i in range(6):
        if not toad(c, i): continue
        h = list(g); h[i] = h[i] + 1; h[i + 1] = h[i + 1] - 1; out.append((g[i + 1] > 0, c, h, i, 'slide'))
        if i + 1 < 6 and not toad(c, i + 1):
            h = list(g); h[i] = h[i] + 1; h[i + 2] = h[i + 2] - 1; out.append((z3.And(g[i + 1] == 0, g[i + 2] > 0), c ^ (3 << i), h, i, 'jump'))
    return out
def rmoves(c, g):
    out = []
    for i in range(6):
        if toad(c, i): continue
        h = list(g); h[i] = h[i] - 1; h[i + 1] = h[i + 1] + 1; out.append((g[i] > 0, c, h, i, 'slide'))
        if i >= 1 and toad(c, i - 1):
            h = list(g); h[i - 1] = h[i - 1] - 1; h[i + 1] = h[i + 1] + 1; out.append((z3.And(g[i] == 0, g[i - 1] > 0), c ^ (3 << (i - 1)), h, i, 'jump'))
    return out
if __name__ == '__main__':
    raw = load(sys.argv[1]); SL = {k: cases(v) for k, v in raw.items()}
    nmin = int(sys.argv[2]) if len(sys.argv) > 2 else 0; nmax = int(sys.argv[3]) if len(sys.argv) > 3 else None
    print(len(SL), 'slices,', sum(len(v) for v in SL.values()), 'cases')
    g = [z3.Int('g%d' % k) for k in range(7)]; N = sum(g); bad = 0; t0 = time.time()
    for (c, a), cs in sorted(SL.items()):
        for ci, case in enumerate(cs):
            pre = [x >= 0 for x in g] + [ab(c, g) == a, N >= nmin] + ([N <= nmax] if nmax else []) + [lit(l, g) for l in case]
            for (cond, c2, h, i, kind) in lmoves(c, g):
                s = z3.Solver(); s.add(pre); s.add(cond)
                da = -1 if kind == 'slide' else -2
                s.add(z3.Not(z3.Or([z3.And(cr, member(SL, c3, a + da + (1 if k2 == 'slide' else 2), r)) for (cr, c3, r, j, k2) in rmoves(c2, h)])))
                res = s.check()
                if res != z3.unsat:
                    bad += 1
                    if res == z3.sat:
                        m = s.model(); gv = [m.eval(x, model_completion=True).as_long() for x in g]
                        if bad <= 30: print('FAIL %s ab %d case %d, Left %s of piece %d: %s  N=%d' % (name(c), a, ci, kind, i, gv, sum(gv)))
                    else: print('UNKNOWN', name(c), a, ci)
    print('failures', bad, 'time %.0fs' % (time.time() - t0))
