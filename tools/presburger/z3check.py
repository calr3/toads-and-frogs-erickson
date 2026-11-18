import sys, z3
# orders: bitmask, bit i = piece i is a toad
ORD = {'TTFF': 3, 'TFTF': 5, 'FTTF': 6, 'TFFT': 9, 'FTFT': 10, 'FFTT': 12}
def toad(c, i): return (c >> i) & 1
def coef(c, k):
    tl = sum(1 for i in range(k) if toad(c, i)); fr = sum(1 for i in range(k, 4) if not toad(c, i)); return tl - fr
def ab(c, g): return sum(coef(c, k) * g[k] for k in range(5))
def passings(c):
    # number of (toad, frog) pairs with frog left of toad
    return sum(1 for i in range(4) for j in range(i) if toad(c, i) and not toad(c, j))
def load_tree(fn):
    lines = open(fn).read().split('\n'); c, n = map(int, lines[0].split()); nodes = {}
    for l in lines[1:]:
        if not l.strip(): continue
        p = l.split(); i = int(p[0])
        if p[1] == 'leaf': nodes[i] = ('leaf', int(p[2]))
        else: nodes[i] = ('test', int(p[2]), list(map(int, p[3:8])), int(p[8]), int(p[9]), int(p[10]), int(p[11]))
    return c, nodes
def tree_expr(nodes, c, g, want):  # expression: tree predicts `want` (0 = loss)
    def rec(i):
        nd = nodes[i]
        if nd[0] == 'leaf': return z3.BoolVal(nd[1] == want)
        _, kind, f, m, v, yes, no = nd
        F = sum(f[k] * g[k] for k in range(5))
        if kind == 0: t = F >= v
        elif kind == 1: t = (F % m) == v
        else: t = ab(c, g) >= v
        return z3.If(t, rec(yes), rec(no))
    return rec(0)
TREES = {}
def good(c, g):
    a = ab(c, g); P = passings(c)
    dom = z3.And(a >= -P, a <= P + 1)
    if c in TREES: return z3.And(dom, TREES[c](g))
    raise Exception("no formula for %d" % c)
def lmoves(c, g):  # list of (cond, c2, h)
    out = []
    for i in range(4):
        if not toad(c, i): continue
        if i + 1 <= 4:
            h = list(g); h[i] += 1; h[i+1] -= 1; out.append((g[i+1] > 0, c, h, i, 'slide'))
        if i + 1 < 4 and not toad(c, i + 1):
            h = list(g); h[i] += 1; h[i+2] -= 1; out.append((z3.And(g[i+1] == 0, g[i+2] > 0), c ^ (3 << i), h, i, 'jump'))
    return out
def rmoves(c, g):
    out = []
    for i in range(4):
        if toad(c, i): continue
        h = list(g); h[i] -= 1; h[i+1] += 1; out.append((g[i] > 0, c, h, i, 'slide'))
        if i >= 1 and toad(c, i - 1):
            h = list(g); h[i-1] -= 1; h[i+1] += 1; out.append((z3.And(g[i] == 0, g[i-1] > 0), c ^ (3 << (i - 1)), h, i, 'jump'))
    return out
def check(c):
    g = [z3.Int('g%d' % k) for k in range(5)]
    bad = 0
    for (cond, c2, h, i, kind) in lmoves(c, g):
        s = z3.Solver(); s.add([x >= 0 for x in g]); s.add(good(c, g)); s.add(cond)
        replies = [z3.And(cr, good(c3, r)) for (cr, c3, r, j, k2) in rmoves(c2, h)]
        s.add(z3.Not(z3.Or(replies)) if replies else z3.BoolVal(True))
        res = s.check()
        if res == z3.sat:
            m = s.model(); gv = [m.eval(x, model_completion=True).as_long() for x in g]
            print("  FAIL order %d Left %s of piece %d: counterexample %s ab=%d" % (c, kind, i, gv, sum(coef(c,k)*gv[k] for k in range(5)))); bad += 1
        elif res == z3.unknown: print("  UNKNOWN order %d Left %s %d" % (c, kind, i)); bad += 1
    return bad
