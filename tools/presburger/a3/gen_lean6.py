# Turn an invariant written by cegar6 into a plan for the Lean proof that it is closed under a Left move followed
# by a Right reply: for every (piece order, case, Left move), a decision tree over linear literals whose leaves
# name one Right reply and one target case.   Usage: python3 gen_lean6.py INV PLAN.pkl [NMAX] [PART/OF]
import sys, z3, pickle, time
from z3check6 import load, toad, coef, name
ORDERS = [c for c in range(64) if bin(c).count('1') == 3]
def ab_form(c): return tuple(coef(c, k) for k in range(7))
def E(k): return tuple(1 if i == k else 0 for i in range(7))
ONES = (1,) * 7
# literal: (form, op, m, v) with op in ge, le, eq, mod, nmod
def neg(l):
    a, op, m, v = l
    return {'ge': (a, 'le', 0, v - 1), 'le': (a, 'ge', 0, v + 1), 'mod': (a, 'nmod', m, v), 'nmod': (a, 'mod', m, v)}[op]
def subst(l, d):   # a literal about g + d, rewritten as a literal about g
    a, op, m, v = l; s = sum(a[k] * d[k] for k in range(7))
    if op in ('mod', 'nmod'): return (a, op, m, (v - s) % m)
    return (a, op, m, v - s)
G = [z3.Int('g%d' % k) for k in range(7)]
def lit_z3(l):
    a, op, m, v = l; F = sum(a[k] * G[k] for k in range(7) if a[k])
    if op == 'ge': return F >= v
    if op == 'le': return F <= v
    if op == 'eq': return F == v
    if op == 'mod': return F % m == v
    return F % m != v
def build_cases(raw, nmax):
    """per order: list of cases; a case is (race count, [literals]); also the tree nodes with leaf -> case index"""
    cases = {c: [] for c in ORDERS}; leafcase = {}
    for (c, a), nodes in sorted(raw.items()):
        def rec(i, path):
            nd = nodes[i]
            if nd[0] == 'leaf':
                if nd[1] != 0: return
                lits = [(ab_form(c), 'eq', 0, a)] + path
                for k in range(7):
                    lo, hi = nd[2][2 * k], nd[2][2 * k + 1]
                    if lo > 0: lits.append((E(k), 'ge', 0, lo))
                    if hi < 127: lits.append((E(k), 'le', 0, hi))
                if nmax is not None: lits.append((ONES, 'le', 0, nmax))
                lits = list(dict.fromkeys(lits))
                s = z3.Solver(); s.add([x >= 0 for x in G]); s.add([lit_z3(l) for l in lits])
                if s.check() == z3.sat: leafcase[(c, a, i)] = len(cases[c]); cases[c].append((a, lits))
                return
            _, kind, f, m, v, y, n = nd
            t = (tuple(f), 'ge', 0, v) if kind == 0 else (tuple(f), 'mod', m, v)
            rec(y, path + [t]); rec(n, path + [neg(t)])
        rec(0, [])
    return cases, leafcase
def lmoves(c):
    out = []
    for i in range(6):
        if not toad(c, i): continue
        d = [0] * 7; d[i] += 1; d[i + 1] -= 1; out.append((i, 'slide', c, tuple(d), [(E(i + 1), 'ge', 0, 1)], -1))
        if i + 1 < 6 and not toad(c, i + 1):
            d = [0] * 7; d[i] += 1; d[i + 2] -= 1; out.append((i, 'jump', c ^ (3 << i), tuple(d), [(E(i + 1), 'le', 0, 0), (E(i + 2), 'ge', 0, 1)], -2))
    return out
def rmoves(c):
    out = []
    for i in range(6):
        if toad(c, i): continue
        d = [0] * 7; d[i] -= 1; d[i + 1] += 1; out.append((i, 'slide', c, tuple(d), [(E(i), 'ge', 0, 1)], 1))
        if i >= 1 and toad(c, i - 1):
            d = [0] * 7; d[i - 1] -= 1; d[i + 1] += 1; out.append((i, 'jump', c ^ (3 << (i - 1)), tuple(d), [(E(i), 'le', 0, 0), (E(i - 1), 'ge', 0, 1)], 2))
    return out
def addv(a, b): return tuple(x + y for x, y in zip(a, b))
class Region:
    def __init__(self, lits):
        self.s = z3.Solver(); self.s.add([x >= 0 for x in G]); self.s.add([lit_z3(l) for l in lits]); self.lits = list(lits)
    def sat(self): return self.s.check() == z3.sat
    def implies(self, l):
        self.s.push(); self.s.add(z3.Not(lit_z3(l))); r = self.s.check() == z3.unsat; self.s.pop(); return r
    def model_with(self, lits_list):
        """a model of the region satisfying one of the conjunctions (as z3 formula), or None"""
        self.s.push(); self.s.add(lits_list); r = self.s.check(); m = self.s.model() if r == z3.sat else None; self.s.pop(); return m
    def extend(self, l): return Region(self.lits + [l])
def member_z3(raw, c, a, d):
    """the tree of slice (c, a) evaluated at g + d, as a z3 formula"""
    nodes = raw.get((c, a))
    if not nodes: return None
    g = [G[k] + d[k] for k in range(7)]
    def rec(i):
        nd = nodes[i]
        if nd[0] == 'leaf':
            if nd[1] != 0: return z3.BoolVal(False)
            box = []
            for k in range(7):
                lo, hi = nd[2][2 * k], nd[2][2 * k + 1]
                if lo > 0: box.append(g[k] >= lo)
                if hi < 127: box.append(g[k] <= hi)
            return z3.And(box) if box else z3.BoolVal(True)
        _, kind, f, m, v, y, n = nd
        F = sum(f[k] * g[k] for k in range(7) if f[k])
        return z3.If(F >= v if kind == 0 else F % m == v, rec(y), rec(n))
    return rec(0)
NMAXLIT = None
def decompose(R, c2, a2, dL, raw, leafcase, depth=0):
    if not R.sat(): return ('dead',)
    if depth > 60: raise Exception('too deep')
    opts = []
    for (j, kind, c3, dR, condR, da) in rmoves(c2):
        a3 = a2 + da; dT = addv(dL, dR); M = member_z3(raw, c3, a3, dT)
        if M is None: continue
        cond = [subst(l, dL) for l in condR]
        opts.append((j, kind, c3, a3, dT, cond, M))
    def path_lits(c3, a3, dT, model):
        """walk the tree of the target slice at the model point: the literals (about g) that put g + dT in its leaf"""
        nodes = raw[(c3, a3)]; i = 0; out = []; val = [model.eval(G[k], model_completion=True).as_long() + dT[k] for k in range(7)]
        while nodes[i][0] != 'leaf':
            _, kind, f, m, v, y, n = nodes[i]; F = sum(f[k] * val[k] for k in range(7))
            t = (tuple(f), 'ge', 0, v) if kind == 0 else (tuple(f), 'mod', m, v)
            if (F >= v) if kind == 0 else (F % m == v): out.append(subst(t, dT)); i = y
            else: out.append(subst(neg(t), dT)); i = n
        nd = nodes[i]
        for k in range(7):
            lo, hi = nd[2][2 * k], nd[2][2 * k + 1]
            if lo > 0: out.append(subst((E(k), 'ge', 0, lo), dT))
            if hi < 127: out.append(subst((E(k), 'le', 0, hi), dT))
        return out, i
    for (j, kind, c3, a3, dT, cond, M) in opts:
        m = R.model_with([lit_z3(l) for l in cond] + [M])
        if m is None: continue
        need, leaf = path_lits(c3, a3, dT, m); need = cond + need
        for l in need:
            if not R.implies(l):
                return ('split', l, decompose(R.extend(l), c2, a2, dL, raw, leafcase, depth + 1), decompose(R.extend(neg(l)), c2, a2, dL, raw, leafcase, depth + 1))
        return ('leaf', j, kind, c3, leafcase[(c3, a3, leaf)])
    raise Exception('no reply for a region: the invariant is not closed')
def count(t): return 1 if t[0] == 'leaf' else 0 if t[0] == 'dead' else count(t[2]) + count(t[3])
if __name__ == '__main__':
    raw = load(sys.argv[1]); nmax = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else None
    part, of = (map(int, sys.argv[4].split('/')) if len(sys.argv) > 4 else (0, 1))
    cases, leafcase = build_cases(raw, nmax)
    print({name(c): len(cases[c]) for c in ORDERS}, 'total', sum(len(v) for v in cases.values())); sys.stdout.flush()
    plan = {}; total = 0; t0 = time.time(); fails = 0; job = 0
    for c in ORDERS:
        for (i, kind, c2, dL, condL, da) in lmoves(c):
            for s, (a, lits) in enumerate(cases[c]):
                job += 1
                if job % of != part: continue
                R = Region(lits + condL)
                try: t = decompose(R, c2, a + da, dL, raw, leafcase)
                except Exception as e: t = ('fail', str(e)); fails += 1; print('FAIL', name(c), i, kind, s, e)
                plan[(c, i, kind, s)] = t; total += count(t) if t[0] != 'fail' else 0
        print(name(c), 'done; leaves so far', total, 'time %.0fs' % (time.time() - t0)); sys.stdout.flush()
    print('total leaves', total, 'failures', fails)
    pickle.dump((cases, plan), open(sys.argv[2], 'wb'))
