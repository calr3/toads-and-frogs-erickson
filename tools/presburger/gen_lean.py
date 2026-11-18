# Generate the Lean proof that the invariant `inv2` is closed under a Left move followed by a Right reply.
# Cells (conjunctions of linear literals) per piece order come from the decision trees; Z3 decomposes each
# (order, Left move, source cell) into regions with a single Right reply and a single target cell.
import sys, z3, json
from z3check import load_tree, coef, toad, passings
ORDERS = [3, 5, 6, 9, 10, 12]
ONAME = {3: 'TTFF', 5: 'TFTF', 6: 'FTTF', 9: 'TFFT', 10: 'FTFT', 12: 'FFTT'}
def bools(c): return [bool((c >> i) & 1) for i in range(4)]
# literal: (a tuple of 5 ints, op, m, v); ops: ge, le, eq, ne, mod, nmod
def lit_z3(l, g):
    a, op, m, v = l; F = sum(a[k] * g[k] for k in range(5))
    if op == 'ge': return F >= v
    if op == 'le': return F <= v
    if op == 'eq': return F == v
    if op == 'ne': return F != v
    if op == 'mod': return F % m == v
    if op == 'nmod': return F % m != v
    raise Exception(op)
def neg(l):
    a, op, m, v = l
    return {'ge': (a, 'le', 0, v - 1), 'le': (a, 'ge', 0, v + 1), 'eq': (a, 'ne', 0, v), 'ne': (a, 'eq', 0, v),
            'mod': (a, 'nmod', m, v), 'nmod': (a, 'mod', m, v)}[op]
def subst(l, d):  # literal over r = g + d, rewritten over g
    a, op, m, v = l; s = sum(a[k] * d[k] for k in range(5))
    if op in ('mod', 'nmod'): return (a, op, m, (v - s) % m)
    return (a, op, m, v - s)
def form_lean(a, names):
    parts = []
    for k in range(5):
        if a[k] == 0: continue
        t = f"({names[k]}:Int)" if abs(a[k]) == 1 else f"{abs(a[k])} * ({names[k]}:Int)"
        if not parts: parts.append(('-' if a[k] < 0 else '') + t)
        else: parts.append((' - ' if a[k] < 0 else ' + ') + t)
    return ''.join(parts) if parts else '0'
def lit_lean(l, names):
    a, op, m, v = l; F = form_lean(a, names)
    if op == 'ge': return f"{F} ≥ {v}"
    if op == 'le': return f"{F} ≤ {v}"
    if op == 'eq': return f"{F} = {v}"
    if op == 'ne': return f"{F} ≠ {v}"
    if op == 'mod': return f"({F}) % {m} = {v}"
    if op == 'nmod': return f"({F}) % {m} ≠ {v}"
E = lambda k: tuple(1 if i == k else 0 for i in range(5))
ONES = (1, 1, 1, 1, 1)
def ab_form(c): return tuple(coef(c, k) for k in range(5))
def tree_cells(c, fn, want=0):
    cc, nodes = load_tree(fn); assert cc == c
    out = []
    def rec(i, path):
        nd = nodes[i]
        if nd[0] == 'leaf':
            if nd[1] == want: out.append(list(path))
            return
        _, kind, f, m, v, yes, no = nd
        if kind == 0: t = (tuple(f), 'ge', 0, v)
        elif kind == 1: t = (tuple(f), 'mod', m, v)
        else: t = (ab_form(c), 'ge', 0, v)
        rec(yes, path + [t]); rec(no, path + [neg(t)])
    rec(0, []); return out
G = [z3.Int('g%d' % k) for k in range(5)]
NONNEG = [x >= 0 for x in G]
def sat(lits):
    s = z3.Solver(); s.add(NONNEG); s.add([lit_z3(l, G) for l in lits]); return s.check() == z3.sat
def implies(lits, l):
    s = z3.Solver(); s.add(NONNEG); s.add([lit_z3(x, G) for x in lits]); s.add(z3.Not(lit_z3(l, G))); return s.check() == z3.unsat
def to_eq(cell):
    """Replace a bound by an equality when the cell implies the opposite bound (omega handles equalities exactly)."""
    out = []
    for l in cell:
        a, op, m, v = l
        if op == 'ge' and implies(cell, (a, 'le', 0, v)): l = (a, 'eq', 0, v)
        elif op == 'le' and implies(cell, (a, 'ge', 0, v)): l = (a, 'eq', 0, v)
        out.append(l)
    return list(dict.fromkeys(out))
def simplify(cell):
    cell = to_eq(list(dict.fromkeys(cell))); changed = True
    while changed:
        changed = False
        for i in range(len(cell)):
            rest = cell[:i] + cell[i+1:]
            if implies(rest, cell[i]): cell = rest; changed = True; break
    return to_eq(cell)
def build_cells():
    cells = {}
    for c in ORDERS:
        P = passings(c); dom = [(ab_form(c), 'ge', 0, -P), (ab_form(c), 'le', 0, P + 1)]
        if c == 3:
            a = ab_form(3); cs = []
            cs.append([(a, 'eq', 0, 0), (E(4), 'eq', 0, 0), (ONES, 'ge', 0, 9), (ONES, 'mod', 6, 3)])
            cs.append([(a, 'eq', 0, 0), (E(4), 'eq', 0, 0), (ONES, 'ge', 0, 9), (ONES, 'mod', 6, 5)])
            cs.append([(a, 'eq', 0, 1), (E(4), 'eq', 0, 0), (ONES, 'ge', 0, 7), (ONES, 'mod', 6, 1)])
            for path in tree_cells(3, 'tree3.txt'):
                for abv in (0, 1): cs.append([(E(2), 'le', 0, 1), (a, 'eq', 0, abv)] + path)
        else:
            cs = [dom + p for p in tree_cells(c, 'tree%d.txt' % c)]
        out = []
        for cell in cs:
            if not sat(cell): continue
            out.append(simplify(cell))
        cells[c] = out
    return cells
# moves: (piece, kind, new order, delta, condition literals over the mover's position)
def lmoves(c):
    out = []
    for i in range(4):
        if not toad(c, i): continue
        d = [0] * 5; d[i] += 1; d[i + 1] -= 1; out.append((i, 'slide', c, tuple(d), [(E(i + 1), 'ge', 0, 1)]))
        if i + 1 < 4 and not toad(c, i + 1):
            d = [0] * 5; d[i] += 1; d[i + 2] -= 1; out.append((i, 'jump', c ^ (3 << i), tuple(d), [(E(i + 1), 'eq', 0, 0), (E(i + 2), 'ge', 0, 1)]))
    return out
def rmoves(c):
    out = []
    for i in range(4):
        if toad(c, i): continue
        d = [0] * 5; d[i] -= 1; d[i + 1] += 1; out.append((i, 'slide', c, tuple(d), [(E(i), 'ge', 0, 1)]))
        if i >= 1 and toad(c, i - 1):
            d = [0] * 5; d[i - 1] -= 1; d[i + 1] += 1; out.append((i, 'jump', c ^ (3 << (i - 1)), tuple(d), [(E(i), 'eq', 0, 0), (E(i - 1), 'ge', 0, 1)]))
    return out
def addv(a, b): return tuple(x + y for x, y in zip(a, b))
def decompose(R, c2, dL, cells, depth=0):
    """R: literals over the source position; Left's move gave order c2 with gaps g + dL. Returns a tree."""
    if not sat(R): return ('dead',)
    cands = []
    for (j, kind, c3, dR, condR) in rmoves(c2):
        cond = [subst(l, dL) for l in condR]; dT = addv(dL, dR)
        for t, T in enumerate(cells[c3]):
            Ts = [subst(l, dT) for l in T]
            need = cond + Ts
            if all(implies(R, l) for l in need): return ('leaf', j, kind, c3, dT, t)
            if sat(R + need): cands.append(need)
    if not cands or depth > 30: raise Exception("no reply for region %s" % (R,))
    need = cands[0]
    for l in need:
        if not implies(R, l):
            return ('split', l, decompose(R + [l], c2, dL, cells, depth + 1), decompose(R + [neg(l)], c2, dL, cells, depth + 1))
    raise Exception("unreachable")
def count(t):
    if t[0] == 'leaf': return 1
    if t[0] == 'dead': return 0
    return count(t[2]) + count(t[3])
if __name__ == '__main__':
    cells = build_cells()
    for c in ORDERS: print(ONAME[c], len(cells[c]), "cells, literals", sum(len(x) for x in cells[c]))
    plan = {}
    total = 0
    for c in ORDERS:
        for (i, kind, c2, dL, condL) in lmoves(c):
            trees = []
            for s, S in enumerate(cells[c]):
                R = S + condL
                t = decompose(R, c2, dL, cells) if sat(R) else ('dead',)
                trees.append(t); total += count(t)
            plan[(c, i, kind)] = trees
            print(ONAME[c], i, kind, "leaves", sum(count(t) for t in trees)); sys.stdout.flush()
    print("total leaves", total)
    import pickle; pickle.dump((cells, plan), open('plan.pkl', 'wb'))
