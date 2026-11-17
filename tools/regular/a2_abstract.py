"""Abstract check of Right's strategy from T.T .^m FF, for all m at once.

A shape is (order, g4-g0, g3-g1, cap(min(g0,g4)), cap(min(g1,g3)), cap(g2)) where
cap(x) = x for x < K and (K, x mod 2) otherwise.  One move changes each gap by at most 1, so
the shapes a move can lead to are found from two witnesses per capped component (the
smallest value with that parity, and the next one).  The strategy table maps the shape of a
Right-to-move position to Right's move type (which frog, slide or jump).

The check: starting from the shapes of T.T .^m FF (all m >= 1), every Left move from every
witness leads to a shape in the table, whose move type is legal for every witness of that
shape and leads back to a shape in the set.  If this closes, Right's strategy wins from
every T.T .^m FF, i.e. those positions are <= 0.
"""
import itertools
import sys
from a2_strategy import gaps, shape, reachable, move_type
from folded import lm

K = int(sys.argv[1]) if len(sys.argv) > 1 else 4


def pos(order, g):
    s = '.' * g[0]
    for k, c in enumerate(order):
        s += c + '.' * g[k + 1]
    return s


def witnesses(a):
    o, d0, d1, c0, c1, c2 = a
    def vals(c):
        if isinstance(c, tuple):
            v = K if K % 2 == c[1] else K + 1
            return [v, v + 2]
        return [c]
    out = []
    for m0, m1, g2 in itertools.product(vals(c0), vals(c1), vals(c2)):
        g0, g4 = (m0, m0 + d0) if d0 >= 0 else (m0 - d0, m0)
        g1, g3 = (m1, m1 + d1) if d1 >= 0 else (m1 - d1, m1)
        out.append(pos(o, (g0, g1, g2, g3, g4)))
    return out


def apply_type(q, t):
    """Apply Right's move type t = (frog 1 or 2, distance 1 or 2) to q, or None."""
    fr = [i for i, c in enumerate(q) if c == 'F']
    i = fr[t[0] - 1]
    if t[1] == 1 and i >= 1 and q[i - 1] == '.':
        return q[:i - 1] + 'F.' + q[i + 1:]
    if t[1] == 2 and i >= 2 and q[i - 1] == 'T' and q[i - 2] == '.':
        return q[:i - 2] + 'FT.' + q[i + 1:]
    return None


if __name__ == '__main__':
    table = {}
    for m in range(1, 41):
        _, ch = reachable(m)
        for q, r in ch:
            table.setdefault(shape(q, K), move_type(q, r))
    start = {shape('T.T' + '.' * m + 'FF', K) for m in range(1, K + 3)}
    seen, todo, problems = set(start), list(start), []
    while todo:
        a = todo.pop()
        for z in witnesses(a):
            for q in lm(z):
                aq = shape(q, K)
                t = table.get(aq)
                if t is None:
                    problems.append(('no strategy for shape', aq, q)); continue
                for qw in witnesses(aq):
                    r = apply_type(qw, t)
                    if r is None:
                        problems.append(('illegal reply', aq, qw, t)); continue
                    ar = shape(r, K)
                    if ar not in seen:
                        seen.add(ar); todo.append(ar)
    print(f'K={K}: {len(seen)} Left-to-move shapes, {len(table)} table entries, {len(problems)} problems')
    for p in problems[:10]:
        print('  ', p)
