# Z3 check that the invariant `good` (tree files + the TTFF families) is closed under play:
# from every position in `good` with Left to move, every Left move has a Right reply back into `good`.
# Board size is unbounded: the gaps are free nonnegative integers.  Usage: python3 verify.py
from z3check import *
import z3, sys
# Contact region of TTFF: centre gap at most K.
K = 1; t3 = 'tree3.txt'
files = {3: t3, 5: 'tree5.txt', 6: 'tree6.txt', 9: 'tree9.txt', 10: 'tree10.txt', 12: 'tree12.txt'}
for c, fn in files.items():
    cc, nodes = load_tree(fn); assert cc == c
    if c == 3:
        def mk(nodes, c):
            def f(g):
                N = g[0] + g[1] + g[2] + g[3] + g[4]; a = ab(c, g)
                P0 = z3.And(a == 0, g[4] == 0, N >= 9, z3.Or(N % 6 == 3, N % 6 == 5))
                P1 = z3.And(a == 1, g[4] == 0, N >= 7, N % 6 == 1)
                Ct = z3.And(g[2] <= K, z3.Or(a == 0, a == 1), tree_expr(nodes, c, g, 0))
                return z3.Or(P0, P1, Ct)
            return f
        TREES[c] = mk(nodes, c)
    else: TREES[c] = (lambda nodes, c: (lambda g: tree_expr(nodes, c, g, 0)))(nodes, c)
tot = 0
for c in [12, 10, 9, 6, 5, 3]:
    b = check(c); print("order", c, "failures", b); tot += b
print("total", tot)
