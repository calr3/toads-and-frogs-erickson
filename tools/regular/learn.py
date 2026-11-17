"""Counterexample-guided search for a small automaton invariant (N, Z) on the folded board.

A SAT solver proposes a k-state DFA with two acceptance flags (N and Z) consistent with the
constraints collected so far; `folded.check` either accepts it or returns a shortest
counterexample word, whose constraints are added.  When the constraints become unsatisfiable,
k grows.  With a length bound L the search only has to be right on boards of <= L cells.

Usage: learn.py [--n0 N] [--k K] [--budget SEC --solver glucose4] L1 L2 ...
(even bounds; 0 means no bound)
"""
import json
import os
import sys
import threading
import time
from pysat.solvers import Solver
from folded import (ORIENT, NLET, DFA, fold, unfold, lm, rm, mirror, le0, Np, check, check_all, starts_rows, minimize, word_str)


class Learner:
    def __init__(self, k, solver='cadical195'):
        self.k = k; self.nv = 0
        self.S = Solver(name=solver)
        self.d = [[[self.new() for _ in range(k)] for _ in range(NLET)] for _ in range(k)]
        for s in range(k):
            for a in range(NLET):
                v = self.d[s][a]
                self.S.add_clause(v)
                for i in range(k):
                    for j in range(i + 1, k):
                        self.S.add_clause([-v[i], -v[j]])
        self._bfs_symmetry_breaking()
        self.acc = {'N': [self.new() for _ in range(k)], 'Z': [self.new() for _ in range(k)]}
        root = [self.new() for _ in range(k)]
        self.S.add_clause([root[0]])
        for s in range(1, k):
            self.S.add_clause([-root[s]])
        self.x = {(): root}
        self.w = {'N': {}, 'Z': {}}

    def _bfs_symmetry_breaking(self):
        """Number the states in breadth-first order (Ulyantsev, Zakirzyanov, Shalyto 2015)."""
        k, d, add = self.k, self.d, self.S.add_clause
        if k <= 1:
            return
        t = {(i, j): self.new() for i in range(k) for j in range(i + 1, k)}
        for (i, j), v in t.items():           # t_ij <-> some transition i -> j
            add([-v] + [d[i][a][j] for a in range(NLET)])
            for a in range(NLET):
                add([v, -d[i][a][j]])
        par = {(j, i): self.new() for j in range(1, k) for i in range(j)}
        for j in range(1, k):                 # parent of j = least i with a transition i -> j
            add([par[j, i] for i in range(j)])
            for i in range(j):
                v = par[j, i]
                add([-v, t[i, j]])
                for i2 in range(i):
                    add([-v, -t[i2, j]])
                add([v, -t[i, j]] + [t[i2, j] for i2 in range(i)])
        for j in range(1, k - 1):             # parents are non-decreasing
            for i in range(j):
                for i2 in range(i):
                    add([-par[j, i], -par[j + 1, i2]])
        m = {}
        for i in range(k):                    # m_iaj: a is the least letter with i -> j
            for j in range(i + 1, k):
                for a in range(NLET):
                    v = m[i, a, j] = self.new()
                    add([-v, d[i][a][j]])
                    for b in range(a):
                        add([-v, -d[i][b][j]])
                    add([v, -d[i][a][j]] + [d[i][b][j] for b in range(a)])
        for j in range(1, k - 1):             # siblings ordered by their least letter
            for i in range(j):
                for a in range(NLET):
                    for b in range(a):
                        add([-par[j, i], -par[j + 1, i], -m[i, a, j], -m[i, b, j + 1]])

    def new(self):
        self.nv += 1
        return self.nv

    def node(self, f):
        if f in self.x:
            return self.x[f]
        p = self.node(f[:-1]); a = f[-1]
        v = [self.new() for _ in range(self.k)]
        for s in range(self.k):
            for t in range(self.k):
                self.S.add_clause([-p[s], -self.d[s][a][t], v[t]])
        self.x[f] = v
        return v

    def var(self, which, f):
        tab = self.w[which]
        if f not in tab:
            v = self.node(f); acc = self.acc[which]; w = self.new()
            for s in range(self.k):
                self.S.add_clause([-v[s], -acc[s], w])
                self.S.add_clause([-v[s], acc[s], -w])
            tab[f] = w
        return tab[f]

    def add(self, clause):
        self.S.add_clause(clause)

    def solve(self, budget=None):
        """True / False, or None if the time budget ran out."""
        if budget is None:
            return self.S.solve()
        timer = threading.Timer(budget, self.S.interrupt)
        timer.start()
        try:
            res = self.S.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
            self.S.clear_interrupt()
        return res

    def model(self):
        m = {l for l in self.S.get_model() if l > 0}
        delta = [[next(t for t in range(self.k) if self.d[s][a][t] in m) for a in range(NLET)]
                 for s in range(self.k)]
        return (DFA(delta, [v in m for v in self.acc['N']]),
                DFA(delta, [v in m for v in self.acc['Z']]))


def add_constraints(Lr, f):
    """Clauses saying: if f is in N (resp. Z), it satisfies the invariant conditions."""
    w = unfold(f)
    N = lambda g: Lr.var('N', g)
    Z = lambda g: Lr.var('Z', g)
    if not Np(w):
        Lr.add([-N(f)])
    if not le0(w):
        Lr.add([-Z(f)])

    def lf_lits(q):  # disjunction for "q ∈ LF"; None if q is symmetric
        if mirror(q) == q:
            return None
        return ([Z(fold(q))] if le0(q) else []) + [N(fold(r)) for r in rm(q) if Np(r)]

    if Np(w):
        lits = lf_lits(w)
        if lits is not None:
            Lr.add([-N(f)] + lits)
        for q in lm(w):
            lits = lf_lits(q)
            if lits is not None:
                Lr.add([-N(f)] + lits)
    if le0(w):
        for q in lm(w):
            Lr.add([-Z(f)] + [Z(fold(r)) for r in rm(q) if le0(r)])


def search(bound, k, cexs, n0=0, budget=None, kstep=4, solver='glucose4', tlimit=None, log=True,
           rows=None):
    """Find an invariant valid on boards of n0..bound cells (bound 0: no upper bound).

    Each SAT call gets `budget` seconds (None: unlimited).  A call that runs out of time
    raises k by kstep; an unsatisfiable one raises k by 1.  Returns (k, N, Z) or None."""
    t0 = time.time()
    maxlen = bound // 2 if bound else None
    starts = [fold('T' * a + '.' * (n - 2 * a) + 'F' * a)
              for n in range(n0, bound + 1) for a in range(n // 2 + 1)]
    starts = [s for s in starts if unfold(s) != 'TTT..FFF'
              and (rows is None or unfold(s).count('T') in rows)]
    sdfa = starts_rows(rows) if rows else None
    while True:
        Lr = Learner(k, solver)
        for s in starts:
            Lr.add([Lr.var('N', s)])
        for kind, f in cexs:
            if kind == 'start':
                Lr.add([Lr.var('N', f)])
            else:
                add_constraints(Lr, f)
        while True:
            if tlimit and time.time() - t0 > tlimit:
                return None
            res = Lr.solve(budget)
            if not res:
                if log:
                    why = 'unsat' if res is False else 'timeout'
                    print(f'    k={k} {why} after {len(cexs)} counterexamples ({time.time()-t0:.0f}s)', flush=True)
                k += 1 if res is False else kstep
                break
            N, Z = Lr.model()
            found = check_all(N, Z, maxlen, n0, sdfa)
            if not found:
                return k, N, Z
            for cex in found:
                cexs.append(cex)
                if cex[0] == 'start':
                    Lr.add([Lr.var('N', cex[1])])
                else:
                    add_constraints(Lr, cex[1])


def first_failure(N, Z, n0, upto, rows=None):
    """Board size of the shortest counterexample for (N, Z), or None if none up to `upto`."""
    cex = check(N, Z, upto // 2, n0, starts_rows(rows) if rows else None)
    if cex is None:
        return None
    return len(unfold(cex[1]))


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('bounds', type=int, nargs='+')
    ap.add_argument('--n0', type=int, default=0)
    ap.add_argument('--k', type=int, default=1)
    ap.add_argument('--budget', type=float, default=None)
    ap.add_argument('--kstep', type=int, default=4)
    ap.add_argument('--solver', default='cadical195')
    ap.add_argument('--rows', type=str, default=None, help='comma-separated values of a')
    args = ap.parse_args()
    k, cexs, n0 = args.k, [], args.n0
    rows = {int(x) for x in args.rows.split(',')} if args.rows else None
    for bound in args.bounds:
        t0 = time.time()
        res = search(bound, k, cexs, n0=n0, budget=args.budget, kstep=args.kstep, solver=args.solver,
                     rows=rows)
        k, N, Z = res
        if os.environ.get('SAVE_DIR'):
            tag = f'_rows{args.rows}' if rows else ''
            path = os.path.join(os.environ['SAVE_DIR'], f'inv_{ORIENT}_n{n0}_L{bound}{tag}.json')
            with open(path, 'w') as fh:
                json.dump({'orient': ORIENT, 'n0': n0, 'bound': bound, 'delta': N.delta,
                           'accN': N.acc, 'accZ': Z.acc}, fh)
        ff = first_failure(N, Z, n0, 40, rows)
        print(f'L={bound}: k={k}  |N|={len(minimize(N))} |Z|={len(minimize(Z))}  '
              f'counterexamples={len(cexs)}  first failure on {ff}-cell boards  '
              f'{time.time()-t0:.0f}s', flush=True)
