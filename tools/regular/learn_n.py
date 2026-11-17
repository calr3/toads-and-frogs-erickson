"""Given a normal-play invariant Z (from learn_z.py), learn N so that (N, Z) is an invariant
for the start positions of the given rows.

Usage: learn_n.py Z.json --rows 2 [--budget SEC] L1 L2 ... 0
"""
import argparse
import json
import os
import time
from learn import Learner
from folded import (DFA, fold, unfold, lm, rm, mirror, Np, check_all, starts_rows, minimize)


def add_n(Lr, f, Z):
    w = unfold(f)
    N = lambda g: Lr.var('N', g)
    if not Np(w):
        Lr.add([-N(f)])
        return

    def lits(q):  # None when q is in LF whatever N is
        if mirror(q) == q or Z.accepts(fold(q)):
            return None
        return [N(fold(r)) for r in rm(q) if Np(r)]
    for q in [w] + lm(w):
        l = lits(q)
        if l is not None:
            Lr.add([-N(f)] + l)


def search(Z, rows, bound, k, cexs, budget, kstep, solver):
    t0 = time.time()
    maxlen = bound // 2 if bound else None
    sdfa = starts_rows(rows)
    while True:
        Lr = Learner(k, solver)
        for kind, f in cexs:
            if kind == 'start':
                Lr.add([Lr.var('N', f)])
            else:
                add_n(Lr, f, Z)
        while True:
            res = Lr.solve(budget)
            if not res:
                print(f'    k={k} {"unsat" if res is False else "timeout"} after {len(cexs)} counterexamples '
                      f'({time.time()-t0:.0f}s)', flush=True)
                k += 1 if res is False else kstep
                break
            N, _ = Lr.model()
            found = check_all(N, Z, maxlen, 0, sdfa)
            assert all(kind != 'Z' for kind, _ in found), 'Z is not a normal-play invariant'
            if not found:
                return k, N
            for kind, f in found:
                cexs.append((kind, f))
                if kind == 'start':
                    Lr.add([Lr.var('N', f)])
                else:
                    add_n(Lr, f, Z)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('zfile')
    ap.add_argument('bounds', type=int, nargs='+')
    ap.add_argument('--rows', default='2')
    ap.add_argument('--k', type=int, default=1)
    ap.add_argument('--budget', type=float, default=None)
    ap.add_argument('--kstep', type=int, default=2)
    ap.add_argument('--solver', default='glucose4')
    args = ap.parse_args()
    zd = json.load(open(args.zfile))
    Z = DFA(zd['delta'], zd['acc'])
    rows = {int(x) for x in args.rows.split(',')}
    k, cexs = args.k, []
    for bound in args.bounds:
        t0 = time.time()
        k, N = search(Z, rows, bound, k, cexs, args.budget, args.kstep, args.solver)
        Nm = minimize(N)
        print(f'L={bound}: k={k} |N|={len(Nm)} counterexamples={len(cexs)} {time.time()-t0:.0f}s', flush=True)
        if os.environ.get('SAVE_DIR'):
            with open(os.path.join(os.environ['SAVE_DIR'], f'n_rows{args.rows}_L{bound}.json'), 'w') as fh:
                json.dump({'delta': Nm.delta, 'acc': Nm.acc}, fh)
