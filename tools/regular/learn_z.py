"""Learn a normal-play invariant Z containing a given regular set P of positions <= 0.

Z must satisfy: every Left move from a position of Z has a Right reply back into Z, so every
position of Z (in particular of P) is <= 0.  Used for the a = 2 row, where P is the set of
positions at which Right passes under "mirror, otherwise pass".

Usage: learn_z.py [--budget SEC] L1 L2 ... 0     (bounds on board size; 0 = all boards)
"""
import argparse
import json
import os
import time
from learn import Learner
from folded import (NLET, DFA, VALID, PL, PR, PreTracker, _trans, _coreach, _bfs, _simple,
                    union, inter, compl, shortest, minimize, fold, unfold, lm, rm, le0, word_str)

# Pass positions of the a = 2 row (folded, read from the ends inwards):
#   A  _i T _{j+1} T F _j F _i          = (..)^i (TF) (..)^j (.F) (MT),   j >= 1
#   B  _i T _{j+1} F T _{j-1} F _i      = (..)^i (TF) (..)^m (.T) (.F),   m >= 0
#   C  _{i+1} T T _ F _ F _i            = (..)^i (.F) (T.) (TF) (M.)
EE, TF_, EF, ET, TE, MT, ME = 0, 5, 2, 1, 3, 10, 9
FAM_A = _simple({0: lambda a: {EE: 0, TF_: 1}.get(a, 'dead'), 1: lambda a: {EE: 2}.get(a, 'dead'),
                 2: lambda a: {EE: 2, EF: 3}.get(a, 'dead'), 3: lambda a: {MT: 4}.get(a, 'dead')}, 0, {4})
FAM_B = _simple({0: lambda a: {EE: 0, TF_: 1}.get(a, 'dead'), 1: lambda a: {EE: 1, ET: 2}.get(a, 'dead'),
                 2: lambda a: {EF: 3}.get(a, 'dead')}, 0, {3})
FAM_C = _simple({0: lambda a: {EE: 0, EF: 1}.get(a, 'dead'), 1: lambda a: {TE: 2}.get(a, 'dead'),
                 2: lambda a: {TF_: 3}.get(a, 'dead'), 3: lambda a: {ME: 4}.get(a, 'dead')}, 0, {4})
PASS2 = union(FAM_A, FAM_B, FAM_C)


def members(P, maxcells):
    """Words of P for boards of at most maxcells cells."""
    out = []
    frontier = [((), P.start)]
    for _ in range(maxcells // 2 + 1):
        nxt = []
        for f, s in frontier:
            if P.acc[s] and len(unfold(f)) <= maxcells:
                out.append(f)
            for a in range(NLET):
                t = P.delta[s][a]
                if t in _coreach(P):
                    nxt.append((f + (a,), t))
        frontier = nxt
    return out


def check_z(Z, P, maxlen=None):
    V = VALID
    BZ = PreTracker(Z, PR)
    liveZ = _coreach(Z)
    found = []

    def succ_z(st):
        v, z, t, b = st
        for a in range(NLET):
            z2 = Z.delta[z][a]
            if z2 in liveZ:
                v2 = V.delta[v][a]
                for o, t2 in _trans(PL, t, a):
                    yield a, (v2, z2, t2, BZ.step(b, o))
    w = _bfs((V.start, Z.start, 'p', BZ.start), succ_z,
             lambda st: V.acc[st[0]] and Z.acc[st[1]] and st[2] in ('q', 'e') and not BZ.acc(st[3]), maxlen)
    if w is not None:
        found.append(('Z', w))
    w = shortest(inter(P, compl(Z)), maxlen)
    if w is not None:
        found.append(('P', w))
    return found


def add_z(Lr, f):
    w = unfold(f)
    Z = lambda g: Lr.var('Z', g)
    if not le0(w):
        Lr.add([-Z(f)])
        return
    for q in lm(w):
        Lr.add([-Z(f)] + [Z(fold(r)) for r in rm(q) if le0(r)])


def search(P, bound, k, cexs, budget, kstep, solver):
    t0 = time.time()
    maxlen = bound // 2 if bound else None
    pos = members(P, bound) if bound else []
    while True:
        Lr = Learner(k, solver)
        for f in pos:
            Lr.add([Lr.var('Z', f)])
        for kind, f in cexs:
            if kind == 'P':
                Lr.add([Lr.var('Z', f)])
            else:
                add_z(Lr, f)
        while True:
            res = Lr.solve(budget)
            if not res:
                print(f'    k={k} {"unsat" if res is False else "timeout"} after {len(cexs)} counterexamples '
                      f'({time.time()-t0:.0f}s)', flush=True)
                k += 1 if res is False else kstep
                break
            _, Z = Lr.model()
            found = check_z(Z, P, maxlen)
            if not found:
                return k, Z
            for kind, f in found:
                cexs.append((kind, f))
                if kind == 'P':
                    Lr.add([Lr.var('Z', f)])
                else:
                    add_z(Lr, f)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('bounds', type=int, nargs='+')
    ap.add_argument('--k', type=int, default=1)
    ap.add_argument('--budget', type=float, default=None)
    ap.add_argument('--kstep', type=int, default=2)
    ap.add_argument('--solver', default='glucose4')
    args = ap.parse_args()
    k, cexs = args.k, []
    for bound in args.bounds:
        t0 = time.time()
        k, Z = search(PASS2, bound, k, cexs, args.budget, args.kstep, args.solver)
        Zm = minimize(Z)
        ff = check_z(Z, PASS2, 20)
        print(f'L={bound}: k={k} |Z|={len(Zm)} counterexamples={len(cexs)} '
              f'first failure: {min((len(unfold(f)) for _, f in ff), default=None)} cells  {time.time()-t0:.0f}s',
              flush=True)
        if os.environ.get('SAVE_DIR'):
            with open(os.path.join(os.environ['SAVE_DIR'], f'z2_L{bound}.json'), 'w') as fh:
                json.dump({'delta': Zm.delta, 'acc': Zm.acc}, fh)
