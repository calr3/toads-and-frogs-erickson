#!/usr/bin/env python3
"""Generate a Lean proof that T^a E^b F^a is infinitesimal from an explicit Right strategy.

Every position in the strategy DAG becomes one lemma:
  * `n_i : UpperZero (tf p)` (Left stop <= 0, Right still has his "pass"), or
  * `z_i : tf p <= 0`       (normal play, Right moving second).
The moves are checked by `decide` in the kernel; the lemmas are combined with the helper
theorems of `Cgt/Certificate.lean`.

Usage: gen_cert.py a b > Cgt/Cert/Case_a_b.lean
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(1000000)


def lm(s):
    n = len(s); out = []
    for i, c in enumerate(s):
        if c == 'T':
            if i + 1 < n and s[i + 1] == '.':
                out.append(s[:i] + '.T' + s[i + 2:])
            elif i + 2 < n and s[i + 1] == 'F' and s[i + 2] == '.':
                out.append(s[:i] + '.FT' + s[i + 3:])
    return out


def rm(s):
    out = []
    for i, c in enumerate(s):
        if c == 'F':
            if i - 1 >= 0 and s[i - 1] == '.':
                out.append(s[:i - 1] + 'F.' + s[i + 1:])
            elif i - 2 >= 0 and s[i - 1] == 'T' and s[i - 2] == '.':
                out.append(s[:i - 2] + 'FT.' + s[i + 1:])
    return out


def mirror(s):
    return ''.join({'T': 'F', 'F': 'T', '.': '.'}[c] for c in reversed(s))


@lru_cache(None)
def LF(s):
    return any(not RF(t) for t in lm(s))


@lru_cache(None)
def RF(s):
    return any(not LF(t) for t in rm(s))


def le0(s):
    return not LF(s)


@lru_cache(None)
def Mp(s):
    return le0(s) or any(Np(t) for t in rm(s))


@lru_cache(None)
def Np(s):
    return (mirror(s) == s or Mp(s)) and all(Mp(t) for t in lm(s))


# ---------------------------------------------------------------- strategy extraction
nodesN = {}   # position -> (lf, passes, pairs)
nodesZ = {}   # position -> pairs
orderN, orderZ = [], []


def pick_N_reply(q):
    cands = [r for r in rm(q) if Np(r)]
    if not cands:
        return None
    for r in cands:              # reuse existing nodes first
        if r in nodesN:
            return r
    for r in cands:              # then symmetric replies
        if mirror(r) == r:
            return r
    return cands[0]


def pick_Z_reply(q):
    cands = [r for r in rm(q) if le0(r)]
    for r in cands:
        if r in nodesZ:
            return r
    return cands[0]


def buildZ(z):
    if z in nodesZ:
        return
    nodesZ[z] = None
    pairs = []
    for q in lm(z):
        r = pick_Z_reply(q)
        buildZ(r)
        pairs.append((q, r))
    nodesZ[z] = pairs
    orderZ.append(z)


def buildN(p):
    if p in nodesN:
        return
    nodesN[p] = None
    assert Np(p)
    if mirror(p) == p:
        lf = ('sym',)
    else:
        r = pick_N_reply(p)
        if r is not None:
            buildN(r)
            lf = ('reply', r)
        else:
            assert le0(p)
            buildZ(p)
            lf = ('le', p)
    passes, pairs = [], []
    for q in lm(p):
        r = pick_N_reply(q)
        if r is not None and (r in nodesN or not le0(q)):
            buildN(r)
            pairs.append((q, r))
        else:
            assert le0(q)
            buildZ(q)
            passes.append(q)
    nodesN[p] = (lf, passes, pairs)
    orderN.append(p)


# ---------------------------------------------------------------- Lean output
def lit(s):
    return '[' + ', '.join({'T': 'T', 'F': 'F', '.': 'E'}[c] for c in s) + ']'


def main():
    a, b = int(sys.argv[1]), int(sys.argv[2])
    start = 'T' * a + '.' * b + 'F' * a
    if not Np(start):
        sys.exit(f'({a},{b}) is not infinitesimal')
    buildN(start)
    zid = {z: i for i, z in enumerate(orderZ)}
    nid = {p: i for i, p in enumerate(orderN)}
    out = []
    out.append('import Cgt.Certificate\n')
    out.append(f'/-! Machine-generated certificate: `T^{a} □^{b} F^{a}` is infinitesimal. -/\n')
    out.append(f'namespace Cgt.Cert_{a}_{b}')
    out.append('open Cell Game\n')

    def cases(names):
        t = 'trivial'
        for nm in reversed(names):
            t = f'(And.intro {nm} {t})'
        return t

    for z in orderZ:
        pairs = nodesZ[z]
        plist = '[' + ', '.join(f'({lit(q)}, {lit(r)})' for q, r in pairs) + ']'
        names = [f'z_{zid[r]}' for _, r in pairs]
        out.append(f'theorem z_{zid[z]} : le (tf {lit(z)}) zero :=')
        out.append(f'  le_zero_of_pairs {lit(z)} {plist} (by decide +kernel) (by decide +kernel)')
        out.append(f'    {cases(names)}\n')
    for p in orderN:
        lf, passes, pairs = nodesN[p]
        if lf[0] == 'sym':
            lfp = f'(lfZero_of_mirror_dec {lit(p)} (by decide +kernel))'
        elif lf[0] == 'reply':
            lfp = f'(lfZero_of_reply {lit(p)} {lit(lf[1])} (by decide +kernel) n_{nid[lf[1]]})'
        else:
            lfp = f'((lfZero_tf_iff _).2 (Or.inl z_{zid[lf[1]]}))'
        pl = '[' + ', '.join(lit(q) for q in passes) + ']'
        prl = '[' + ', '.join(f'({lit(q)}, {lit(r)})' for q, r in pairs) + ']'
        out.append(f'theorem n_{nid[p]} : UpperZero (tf {lit(p)}) :=')
        out.append(f'  upperZero_of_pairs {lit(p)} {lfp} {pl} {prl}')
        out.append('    (by decide +kernel) (by decide +kernel)')
        out.append(f'    {cases([f"z_{zid[q]}" for q in passes])}')
        out.append(f'    {cases([f"n_{nid[r]}" for _, r in pairs])}\n')
    out.append(f'theorem infinitesimal : Infinitesimal (tf (start {a} {b})) := by')
    out.append(f'  rw [infinitesimal_start_iff, show start {a} {b} = {lit(start)} from by decide]')
    out.append(f'  exact n_{nid[start]}\n')
    out.append(f'end Cgt.Cert_{a}_{b}')
    print('\n'.join(out))
    print(f'-- nodes: N={len(orderN)} Z={len(orderZ)}', file=sys.stderr)


if __name__ == '__main__':
    main()
