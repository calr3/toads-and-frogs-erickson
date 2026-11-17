"""Lower bounds on the size of any automaton invariant (N, Z), from forced positions.

Every invariant contains the start positions (other than (3, 2)).  If p must be in N and a
Left option q of p (or p itself, for a Left pass) is not symmetric, not <= 0, and has exactly
one Right reply r with Left stop <= 0, then r must be in N.  Similarly for Z (normal play,
Right moving second): a unique reply r <= 0 to a Left move from a forced Z position is forced,
and so is q ∈ Z when q <= 0 has no good reply into N.  Losing positions are never in N or Z.

Two folded prefixes u, u' need different DFA states if some suffix v puts uv in a forced set
and u'v in the corresponding losing set.  A set of pairwise distinguishable prefixes bounds
the number of states of *every* DFA invariant from below.

Usage: forced.py n_min n_max   (boards with n_min <= n <= n_max cells)
"""
import sys
from folded import fold, lm, rm, mirror, le0, Np, ORIENT


def forced_sets(n):
    FN, FZ = set(), set()
    stack = [('N', 'T' * a + '.' * (n - 2 * a) + 'F' * a) for a in range(n // 2 + 1)]
    stack = [x for x in stack if x[1] != 'TTT..FFF']
    reach = set()
    while stack:
        kind, p = stack.pop()
        if (kind == 'N' and p in FN) or (kind == 'Z' and p in FZ):
            continue
        (FN if kind == 'N' else FZ).add(p)
        if kind == 'N':
            assert Np(p), p
            qs = ([] if mirror(p) == p else [p]) + lm(p)
            for q in qs:
                if mirror(q) == q:
                    continue
                good = [r for r in rm(q) if Np(r)]
                if not le0(q) and len(good) == 1:
                    stack.append(('N', good[0]))
                elif le0(q) and not good:
                    stack.append(('Z', q))
        else:
            assert le0(p), p
            for q in lm(p):
                good = [r for r in rm(q) if le0(r)]
                if len(good) == 1:
                    stack.append(('Z', good[0]))
    return FN, FZ


def reachable(n):
    seen = set()
    stack = ['T' * a + '.' * (n - 2 * a) + 'F' * a for a in range(n // 2 + 1)]
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        stack.extend(lm(p)); stack.extend(rm(p))
    return seen


def lower_bound(n_min, n_max):
    # signature of each prefix: suffix -> label ('N+', 'N-', 'Z+', 'Z-')
    sig = {}
    npos = {'FN': 0, 'FZ': 0, 'bad': 0}
    for n in range(n_min, n_max + 1):
        FN, FZ = forced_sets(n)
        npos['FN'] += len(FN); npos['FZ'] += len(FZ)
        labels = {}
        for p in FN:
            labels.setdefault(fold(p), set()).add('N+')
        for p in FZ:
            labels.setdefault(fold(p), set()).add('Z+')
        for p in reachable(n):
            if not Np(p):
                labels.setdefault(fold(p), set()).add('N-'); npos['bad'] += 1
            if not le0(p):
                labels.setdefault(fold(p), set()).add('Z-')
        for f, ls in labels.items():
            for i in range(len(f) + 1):
                d = sig.setdefault(f[:i], {})
                for l in ls:
                    d.setdefault(f[i:], set()).add(l)
    opp = {'N+': 'N-', 'N-': 'N+', 'Z+': 'Z-', 'Z-': 'Z+'}

    def distinct(u, v):
        su, sv = sig[u], sig[v]
        if len(su) > len(sv):
            su, sv = sv, su
        for suf, ls in su.items():
            lv = sv.get(suf)
            if lv and any(opp[l] in lv for l in ls):
                return True
        return False
    # greedy clique, most constrained prefixes first
    prefixes = sorted(sig, key=lambda u: -len(sig[u]))
    clique = []
    for u in prefixes:
        if all(distinct(u, v) for v in clique):
            clique.append(u)
    return len(clique), npos


if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for top in range(lo, hi + 1):
        size, npos = lower_bound(lo, top)
        print(f'[{ORIENT}] boards {lo}..{top}: every invariant DFA needs >= {size} states '
              f'(forced N {npos["FN"]}, forced Z {npos["FZ"]}, losing {npos["bad"]})', flush=True)
