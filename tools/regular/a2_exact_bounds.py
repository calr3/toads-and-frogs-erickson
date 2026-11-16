#!/usr/bin/env python3
"""How much asymmetry Right needs to prove the exact values of TT□ᵇFF.

TT□ᵇFF = 0 follows from T□T□ᵏF□F <= 0 (k = b - 2), and TT□ᵇFF = * from TT□ᵏF□F <= 0
(k = b - 1); see Cgt/RowA2Values.lean.  For each k this prints the smallest D such that Right,
moving second, can win that position while keeping |g4 - g0| <= D and |g3 - g1| <= D after each
of its replies (the mirrored gap differences that the shapes of Cgt/Shape4.lean store exactly).

Usage: a2_exact_bounds.py zero|star KMIN KMAX
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'scripts'))
sys.setrecursionlimit(10 ** 6)
import gen_row2 as g  # noqa: E402


def min_bound(s, top=60):
    for D in range(top):
        g.D = D
        g.win_bounded.cache_clear()
        if g.win_bounded(s):
            return D
    return None


def main():
    family, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    for k in range(lo, hi + 1):
        s = ('T.T' if family == 'zero' else 'TT') + '.' * k + 'F.F'
        print(k, min_bound(s) if g.le0(s) else 'not <= 0', flush=True)


if __name__ == '__main__':
    main()
