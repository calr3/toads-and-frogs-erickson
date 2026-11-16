#!/usr/bin/env python3
"""Backtracking search for a closed set of four-piece shapes (see gen_row2.py and Cgt/Shape4.lean).

Solves the abstract game on shapes: a shape is won for Right if, for every witness and every
Left move from it, some Right reply leads to a won shape.  Right's replies are restricted to
shapes whose mirrored differences stay within [-D, D].  Losing verdicts are sound for this
abstract game; the winning strategy found is checked for closure at the end.

Usage: search_row2.py FAMILY PERIOD CAP D [LEAN_NAME [DOC]]   (with LEAN_NAME: print a Lean data file)
"""
import sys
from collections import deque
import gen_row2 as g

sys.setrecursionlimit(10 ** 6)


def main():
    family, g.PER, g.K, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    starts = sorted({g.shape(p) for p in g.starts(family)})
    chal = {}          # shape -> list of option lists (shapes), one per (witness, Left move)
    status = {}        # 1 on stack, 2 won (tentative), 3 lost
    choice = {}

    def challenges(s):
        if s not in chal:
            cs = []
            for w in g.wit(s):
                for q in g.lms(w):
                    opts = []
                    for r in g.rms(q):
                        sr = g.shape(r)
                        if abs(sr[1]) <= D and abs(sr[2]) <= D and g.in_range(sr):
                            opts.append((g.asym(r), sr))
                    cs.append([sr for _, sr in sorted(opts)])
            chal[s] = cs
        return chal[s]

    def dfs(s):
        st = status.get(s)
        if st == 3:
            return False
        if st in (1, 2):
            return True
        status[s] = 1
        picks = []
        for opts in challenges(s):
            opts = sorted(opts, key=lambda o: 0 if status.get(o) == 2 else 1)
            for o in opts:
                if dfs(o):
                    picks.append(o)
                    break
            else:
                status[s] = 3
                return False
        choice[s] = picks
        status[s] = 2
        return True

    for it in range(200):
        for k in [k for k, v in status.items() if v != 3]:
            del status[k]
        lost = [s for s in starts if not dfs(s)]
        if lost:
            print(f'iteration {it}: {len(lost)} of {len(starts)} start shapes lost ({len(chal)} shapes explored): '
                  + ', '.join(g.to_str(g.wit(s)[0]) for s in lost))
            return 1
        W, todo = set(), deque(starts)
        while todo:
            s = todo.popleft()
            if s in W:
                continue
            W.add(s)
            todo.extend(choice[s])
        bad = [s for s in W if any(status.get(o) == 3 for o in choice[s])]
        print(f'iteration {it}: strategy uses {len(W)} shapes ({len(chal)} explored), {len(bad)} rely on lost shapes',
              file=sys.stderr, flush=True)
        if not bad:
            print(f'CLOSED with {len(W)} shapes', file=sys.stderr)
            assert g.check_all(W), 'the Lean check would fail'
            if len(sys.argv) > 5:
                print(g.emit_tree(W, sys.argv[5], sys.argv[6] if len(sys.argv) > 6 else 'Machine-generated shapes.'))
            return 0
    return 1


if __name__ == '__main__':
    sys.exit(main())
