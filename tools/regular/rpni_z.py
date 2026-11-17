"""State-merging (RPNI) search for the a = 2 normal-play invariant Z.

Positives: the closure of the pass positions under the canonical local Right strategy
(canonical_z.py); negatives: positions with 2 toads and 2 frogs that are not <= 0.  The
learned automaton is checked for all board sizes with learn_z.check_z; counterexamples are
added (with their closure) and the automaton relearned.

Usage: rpni_z.py NMAX [ROUNDS]
"""
import sys
import time
from folded import DFA, NLET, fold, unfold, lm, le0, minimize, word_str
from canonical_z import closure, reply, all_2t2f, pass_positions
from learn_z import PASS2, check_z
from folded import build, inter


def pieces(nt, nf):
    """Folded words with exactly nt toads and nf frogs."""
    def step(st, a):
        if st == 'dead':
            return 'dead'
        cells = [a // 3, a % 3] if a < 9 else [a - 9]
        t = st[0] + cells.count(1); f = st[1] + cells.count(2)
        return (t, f) if t <= nt and f <= nf else 'dead'
    return minimize(build((0, 0), step, lambda st: st == (nt, nf)))


P22 = pieces(2, 2)


def rpni(pos, neg):
    root = 0; child = [{}]; label = [None]
    def node(f):
        v = root
        for a in f:
            nxt = child[v].get(a)
            if nxt is None:
                nxt = len(child); child.append({}); label.append(None); child[v][a] = nxt
            v = nxt
        return v
    for f in pos:
        label[node(f)] = '+'
    for f in neg:
        v = node(f)
        if label[v] == '+':
            raise ValueError(f'{word_str(f)} is both positive and negative')
        label[v] = '-'
    parent = list(range(len(child))); log = []

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    def merge(a, b):
        a, b = find(a), find(b)
        if a == b:
            return True
        if label[a] and label[b] and label[a] != label[b]:
            return False
        log.append(('p', b, parent[b])); parent[b] = a
        if label[a] is None and label[b]:
            log.append(('l', a, label[a])); label[a] = label[b]
        for c, y in list(child[b].items()):
            x = child[a].get(c)
            if x is None:
                log.append(('c', a, c)); child[a][c] = y
            elif not merge(x, y):
                return False
        return True

    def rollback(mark):
        while len(log) > mark:
            kind, x, y = log.pop()
            if kind == 'p':
                parent[x] = y
            elif kind == 'l':
                label[x] = y
            else:
                del child[x][y]

    red = [root]; redset = {root}
    while True:
        blue = sorted({find(y) for r in red for y in child[find(r)].values()} - redset)
        if not blue:
            break
        b = blue[0]
        for r in red:
            mark = len(log)
            if merge(r, b):
                break
            rollback(mark)
        else:
            red.append(b); redset.add(b)
    idx = {r: i for i, r in enumerate(red)}; sink = len(red)
    delta = [[idx[find(child[r][a])] if a in child[r] else sink for a in range(NLET)] for r in red]
    delta.append([sink] * NLET)
    return minimize(DFA(delta, [label[r] == '+' for r in red] + [False]))


def close(zs, C):
    stack = list(zs)
    while stack:
        z = stack.pop()
        if z in C:
            continue
        C.add(z)
        for q in lm(z):
            stack.append(reply(z, q))


# GROW: add the closure of a troublesome position <= 0 (True), or exclude it from Z (False).
GROW = __import__('os').environ.get('GROW', '0') == '1'

if __name__ == '__main__':
    nmax = int(sys.argv[1]); rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 50
    t0 = time.time()
    C = closure(nmax)
    EXACT = __import__('os').environ.get('EXACT', '0') == '1'
    # EXACT: every 2T2F position up to nmax cells outside the closure is a negative.
    neg = {w for n in range(nmax + 1) for w in all_2t2f(n) if (w not in C if EXACT else not le0(w))}
    covered = nmax
    print(f'closure {len(C)}, negatives {len(neg)}  ({time.time()-t0:.0f}s)', flush=True)
    for rnd in range(rounds):
        Z = inter(rpni([fold(z) for z in C], [fold(w) for w in neg]), P22)
        found = check_z(Z, PASS2)
        if rnd % 25 == 0 or not found:
            print(f'round {rnd}: |Z| = {len(Z)}; positives {len(C)}, negatives {len(neg)}; '
                  f'counterexamples {[(k, unfold(f)) for k, f in found]}  ({time.time()-t0:.0f}s)', flush=True)
        if not found:
            import json
            json.dump({'delta': Z.delta, 'acc': Z.acc}, open(f'z2_rpni_{nmax}_grow{int(GROW)}.json', 'w'))
            print('Z is a normal-play invariant for every board size', flush=True)
            break
        for kind, f in found:
            w = unfold(f)
            if EXACT:
                while covered < len(w):     # cover whole board sizes at a time
                    covered += 1
                    close([z for z in pass_positions(covered) if len(z) == covered], C)
                    neg |= {x for x in all_2t2f(covered) if x not in C}
                if w not in C:
                    neg.add(w)
            elif kind == 'P' or (GROW and le0(w)):
                close([w], C)
            else:
                neg.add(w)
