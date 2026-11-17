"""Toads and Frogs on the folded board, and finite automata over folded positions.

A position w of length n is folded into the word
    f[i] = (w[i], w[n-1-i])   for i < n // 2,
followed by one "middle" letter holding w[n // 2] if n is odd.  The word is read from the
ends of the board inwards.  Mirror symmetry becomes a letter-by-letter condition, and every
move changes at most three consecutive letters, so the move relation is a local rewrite.

Letters: 0..8 are pairs 3*left+right (cells '.'=0, 'T'=1, 'F'=2); 9..11 are middle letters.

An *invariant* is a pair of languages (N, Z) of folded positions such that
  * Z ⊆ { p : every Left move p -> q has a Right reply q -> r with r ∈ Z }      (so p <= 0)
  * N ⊆ LF ∩ { p : every Left move p -> q has q ∈ LF },
    where LF = Sym ∪ Z ∪ { q : some Right move q -> r has r ∈ N }              (so Left stop <= 0)
  * every start position T^a .^b F^a with (a, b) != (3, 2) is in N.
These are exactly the conditions of `upperZero_iff` / `lfZero_iff` / `le_iff`, so by induction
on the (finite) game every position of N has Left stop <= 0.  `check` decides them for
regular N and Z over boards of *every* size.
"""
import sys
from collections import deque
from functools import lru_cache

sys.setrecursionlimit(1000000)

import os

# Reading direction: 'out' reads from the ends of the board inwards (centre last);
# 'in' reads from the centre outwards (centre first).
ORIENT = os.environ.get('FOLD_ORIENT', 'out')
assert ORIENT in ('out', 'in')

CH = '.TF'
IDX = {c: i for i, c in enumerate(CH)}
NLET = 12
SWAP = [0, 2, 1]


def letter_str(a):
    return CH[a // 3] + CH[a % 3] if a < 9 else 'M' + CH[a - 9]


def word_str(f):
    return ' '.join(letter_str(a) for a in f)


def fold(w):
    n = len(w); h = n // 2
    out = [3 * IDX[w[i]] + IDX[w[n - 1 - i]] for i in range(h)]
    if n % 2:
        out.append(9 + IDX[w[h]])
    return tuple(out) if ORIENT == 'out' else tuple(reversed(out))


def unfold(f):
    if ORIENT == 'in':
        f = tuple(reversed(f))
    if f and f[-1] >= 9:
        mid, pairs = CH[f[-1] - 9], f[:-1]
    else:
        mid, pairs = '', f
    left = ''.join(CH[x // 3] for x in pairs)
    right = ''.join(CH[x % 3] for x in pairs)
    return left + mid + right[::-1]


# ------------------------------------------------------------------ the game (unfolded)
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
def Mp(s):  # Right stop <= 0  (LfZero)
    return le0(s) or any(Np(t) for t in rm(s))


@lru_cache(None)
def Np(s):  # Left stop <= 0   (UpperZero)
    return (mirror(s) == s or Mp(s)) and all(Mp(t) for t in lm(s))


# ------------------------------------------------------------------ moves as folded rewrites
def _cell_pos(n, c):
    h = n // 2
    if c < h:
        return (c, 0)
    if n % 2 and c == h:
        return (h, 2)
    return (n - 1 - c, 1)


def _rel(spec, a):
    """Apply one window position's rewrite to letter a (None if not applicable)."""
    sp = dict(spec)
    if a >= 9:
        if 2 not in sp or sp[2][0] != a - 9:
            return None
        return 9 + sp[2][1]
    if 2 in sp:
        return None
    X, Y = divmod(a, 3)
    if 0 in sp:
        if X != sp[0][0]:
            return None
        X = sp[0][1]
    if 1 in sp:
        if Y != sp[1][0]:
            return None
        Y = sp[1][1]
    return 3 * X + Y


def patterns(player, nmax=14):
    """Window rewrites for one player's moves: list of (anchored, tables).

    tables[j][a] is the rewritten letter at window offset j (or None).  An anchored window
    straddles the centre of the board and so must end at the last letter of the word."""
    piece, other, d = ('T', 'F', 1) if player == 'L' else ('F', 'T', -1)
    keys = set()
    for n in range(1, nmax + 1):
        last = n // 2 - 1 + n % 2
        for c in range(n):
            for cells in ([(c, piece, '.'), (c + d, '.', piece)],
                          [(c, piece, '.'), (c + d, other, other), (c + 2 * d, '.', piece)]):
                if any(not 0 <= x < n for x, _, _ in cells):
                    continue
                pos = [(_cell_pos(n, x), b, a) for x, b, a in cells]
                idxs = [p[0] for p, _, _ in pos]
                tracks = {p[1] for p, _, _ in pos}
                lo, hi = min(idxs), max(idxs)
                anchored = 2 in tracks or (0 in tracks and 1 in tracks)
                assert not anchored or hi == last
                spec = [dict() for _ in range(hi - lo + 1)]
                for (i, t), b, a in pos:
                    spec[i - lo][t] = (IDX[b], IDX[a])
                keys.add((anchored, tuple(tuple(sorted(s.items())) for s in spec)))
    res = [(anch, [[_rel(s, a) for a in range(NLET)] for s in spec]) for anch, spec in sorted(keys)]
    if ORIENT == 'in':
        res = [(anch, list(reversed(tables))) for anch, tables in res]
    return res


PL = patterns('L')
PR = patterns('R')


def _may_start(anch, phase):
    """Centre-straddling windows end the word ('out') or start it ('in')."""
    return ORIENT == 'out' or not anch or phase == 'p0'


def _after(anch):
    return 'e' if (anch and ORIENT == 'out') else 'q'


P0 = 'p0' if ORIENT == 'in' else 'p'


def pat_moves(pats, f):
    res = set(); n = len(f)
    for anch, tables in pats:
        m = len(tables)
        for lo in (([n - m] if ORIENT == 'out' else [0]) if anch else range(n - m + 1)):
            if lo < 0 or lo + m > n:
                continue
            out = list(f)
            for j in range(m):
                o = tables[j][f[lo + j]]
                if o is None:
                    break
                out[lo + j] = o
            else:
                res.add(tuple(out))
    return res


# ------------------------------------------------------------------ automata
class DFA:
    def __init__(self, delta, acc, start=0):
        self.delta, self.acc, self.start = delta, acc, start

    def __len__(self):
        return len(self.delta)

    def run(self, f):
        s = self.start
        for a in f:
            s = self.delta[s][a]
        return s

    def accepts(self, f):
        return self.acc[self.run(f)]


def build(start, step, is_acc):
    ids = {start: 0}; order = [start]; delta = []
    i = 0
    while i < len(order):
        st = order[i]; row = []
        for a in range(NLET):
            t = step(st, a)
            if t not in ids:
                ids[t] = len(order); order.append(t)
            row.append(ids[t])
        delta.append(row); i += 1
    return DFA(delta, [bool(is_acc(st)) for st in order])


def minimize(D):
    part = [1 if x else 0 for x in D.acc]
    nclass = len(set(part))
    while True:
        sig = {}
        new = [sig.setdefault((part[s],) + tuple(part[t] for t in D.delta[s]), len(sig))
               for s in range(len(D))]
        if len(sig) == nclass:
            break
        part, nclass = new, len(sig)
    part = new
    # renumber so the start state is 0, in BFS order
    order = {part[D.start]: 0}; q = deque([D.start]); seen = {D.start}
    while q:
        s = q.popleft()
        for t in D.delta[s]:
            if part[t] not in order:
                order[part[t]] = len(order)
            if t not in seen:
                seen.add(t); q.append(t)
    delta = [None] * len(order); acc = [False] * len(order)
    for s in seen:
        c = order[part[s]]
        delta[c] = [order[part[t]] for t in D.delta[s]]
        acc[c] = D.acc[s]
    return DFA(delta, acc)


def product(A, B, op):
    return minimize(build((A.start, B.start),
                          lambda st, a: (A.delta[st[0]][a], B.delta[st[1]][a]),
                          lambda st: op(A.acc[st[0]], B.acc[st[1]])))


def inter(*Ds):
    R = Ds[0]
    for D in Ds[1:]:
        R = product(R, D, lambda x, y: x and y)
    return R


def union(*Ds):
    R = Ds[0]
    for D in Ds[1:]:
        R = product(R, D, lambda x, y: x or y)
    return R


def compl(D):
    return DFA(D.delta, [not x for x in D.acc], D.start)


def pre(X, pats):
    """DFA for { q : some move q -> r of the given patterns has r ∈ X }."""
    def step(S, a):
        out = set()
        for st in S:
            k = st[0]
            if k in ('p', 'p0'):
                x = st[1]
                out.add(('p', X.delta[x][a]))
                for pi, (anch, tables) in enumerate(pats):
                    o = tables[0][a]
                    if o is not None and _may_start(anch, k):
                        x2 = X.delta[x][o]
                        out.add((_after(anch), x2) if len(tables) == 1 else ('w', pi, 1, x2))
            elif k == 'w':
                _, pi, j, x = st
                anch, tables = pats[pi]
                o = tables[j][a]
                if o is not None:
                    x2 = X.delta[x][o]
                    out.add((_after(anch), x2) if j + 1 == len(tables) else ('w', pi, j + 1, x2))
            elif k == 'q':
                out.add(('q', X.delta[st[1]][a]))
        return frozenset(out)
    return minimize(build(frozenset([(P0, X.start)]), step,
                          lambda S: any(st[0] in 'qe' and X.acc[st[-1]] for st in S)))


def _simple(table, start, accepting):
    """DFA from a dict state -> (function letter -> state); missing -> dead."""
    return minimize(build(start, lambda s, a: table.get(s, lambda a: 'dead')(a) if s != 'dead' else 'dead',
                          lambda s: s in accepting))


def reverse(D):
    """DFA for the reversed language."""
    def step(S, a):
        return frozenset(s for s in range(len(D)) if D.delta[s][a] in S)
    return minimize(build(frozenset(s for s in range(len(D)) if D.acc[s]), step, lambda S: D.start in S))


def _orient(D):
    return D if ORIENT == 'out' else reverse(D)


VALID = _orient(_simple({0: lambda a: 0 if a < 9 else 1}, 0, {0, 1}))
SYM = _orient(_simple({0: lambda a: 0 if a < 9 and a % 3 == SWAP[a // 3] else (1 if a == 9 else 'dead')}, 0, {0, 1}))
_TF, _EE, _M0 = 5, 0, 9
STARTS = _orient(_simple({0: lambda a: {_TF: 0, _EE: 1, _M0: 2}.get(a, 'dead'),
                          1: lambda a: {_EE: 1, _M0: 2}.get(a, 'dead')}, 0, {0, 1, 2}))


def word_dfa(f):
    return _simple({i: (lambda i: lambda a: i + 1 if a == f[i] else 'dead')(i) for i in range(len(f))}, 0, {len(f)})


STARTS_OK = inter(STARTS, compl(word_dfa(fold('TTT..FFF'))))


def starts_rows(rows):
    """Start positions T^a .^b F^a with a in `rows` (all b), except (3, 2)."""
    amax = max(rows) + 1
    def step(st, a):
        if st == 'dead':
            return 'dead'
        phase, cnt = st
        if phase == 0 and a == _TF:
            return (0, min(cnt + 1, amax))
        if a == _EE:
            return (1, cnt)
        if a == _M0:
            return (2, cnt)
        return 'dead'
    D = minimize(build((0, 0), step, lambda st: st != 'dead' and st[1] in rows))
    return inter(_orient(D), compl(word_dfa(fold('TTT..FFF'))))


def valid_min(n0):
    """Valid folded words of boards with at least n0 cells."""
    cap = n0 // 2 + 1
    def step(st, a):
        if st == 'dead' or st[1]:
            return 'dead'
        return (min(st[0] + 1, cap), a >= 9)
    return _orient(minimize(build((0, False), step, lambda st: st != 'dead' and 2 * st[0] - st[1] >= n0)))


def shortest(D, maxlen=None):
    if D.acc[D.start]:
        return ()
    par = {D.start: None}; q = deque([(D.start, 0)])
    while q:
        s, dep = q.popleft()
        if maxlen is not None and dep >= maxlen:
            continue
        for a in range(NLET):
            t = D.delta[s][a]
            if t not in par:
                par[t] = (s, a)
                if D.acc[t]:
                    w = []
                    while par[t] is not None:
                        t, a2 = par[t]; w.append(a2)
                    return tuple(reversed(w))
                q.append((t, dep + 1))
    return None


class PreTracker:
    """On-the-fly subset construction for pre(X, pats): the state after reading q tells
    whether some move q -> r of the patterns has r ∈ X."""

    def __init__(self, X, pats):
        self.X, self.pats, self.memo, self.accmemo = X, pats, {}, {}
        self.start = frozenset([(P0, X.start)])

    def step(self, S, a):
        key = (S, a)
        r = self.memo.get(key)
        if r is None:
            X, pats = self.X, self.pats
            out = set()
            for st in S:
                k = st[0]
                if k in ('p', 'p0'):
                    x = st[1]
                    out.add(('p', X.delta[x][a]))
                    for pi, (anch, tables) in enumerate(pats):
                        o = tables[0][a]
                        if o is not None and _may_start(anch, k):
                            x2 = X.delta[x][o]
                            out.add((_after(anch), x2) if len(tables) == 1 else ('w', pi, 1, x2))
                elif k == 'w':
                    _, pi, j, x = st
                    anch, tables = pats[pi]
                    o = tables[j][a]
                    if o is not None:
                        x2 = X.delta[x][o]
                        out.add((_after(anch), x2) if j + 1 == len(tables) else ('w', pi, j + 1, x2))
                elif k == 'q':
                    out.add(('q', X.delta[st[1]][a]))
            r = self.memo[key] = frozenset(out)
        return r

    def acc(self, S):
        r = self.accmemo.get(S)
        if r is None:
            r = self.accmemo[S] = any(st[0] in 'qe' and self.X.acc[st[-1]] for st in S)
        return r


def _trans(pats, t, a):
    """Transducer for one move: from phase t on letter a, the (output letter, phase) pairs."""
    if t in ('p', 'p0'):
        res = [(a, 'p')]
        for pi, (anch, tables) in enumerate(pats):
            o = tables[0][a]
            if o is not None and _may_start(anch, t):
                res.append((o, _after(anch) if len(tables) == 1 else (pi, 1)))
        return res
    if t == 'q':
        return [(a, 'q')]
    if t == 'e':
        return []
    pi, j = t
    anch, tables = pats[pi]
    o = tables[j][a]
    if o is None:
        return []
    return [(o, _after(anch) if j + 1 == len(tables) else (pi, j + 1))]


def _coreach(D):
    """States of D from which an accepting state is reachable."""
    good = {s for s in range(len(D)) if D.acc[s]}
    changed = True
    while changed:
        changed = False
        for s in range(len(D)):
            if s not in good and any(t in good for t in D.delta[s]):
                good.add(s); changed = True
    return good


def _bfs(start, succ, accept, maxlen):
    """Shortest letter sequence from start to an accepting state; succ(state) yields (letter, state)."""
    par = {start: None}
    frontier = [start]; dep = 0
    while frontier:
        for st in frontier:
            if accept(st):
                w = []
                while par[st] is not None:
                    st, a = par[st]; w.append(a)
                return tuple(reversed(w))
        if maxlen is not None and dep >= maxlen:
            return None
        nxt = []
        for st in frontier:
            for a, t in succ(st):
                if t not in par:
                    par[t] = (st, a); nxt.append(t)
        frontier = nxt; dep += 1
    return None


def check(N, Z, maxlen=None, n0=0, starts=None):
    """Return None if (N, Z) is an invariant (on folded words of length <= maxlen), else a
    shortest counterexample (kind, word)."""
    found = check_all(N, Z, maxlen, n0, starts)
    return min(found, key=lambda x: len(x[1])) if found else None


def check_all(N, Z, maxlen=None, n0=0, starts=None):
    """A shortest counterexample (kind, word) for each violated condition; [] if (N, Z) is an
    invariant on folded words of length <= maxlen.  Only the "has a good Right reply" sets
    are determinised, lazily and along the search."""
    V, S = (valid_min(n0) if n0 else VALID), SYM
    BN, BZ = PreTracker(N, PR), PreTracker(Z, PR)
    liveN, liveZ = _coreach(N), _coreach(Z)
    found = []

    # p ∈ N is not symmetric, not in Z, and has no Right move into N.
    def succ_self(st):
        v, n, s, z, b = st
        for a in range(NLET):
            n2 = N.delta[n][a]
            if n2 in liveN:
                yield a, (V.delta[v][a], n2, S.delta[s][a], Z.delta[z][a], BN.step(b, a))
    w = _bfs((V.start, N.start, S.start, Z.start, BN.start), succ_self,
             lambda st: V.acc[st[0]] and N.acc[st[1]] and not S.acc[st[2]] and not Z.acc[st[3]]
             and not BN.acc(st[4]), maxlen)
    if w is not None:
        found.append(('N', w))

    # p ∈ N has a Left move p -> q with q not symmetric, not in Z, and no Right move into N.
    def succ_left(st):
        v, n, t, s, z, b = st
        for a in range(NLET):
            n2 = N.delta[n][a]
            if n2 in liveN:
                v2 = V.delta[v][a]
                for o, t2 in _trans(PL, t, a):
                    yield a, (v2, n2, t2, S.delta[s][o], Z.delta[z][o], BN.step(b, o))
    w = _bfs((V.start, N.start, P0, S.start, Z.start, BN.start), succ_left,
             lambda st: V.acc[st[0]] and N.acc[st[1]] and st[2] in ('q', 'e') and not S.acc[st[3]]
             and not Z.acc[st[4]] and not BN.acc(st[5]), maxlen)
    if w is not None:
        found.append(('N', w))

    # p ∈ Z has a Left move p -> q with no Right move q -> r into Z.
    def succ_z(st):
        v, z, t, b = st
        for a in range(NLET):
            z2 = Z.delta[z][a]
            if z2 in liveZ:
                v2 = V.delta[v][a]
                for o, t2 in _trans(PL, t, a):
                    yield a, (v2, z2, t2, BZ.step(b, o))
    w = _bfs((V.start, Z.start, P0, BZ.start), succ_z,
             lambda st: V.acc[st[0]] and Z.acc[st[1]] and st[2] in ('q', 'e') and not BZ.acc(st[3]), maxlen)
    if w is not None:
        found.append(('Z', w))

    # a start position (other than (3, 2)) is not in N.
    w = shortest(inter(STARTS_OK if starts is None else starts, V, compl(N)), maxlen)
    if w is not None:
        found.append(('start', w))
    return found
