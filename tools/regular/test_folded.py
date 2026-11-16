"""Brute-force tests of folded.py on small boards.  Run with FOLD_ORIENT=out and =in."""
import itertools, random, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from folded import *
print('orientation', ORIENT)
for n in range(0, 10):
    for t in itertools.product('.TF', repeat=n):
        w = ''.join(t); f = fold(w)
        assert unfold(f) == w
        assert {fold(q) for q in lm(w)} == pat_moves(PL, f)
        assert {fold(q) for q in rm(w)} == pat_moves(PR, f)
        assert VALID.accepts(f) and SYM.accepts(f) == (mirror(w) == w)
        assert STARTS_OK.accepts(f) == (any(w == 'T'*a+'.'*(n-2*a)+'F'*a for a in range(n//2+1)) and w != 'TTT..FFF')
        for n0 in (0, 7, 8):
            assert valid_min(n0).accepts(f) == (n >= n0)
print('moves / sets ok')
random.seed(1)
for trial in range(20):
    k = random.randint(1, 4)
    X = DFA([[random.randrange(k) for a in range(NLET)] for s in range(k)], [random.random() < .5 for s in range(k)])
    P = pre(X, PR); T = PreTracker(X, PR)
    for n in range(0, 8):
        for t in itertools.product('.TF', repeat=n):
            f = fold(''.join(t)); S = T.start
            for a in f: S = T.step(S, a)
            exp = any(X.accepts(r) for r in pat_moves(PR, f))
            assert P.accepts(f) == exp and T.acc(S) == exp
print('pre ok')
def trie(words):
    words=set(words); ids={():0}; order=[()]
    for w in sorted(words, key=len):
        for i in range(1,len(w)+1):
            if w[:i] not in ids: ids[w[:i]]=len(order); order.append(w[:i])
    dead=len(order)
    return DFA([[ids.get(p+(a,), dead) for a in range(12)] for p in order]+[[dead]*12], [p in words for p in order]+[False])
def brute(N, Z, maxlen):
    for L in range(0, maxlen+1):
        for f in itertools.product(range(12), repeat=L):
            if not VALID.accepts(f): continue
            w = unfold(f)
            if N.accepts(f):
                lf = lambda q: mirror(q) == q or Z.accepts(fold(q)) or any(N.accepts(fold(r)) for r in rm(q))
                if not lf(w) or not all(lf(q) for q in lm(w)): return ('N', f)
            if Z.accepts(f) and not all(any(Z.accepts(fold(r)) for r in rm(q)) for q in lm(w)): return ('Z', f)
            if STARTS_OK.accepts(f) and not N.accepts(f): return ('start', f)
ML=3
allw=[''.join(t) for n in range(0,2*ML+1) for t in itertools.product('.TF',repeat=n)]
NP=[fold(w) for w in allw if Np(w)]; ZE=[fold(w) for w in allw if le0(w)]
assert check(trie(NP), trie(ZE), ML) is None
random.seed(5)
for trial in range(40):
    NPs=set(NP); ZEs=set(ZE)
    for _ in range(random.randint(1,3)):
        (NPs if random.random()<.5 else ZEs).discard(random.choice(NP if random.random()<.5 else ZE))
    a=check(trie(NPs), trie(ZEs), ML); b=brute(trie(NPs), trie(ZEs), ML)
    assert (a is None) == (b is None) and (a is None or len(a[1]) == len(b[1])), (a,b)
print('check agrees with brute force')
