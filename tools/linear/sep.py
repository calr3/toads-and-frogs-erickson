import numpy as np, itertools, sys
rows = [list(map(int, l.split())) for l in open(sys.argv[1])]
names = {3:'TTFF',5:'TFTF',9:'TFFT',6:'FTTF',10:'FTFT',12:'FFTT'}
from collections import Counter
print('orders:', Counter(names[r[0]] for r in rows))
W = np.array([r[1:6] for r in rows]); Lp = np.array([r[6:11] for r in rows]); cs = np.array([r[0] for r in rows])
M = int(sys.argv[2]) if len(sys.argv) > 2 else 12
cands = []
for f in itertools.product(range(-3, 4), repeat=5):
    nz = [x for x in f if x]
    if not nz or nz[0] < 0 or np.gcd.reduce([abs(x) for x in nz]) != 1: continue
    f = np.array(f); a = np.clip(W @ f, -M, M); b = np.clip(Lp @ f, -M, M)
    sep = a != b
    cands.append((int(sep.sum()), -int(np.abs(f).sum()), tuple(int(x) for x in f), sep))
cands.sort(key=lambda x: (x[0], x[1]), reverse=True)
remaining = np.ones(len(rows), bool); chosen = []
while remaining.any():
    best = max(cands, key=lambda c: ((c[3] & remaining).sum(), c[1]))
    n = int((best[3] & remaining).sum())
    if n == 0: break
    chosen.append(best[2]); remaining &= ~best[3]
    print('form', best[2], 'separates', n, 'more; left', int(remaining.sum()), Counter(names[c] for c in cs[remaining]))
