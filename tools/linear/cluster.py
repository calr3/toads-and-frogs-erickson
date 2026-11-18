import numpy as np, itertools, sys
from collections import defaultdict
names = {3:'TTFF',5:'TFTF',9:'TFFT',6:'FTTF',10:'FTFT'}
def coef(c, k): return sum(1 for i in range(k) if (c>>i)&1) - sum(1 for i in range(k,4) if not (c>>i)&1)
rows = [list(map(int, l.split())) for l in open(sys.argv[1])]
cl = defaultdict(list)
for r in rows:
    c, side, g, d = r[0], r[1], np.array(r[2:7]), np.array(r[7:12])
    ab = sum(coef(c, k) * g[k] for k in range(5))
    cl[(c, side, ab, tuple(d))].append(g)
cands = [np.array(f) for f in itertools.product(range(-3, 4), repeat=5) if any(f) and next(x for x in f if x) > 0]
res = []
for key, pts in sorted(cl.items(), key=lambda kv: -len(kv[1])):
    if len(pts) < 8: continue
    P = np.array(pts); c, side, ab, d = key; d = np.array(d)
    best = None
    for f in cands:
        if f @ d == 0: continue
        v = P @ f; rng = v.max() - v.min()
        k = (rng, np.abs(f).sum())
        if best is None or k < best[0]: best = (k, f, v.min(), v.max())
    (rng, _), f, lo, hi = best
    res.append((names[c], 'LF' if side == 0 else 'RF', ab, tuple(d), len(pts), tuple(int(x) for x in f), int(lo), int(hi)))
    print(f'{names[c]} {"LF" if side == 0 else "RF"} ab={ab:3d} d={tuple(d)} n={len(pts):4d}: form {tuple(int(x) for x in f)} in [{lo}, {hi}]', flush=True)
