import numpy as np, pandas as pd, itertools, sys
DF = pd.read_csv('np22_40.txt', sep=' ', header=None, names=['c','g0','g1','g2','g3','g4','LF','RF'], dtype=np.int16)
names = {3:'TTFF',5:'TFTF',9:'TFFT',6:'FTTF',10:'FTFT',12:'FFTT'}
S = 40
def coef(c, k):
    return sum(1 for i in range(k) if (c>>i)&1) - sum(1 for i in range(k,4) if not (c>>i)&1)
cands = []
for f in itertools.product(range(-3, 4), repeat=5):
    if all(x == 0 for x in f): continue
    nz = [x for x in f if x]
    if nz[0] < 0: continue                      # sign normalisation
    if np.gcd.reduce([abs(x) for x in nz]) != 1: continue
    cands.append(np.array(f))
def run(c, C, M, margin, col, maxforms=4):
    X = DF[DF.c == c]
    G = np.stack([X['g%d' % i].to_numpy().astype(np.int32) for i in range(5)], 1)
    keep = G.sum(1) <= S - margin; G = G[keep]; y = X[col].to_numpy()[keep]
    a = np.array([coef(c, k) for k in range(5)])
    base = np.concatenate([np.where(G < C, G, C + (G - C) % 6), (G @ a)[:, None]], 1)
    forms = []
    def key_ids(cols):
        _, inv = np.unique(cols, axis=0, return_inverse=True); return inv.ravel()
    cols = base
    for step in range(maxforms + 1):
        kid = key_ids(cols)
        df = pd.DataFrame({'k': kid, 'y': y})
        g = df.groupby('k')['y'].agg(['min', 'max']); bad = g.index[g['min'] != g['max']]
        nbad = len(bad)
        print(f'  {names[c]} {col} forms={[tuple(int(v) for v in f) for f in forms]}: {nbad} conflicting keys', flush=True)
        if nbad == 0 or step == maxforms: return forms
        mask = np.isin(kid, bad); Gb = G[mask]; kb = kid[mask]; yb = y[mask]
        best = None
        for f in cands:
            v = np.clip(Gb @ f, -M, M)
            d = pd.DataFrame({'k': kb, 'v': v, 'y': yb}).groupby(['k', 'v'])['y'].agg(['min', 'max'])
            nb = int((d['min'] != d['max']).sum())
            if best is None or nb < best[0]: best = (nb, f)
        forms.append(best[1]); cols = np.concatenate([cols, np.clip(G @ best[1], -M, M)[:, None]], 1)
for c in [3, 5, 9, 6]:
    run(c, 8, 12, 10, 'LF'); run(c, 8, 12, 10, 'RF')
