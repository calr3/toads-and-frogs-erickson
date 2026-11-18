import subprocess, numpy as np, itertools, sys
S = int(sys.argv[1]); C = int(sys.argv[2]); M = int(sys.argv[3]); forms = sys.argv[4:]
cands = []
for f in itertools.product(range(-3, 4), repeat=5):
    nz = [x for x in f if x]
    if not nz or nz[0] < 0 or np.gcd.reduce([abs(x) for x in nz]) != 1: continue
    cands.append(np.array(f))
F = np.array(cands)                       # (nc, 5)
for rnd in range(30):
    p = subprocess.run(['./adjconf', str(S), str(C)] + forms, capture_output=True, text=True)
    rows = np.array([list(map(int, l.split())) for l in p.stdout.splitlines()]) if p.stdout.strip() else np.zeros((0, 12), int)
    print(f'round {rnd}: {len(forms)} forms, {len(rows)} adjacent conflicts', flush=True)
    if len(rows) == 0: break
    G = rows[:, 2:7]; H = G + 6 * rows[:, 7:12]
    a = np.clip(G @ F.T, -M, M); b = np.clip(H @ F.T, -M, M)
    sep = (a != b).sum(0)                  # pairs separated by each candidate
    cost = np.abs(F).sum(1)
    k = max(range(len(cands)), key=lambda i: (sep[i], -cost[i]))
    f = cands[k]; forms.append(','.join(str(int(x)) for x in f) + f':{M}')
    print(f'   add {tuple(int(x) for x in f)}:{M} separating {sep[k]} of {len(rows)}', flush=True)
print('forms:', ' '.join(forms))
