#!/usr/bin/env python3
"""Print the README's table of proved cases, read from the Lean sources.

* Whole families: a <= 2 (Cgt/RowA2.lean, FamilyA1, Basic), b <= 1, and b = 2 with a >= 4.
* Single cases checked by kernel `decide`: the `start a b` cases in Cgt/FiniteCases.lean.
* Strategy certificates: the CgtCerts roots in lakefile.toml.
* (3, 2): proved not infinitesimal.
* Otherwise: confirmed by the exact solver (README "Computational evidence") or not computed.

Usage: gen_grid.py   (run from the repository root)
"""
import re

AMAX, BMAX = 14, 28
# Largest b confirmed by the exact solver, per a (README "Computational evidence").
SOLVER = {2: 28, 3: 26, 4: 24, 5: 16, 6: 10, 7: 8, 8: 6, 9: 5, 10: 4, 11: 4, 12: 4, 13: 3, 14: 3}

kernel = {(int(a), int(b)) for a, b in re.findall(r'start (\d+) (\d+)', open('Cgt/FiniteCases.lean').read())}
certs = {(int(a), int(b)) for a, b in re.findall(r'Case_(\d+)_(\d+)', open('lakefile.toml').read())}


def mark(a, b):
    if (a, b) == (3, 2):
        return '❌'
    if a <= 2 or b <= 1 or (b == 2 and a >= 4):
        return '🟩'
    if (a, b) in kernel:
        return '🔵'
    if (a, b) in certs:
        return '🔶'
    if b <= SOLVER.get(a, -1):
        return '·'
    return ''


cols = [str(a) for a in range(AMAX + 1)] + ['≥ 15']
print('| **b** \\ **a** | ' + ' | '.join(cols) + ' |')
print('|---:|' + ':-:|' * len(cols))
for b in range(BMAX + 1):
    cells = [mark(a, b) for a in range(AMAX + 1)] + [mark(99, b)]
    print(f'| **{b}** | ' + ' | '.join(cells) + ' |')
