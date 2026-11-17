#!/usr/bin/env python3
"""Print the README's table of exact values of T^a .^b F^a, colour-coded by where they come from.

* Published values, transcribed from the papers:
  [WW]  Winning Ways: T .^b F = b·∗ (so ∗ for odd b, 0 for even b), and T^a . F^a = ∗;
  [E96] Erickson, table in §7 (b ≤ 6 for a ≤ 2, b ≤ 8 - a for 3 ≤ a ≤ 6);
  [T11] Thanatipanonda, Figure 2 of arXiv:0804.0640v1 (a ≤ 10, b ≤ 20) and its notes
        (a = 2 up to b = 103, a = 3 up to b = 53). Its "≠ 0" cells are recorded as such.
* Computed here: tools/values.txt, the output of tools/values.cpp (whether the value is 0, ∗ or
  neither), for every cell it could finish.
A computed value that contradicts a published one is marked ⚠️ (none so far).

Usage: gen_values.py [--readme]   (run from the repository root; with --readme the table in
README.md between the markers `<!-- values table: begin/end -->` is replaced)
"""
import re
import sys

BMAX, AMAX = 30, 14
STAR, ZERO, EIGHTH, N, NONZERO = '∗', '0', '±⅛', 'N', '≠0'

pub = {}   # (a, b) -> (value, sources)


def add(a, b, v, src):
    old = pub.get((a, b))
    if old and old[0] != v:
        sys.exit(f'published values disagree at ({a}, {b}): {old} vs {v} [{src}]')
    pub[(a, b)] = (v, (old[1] if old else []) + [src])


# Winning Ways: a = 1 and b = 1 (for every a and b; the table shows a finite part)
for b in range(1, BMAX + 1):
    add(1, b, STAR if b % 2 else ZERO, 'WW')
for a in range(1, AMAX + 2):
    add(a, 1, STAR, 'WW')

# Erickson 1996, §7 (rows a, columns b)
E96 = {1: '∗0∗0∗0', 2: '∗∗∗∗00', 3: '∗' + 'E' + '0∗0', 4: '∗N∗0', 5: '∗N∗', 6: '∗N'}
for a, row in E96.items():
    for i, c in enumerate(row):
        add(a, i + 1, EIGHTH if c == 'E' else c, 'E96')

# Thanatipanonda, Figure 2 (rows a, columns b = 1, 2, ...); '#' = "≠ 0"
T11 = {
    1: '∗0∗0∗0∗0∗0∗0∗0∗0∗0∗0',
    2: '∗∗∗∗00∗00000∗00000∗0',
    3: '∗E0∗0∗0000000∗000000',
    4: '∗N∗0000∗∗00000000000',
    5: '∗N∗∗∗0∗000#0',
    6: '∗N∗∗∗∗∗#',
    7: '∗N∗∗∗##',
    8: '∗N∗∗∗',
    9: '∗N∗∗',
    10: '∗N∗∗',
}
for a, row in T11.items():
    for i, c in enumerate(row):
        add(a, i + 1, EIGHTH if c == 'E' else NONZERO if c == '#' else c, 'T11')
# Notes 1 and 2 of Figure 2
for b in range(21, 104):
    add(2, b, STAR if b % 6 == 1 else ZERO, 'T11')
for b in range(21, 54):
    add(3, b, STAR if b == 29 else ZERO, 'T11')

# Computed here
comp = {}
for line in open('tools/values.txt'):
    p = line.split()
    if len(p) >= 3 and p[2] in ('0', '*', 'other'):
        comp[(int(p[0]), int(p[1]))] = {'0': ZERO, '*': STAR, 'other': 'other'}[p[2]]


def agrees(pv, cv):
    if pv in (ZERO, STAR):
        return cv == pv
    if pv == NONZERO:
        return cv != ZERO
    return cv == 'other'          # ±⅛ and N are neither 0 nor ∗


def cell(a, b):
    p, c = pub.get((a, b)), comp.get((a, b))
    if p and c and not agrees(p[0], c):
        return f'⚠️ {p[0]}/{c}'
    if p and p[0] != NONZERO:
        return f'🔵 {p[0]}'
    if c:
        v = c if c != 'other' else (N if b == 2 else '≠0,∗')
        return f'🟠 {v}'
    if p:
        return f'🔵 {p[0]}'
    return ''


cols = [str(a) for a in range(1, AMAX + 1)] + [f'≥ {AMAX + 1}']
lines = ['| **b** \\ **a** | ' + ' | '.join(cols) + ' |', '|---:|' + ':-:|' * len(cols)]
for b in range(1, BMAX + 1):
    cells = [cell(a, b) for a in range(1, AMAX + 1)] + [cell(AMAX + 1, b) if b == 1 else '']
    lines.append(f'| **{b}** | ' + ' | '.join(cells) + ' |')
table = '\n'.join(lines)

new = sum(1 for k in comp if k not in pub or pub[k][0] == NONZERO)
checked = sum(1 for k in comp if k in pub and pub[k][0] != NONZERO)
bad = sum(1 for k in comp if k in pub and not agrees(pub[k][0], comp[k]))
summary = f'{len(comp)} cells computed: {checked} re-check published values, {new} new; {bad} disagreements'
if '--readme' in sys.argv:
    text = open('README.md').read()
    begin, end = '<!-- values table: begin -->\n', '\n<!-- values table: end -->'
    i, j = text.index(begin) + len(begin), text.index(end)
    open('README.md', 'w').write(text[:i] + table + text[j:])
    print(summary)
else:
    print(table)
    print(f'\n<!-- {summary} -->')
