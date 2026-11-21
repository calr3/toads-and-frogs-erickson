# Positions with one frog

Tools behind the proof of Thanatipanonda's Conjecture T1 (`Cgt/OneFrog/`,
[docs/ONE_FROG.md](../../docs/ONE_FROG.md)). Positions are strings such as `TT..F.`.

| Tool | What it does |
| --- | --- |
| `bounds.py` | For a one-frog position, the least integer `≥` the value (`U`, at least 0) and the greatest integer `≤` it (`Lw`, or −1), by Conway's recursion for comparing with an integer. Also `phi`. No canonical forms, so it reaches boards of 15 squares and more. |
| `check_rules.py MAXLEN` | Checks every step of the induction on all one-frog positions of at most `MAXLEN` squares: each claimed bound must follow from the claims about the positions one or two moves later. `python3 check_rules.py 15` checks 1,094,386 claims with no failure (a few minutes). |

The claims in `check_rules.py` are those of `Cgt/OneFrog/Lower.lean` and `Upper.lean`, with the
degenerate families written as shapes (`packed`) where the Lean proof uses `phi = -2` and
`phi = -1`.
