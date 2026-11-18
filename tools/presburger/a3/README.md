# The row `a = 3`: the approach phase under the front-frog policy

Target: `TT□T□ᵐFFF ≤ 0` for every `m ≥ 5`, which gives the row `T³□ᵇF³` for `b ≥ 6`
(`docs/RESEARCH_NOTES.md` §10, §16).

| File | What it does |
| --- | --- |
| `ex6.h` | Exact normal play for three toads and three frogs (piece order + seven gaps, dense index). |
| `ff.cpp` | `ff S G` explores the game from `TT□T□ᵐFFF` (`m + 1 ≤ S`) with Right always moving the front frog while the centre gap is at least `G`, and any winning move otherwise; counts how often the front frog is not winning. |
| `fam.cpp` | `fam S AB` checks the whole family `□^g₀T□^g₁T□^g₂T□^g₃F□^(AB+3g₀+2g₁+g₂)FF` for every board size up to `S`: Left wins, and positions where the front-frog reply fails. |

Results (`ff 22 2`, `fam 34 -1`): the front frog never fails for `m ≤ 21`, and every position of
the family with race count `−1` is a loss for Left moving first for every number of empty squares
from 6 to 34 (at 5 empty squares, i.e. `m = 4`, all are wins, matching the known failure of the
claim there).

## After contact: the method of §15 does not carry over as it stands

See `docs/RESEARCH_NOTES.md` §17. The tools below were used for that section; all work on exact
play (`ex6.h`). Build with `g++ -O2 -fopenmp -std=c++17`.

| File | What it does |
| --- | --- |
| `close6.cpp` | `close6 S K A0 A1 DL DH`: brute-force closure of "exact losses in a race-count window" on at most `S` empty squares. `close6 22 1 -1 0 -1 1` (window `[−p − 1, p + 1]`; `TTTFFF`: centre gap at most 1, race count −1 or 0) finds no unanswered Left move. |
| `learn6.cpp` | `learn6 SL SV ORDER`: decision tree for the exact loss set of one order on that window, learned on at most `SL` empty squares and validated on `SV`. `RFILE=dump` learns membership in a dumped reachable set instead. |
| `reach6.cpp` | `reach6 S POL`: the positions reached when Right takes the first winning reply in a fixed order of his frogs; per order, the count, race-count range and gap ranges. `DUMP=file` writes them. |
| `cegar6.cpp` | `cegar6 S [OUT]`: counterexample-guided search for a small closed set inside the losses. One tree per (order, race count), learned from the positions that must be in against the Left wins of that slice; other losses are "don't care". `NMIN`, `WCAP`, `WB`, `FR`, `NZ2`, `PRIO` as in the source. |
| `rule6.cpp` | `rule6 M`: whether a fixed rule for Right with no look-ahead (five rules) wins `TT□T□ᵐFFF`. None does, for any `m` from 5 to 20. |
