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
