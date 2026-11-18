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

## After contact (in progress)

| File | What it does |
| --- | --- |
| `post.cpp` | `post S`: positions reached after contact under the policy, per piece order, with the range of the race count. |
| `hull.cpp` | `hull S m`: per order, gap maxima and the dimension of the affine hull of the reached positions. |
| `learn6.cpp` | Decision-tree learner for seven gaps (2,017 linear forms with coefficients in `{−2, …, 2}`, thresholds, residues mod 2 and 3, race count). |
| `core.cpp` | `core S T`: does the outcome depend on the runners' gaps only through the race count, once each is at least `T`? |

Findings so far:

* All 19 later orders occur, with race counts from −10 to 6, and the positions reached are
  full-dimensional in every order (`hull 30 28`). No thin families appear after contact.
* Learning on boards of at most 18 empty squares gives trees of 100 to 1,200 leaves, with errors
  on boards of 24 squares. For `a = 2`, generalising trees needed training on 30 to 38 squares, and
  the seven-gap learner cannot handle that many rows as it stands.
* With a single runner (a frog left of every toad, or a toad right of every frog), its gap matters
  only through the race count (`core 22 2`: no conflicts). With two or more runners there are
  conflicts, so the reduction to a smaller core needs more care.

