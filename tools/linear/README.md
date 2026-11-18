# Odd `b` of the row `a = 2`: shapes with a race counter (work in progress)

Goal: prove `TT□ᵇFF = 0` for odd `b ≡ 3, 5 (mod 6)` and `= ∗` for `b ≡ 1 (mod 6)`, the half of
Thanatipanonda's Conjecture T2 not yet proved (`docs/RESEARCH_NOTES.md` §12, §15). By the
reductions of §12 this means two normal-play claims, Left moving first:

* `T□T□ᵏF□F ≤ 0` for `k ≡ 1, 3 (mod 6)` (then `TT□ᵏ⁺²FF = 0`);
* `TT□ᵏF□F ≤ 0` for `k ≡ 0 (mod 6)` (then `TT□ᵏ⁺¹FF = ∗`).

Exact play (`np22.cpp`) confirms the data: `T□T□ᵏF□F ≤ 0` exactly when `k ≢ 5 (mod 6)` (`k ≥ 6`),
and `TT□ᵏF□F ≤ 0` exactly when `k ≡ 0 (mod 6)`.

## The idea

Finite shapes with capped gaps fail here because the mirrored gaps drift apart by about `2k/3`.
Instead, keep one exact linear quantity, the race count `A − B` (the empty squares in front of the
toads minus those in front of the frogs). A slide changes it by one, a jump by two, so along any
game from these starts it stays within `±4` of its start value: there are at most four jumps.

* **Outcomes are thresholds in `A − B`.** For a fixed key (piece order, capped gaps), "Left moving
  first wins" holds exactly when `A − B` is at least a threshold, for every order. Example (`TTFF`,
  outer gaps at least 4): Left wins exactly when `⌊(A − B)/2⌋ ≥ [g₃ − g₁ ≥ 2]` (centre gap odd) or
  `≥ [g₃ − g₁ ≥ 0]` (centre gap even).
* **Runners.** A frog with no toad to its left, or a toad with no frog to its right, only adds an
  integer (Erickson's Finished Frogs and Terminal Toads theorems), and that integer is already part
  of `A − B`. Keys work best on the position with runners removed and their gaps merged.

## Tools

| Tool | What it does |
| --- | --- |
| `np22.cpp` | Exact normal play for two toads and two frogs, every position with at most `S` empty squares. |
| `absgame.cpp` | Threshold abstraction on the exact data: `A − B ≤ T(key)`, as a greatest fixpoint over all positions with at most `S` empty squares. Keys per runner-reduced pattern (`CFG` file: caps with residues, clamped differences of merged gaps). `ABKEY=1` puts the exact `A − B` into the key; `ABSREACH=k` computes the closed set of shapes reached from the starts. |
| `absplain.cpp` | The exact abstract game, independent of data: shapes are (order, gaps capped at `C` with residue mod 6, exact `A − B`); moves act on shapes, with both outcomes kept when a capped gap at the cap goes down, and shapes that no position realizes dropped. Sound for every board size. |
| `absform.cpp` | The same with one more component, a linear form `F` of the gaps clamped to `[−M, M]`; each case of a move is checked for realizability together with the shape it comes from. `MIXED=t` lists lost shapes whose realizations (capped gaps up to `C + 5 + 6t`) disagree in exact play: comparisons the shape still lacks. |
| `forms.py` | Greedy search, on exact data, for linear forms that make the outcome a function of the shape. |

## Status

* On exact data up to 30 empty squares, keys on runner-reduced positions with clamped differences
  prove every true start and no false one; with the exact `A − B` in the shape, the set closed under
  play from the starts is finite (13,319 Left-to-move and 17,730 Right-to-move shapes with
  `cfg_greedy.txt`; it stops growing after `k = 18`).
* The exact abstract game with plain capped gaps (`absplain.cpp`) proves only starts with `k < C`.
  Positions with several large gaps need comparisons between gaps, and not only pairwise
  differences: on `□^0 T □^g₁ T □^g₂ F F □^g₄` with `A − B = 0`, the outcome is periodic in `g₂`
  with period 6 only once `g₂` exceeds about `1.5·g₁ + 5`. Data with at most 30 empty squares hides
  this, so the data-driven results above are not yet a proof.
* `forms.py` finds one form that removes every conflict on the data up to 30 empty squares:
  `F = g₂ − 2g₃ − 3g₄` (gaps capped at 8, `F` clamped to `±12`). In the exact abstract game
  (`absform.cpp 8 12`, about 5 million shapes, 6 minutes) it proves `T□T□ᵏF□F ≤ 0` for every true
  case `k ≤ 13` and `TT□ᵏF□F ≤ 0` for `k = 6, 12`, but not beyond.
* `MIXED` shows why: on larger boards some shapes still merge wins and losses. Two `TTFF`
  positions `□⁵T□ᵍT□F□ᵍF□⁵` with `g = 9` and `g = 21` (same shape, `A − B = 0`) are a Left win and
  a Right win; this needs a comparison such as `g₁` against `2g₀`. In `TFTF`, the order of the
  centre gap and a waiting gap matters when all are large.
* Next: add these forms, and search lazily (only Right's chosen replies) to keep the number of
  shapes manageable. For Lean, the realizability filter must never reject a real shape: either an
  exact decision with a proof, or certificates of infeasibility (Farkas multipliers, divisibility).
