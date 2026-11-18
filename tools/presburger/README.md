# Odd `b` of the row `a = 2`: a linear invariant, checked by Z3

Goal (Thanatipanonda's Conjecture T2, odd half): `T□T□ᵏF□F ≤ 0` for `k ≡ 1, 3 (mod 6)` and
`TT□ᵏF□F ≤ 0` for `k ≡ 0 (mod 6)` (see `docs/RESEARCH_NOTES.md` §12).

## Right's strategy

* **Approach (`TTFF`).** Right always moves the front frog. Every Left move changes the race count
  `A − B` by `−1` and Right's answer by `+1`, and the rear frog never moves, so the positions stay in
  the family `□^g₀ T □^g₁ T □^g₂ F □^(2g₀+g₁+ab) F` with `ab = 0` (or `ab = 1` after
  `TT□ᵏF□F → T□T□ᵏ⁻¹F□F → T□T□ᵏ⁻²F□□F`). Exact play shows every position of the family is a loss
  for Left moving first when the number of empty squares `N` is `≡ 3, 5 (mod 6)` (`ab = 0`) or
  `≡ 1 (mod 6)` (`ab = 1`).
* **Contact and after.** Right moves into the set of exact losses. For every piece order after the
  first jump, that set is described by a small decision tree over linear forms of the gaps, their
  residues mod 2 and 3, and the race count (`treeC.txt`; `C` is the order, bit `i` set when piece `i`
  is a toad): `FFTT` 2 leaves, `FTFT` 6, `FTTF` 16, `TFFT` 32, `TFTF` 49, and the contact region of
  `TTFF` (centre gap at most 1) 19.

## Files

| File | What it does |
| --- | --- |
| `ex.h` | Exact solver for two toads and two frogs (every position with at most `S` empty squares). |
| `learn.cpp` | Learns a decision tree for "Left moving first wins" on exact data and validates it on larger boards. `EXPORT=file` writes the tree. |
| `z3check.py`, `verify.py` | Z3 check that the invariant `good` is closed: from every `good` position, every Left move has a Right reply into `good`. The gaps are unbounded integers, so this covers every board size. |
| `goodcheck.cpp` | Brute-force sanity check: every `good` position with at most `S` empty squares is an exact loss for Left moving first (`S = 44`: 574,840 positions, no exception). |

`good` is: the race count lies between `−p` and `p + 1`, where `p` is the number of toad–frog pairs
that have already passed each other, and

* `TTFF`: the two families above (`g₄ = 0`, `N ≥ 9` resp. `N ≥ 7`), or centre gap at most 1,
  race count 0 or 1 and `tree3.txt` says loss;
* any other order: its tree says loss.

The starts are in `good`: `T□T□ᵏF□F` is in the first family for `k ≥ 7`, `k ≡ 1, 3 (mod 6)`, and
for `k ≡ 0 (mod 6)`, `k ≥ 6`, the position after `TT□ᵏF□F → T□T□ᵏ⁻¹F□F → T□T□ᵏ⁻²F□□F` is in the second.

Status: `python3 verify.py` reports no failure. The Lean proof (closure by `omega`) is in progress.
