# The column `b = 3`: `Tᵃ □³ Fᵃ` is infinitesimal for every `a`

This note explains the Lean proof of

```lean
theorem Cgt.infinitesimal_start_b_three (a : Nat) : Infinitesimal (tf (start a 3))
```

in `Cgt/Col/Column3.lean`: the case `b = 3` of Erickson's Conjecture 5 (Conjecture 7.5 in
[E96]) for every number `a` of toads and frogs. The only column previously proved for every `a` is
`b = 2`, by Thanatipanonda [T11]. As far as we know, `b = 3` is new; it had been computed up to
`a ≈ 14`. The proof uses Lean core only and has no `sorry`.

The argument has the same outline as the row `a = 2` ([docs/ROW_A2.md](ROW_A2.md)):

1. Right's strategy, found by computer, uses finitely many *shapes*;
2. a *margin relation* shows that checking one witness per shape and choice checks every position
   of that shape;
3. the kernel checks the finite list.

The roles of pieces and gaps are swapped, though. In the row `a = 2`, four pieces are separated by
long gaps. Here three empty squares are separated by long *runs of pieces*, and the number of runs
is not fixed.

## 1. Positions as runs

A position is a list of *runs* `(c, n)`: `n` copies of the cell `c` (`Cgt/Col/Runs.lean`). A run
list is *maximal* if every run is nonempty and adjacent runs have different cells.

* `lmovesR` gives the Left moves of a maximal run list directly: the last toad of a toad run slides
  into the empty run after it, or jumps the single frog after it. The runs on either side are
  merged where needed. `mem_leftMoves_expand` proves that these are exactly the moves of the
  position.
* Right moves are mirrored Left moves (`rmovesR`, `mem_rightMoves_expand`).
* Moves keep run lists maximal.

## 2. Dead runs

Erickson's *dead pieces*: in a block of pieces with no empty square, everything from the first
`TT` to the last `FF` after it can never move again. In run terms (`DeadP`, `Cgt/Col/Dead.lean`), a
run is dead if a toad run of length `≥ 2` at or before it and a frog run of length `≥ 2` at or
after it enclose it, with no empty run in between. A dead toad run cannot move, and a dead interval
survives every move.

Dead runs matter because pieces pile into dead blocks during play. Their lengths never matter for
the game, but they would make the shapes infinite.

## 3. Shapes

The *entries* of a run list are its live toad and frog runs of length `≥ 2`. Together with an
*anchor* of value 2 they are sorted by length. The *key* of a run list (`keyOf`,
`Cgt/Col/Key.lean`) records:

* every run's cell, and its length if it is an empty run or has length 1. Of a dead run of length
  `≥ 2` only "dead" is recorded, and of an entry only "long";
* the sorted order of the entries;
* the gaps between consecutive sorted lengths, starting from the anchor. A gap is kept exactly up
  to 2; above that only its parity.

So the key keeps the *exact* difference between entries whose lengths are close, and only "far
apart, with this parity" across larger gaps. This is the column analogue of the mirrored
differences of the row `a = 2`. It is needed: plain capped lengths lose the race between Left's
toad reservoir and Right's frogs, because dead blocks absorb toads and frogs unequally.

## 4. The margin relation

`Rel j R R'` (`Cgt/Col/Rel.lean`) says:

* the two run lists have the same cells;
* their lengths are equal or both at least 2, with empty runs exact;
* every difference between two entries, or between an entry and the anchor, is equal in both or
  at least `3 + j` in both, with the same sign and parity (`close j`).

Then:

* `Rel 0` determines the key (`keyOf_eq_of_rel`).
* **Margin lemma** (`margin_left`, `Cgt/Col/Margin.lean`). If `Rel (j + 2) R R'`, then every Left
  move of `R` has a corresponding Left move of `R'` with `Rel j`. Every Left move has one form,
  `moveX A n J m C`. The prefix `A` and the suffix `C` survive, with at most their boundary runs
  lengthened. A dead interval cannot contain the moving toad or the empty run beside it. So every
  entry of the result comes from an entry of `R` shifted by at most 1, or is a new run of length 2
  (`origin`), and every difference moves by at most 2.
* The same holds for Right moves by mirroring (`margin_right`, `Cgt/Col/Mirror.lean`).
* **Witness completeness** (`wit_complete`, `Cgt/Col/Wit.lean`). Every maximal run list has a
  witness of its key within margin 4: compress every sorted gap above 8 to 7 or 8, keeping its
  parity. The witnesses of a key (`witOf`) realise each capped gap `c` by `c`, `c + 2` or `c + 4`.

## 5. The finite check and soundness

`checkCol` (`Cgt/Col/Check.lean`) checks, for every witness of every key:

* Left-stop phase (`U` keys; Right still holds his pass): Left's pass and every Left move can be
  answered by Right's pass (a normal-play key) or by a Right move to a `U` key;
* normal play (`N` keys): every Left move has a Right reply with an `N` key.

The soundness theorem `sound` (`Cgt/Col/Sound.lean`) is an induction on `pot`, as for the row
`a = 2`, using the three properties above. If the check passes, every run list with an `N` key is
`≤ 0`, and every one with a `U` key has Left stop `≤ 0`. The start `Tᵃ□³Fᵃ` has a `U` key for every
`a ≥ 2` (`key_s3`; beyond `a = 6` the key depends only on the parity of `a`). Its Left stop is
therefore `≤ 0`, so it is infinitesimal.

## 6. The data and the kernel check

* `tools/column/col_shapes.cpp` finds the shapes. It solves the game on shapes with backtracking,
  then minimises the set greedily. Its settings: cap and gap threshold 2, margin 4 per round,
  dead runs kept one by one. Right may use at most 10 runs, which is enough for every `a` tested.
* `scripts/ColGen.lean` translates the shapes into Lean keys and checks the closure with the Lean
  definitions. It writes `Cgt/Col/B3Data.lean`: 382 Left-stop keys and 2,649 normal-play keys,
  with 10,275 witnesses.
* `scripts/gen_col_chunks.py` splits the check into chunks of bounded work, one theorem each,
  evaluated by `decide +kernel`. That gives 16 files `Cgt/Col/B3Check*.lean` of about 2 minutes
  each; the kernel needs too much memory for one big check.
* `B3Blocks.lean` and `B3.lean` reassemble the chunks.

Independent checks of the same certificate:

* `tools/column/verify_shapes.py` re-implements everything in Python and finds the set closed;
* `tools/column/col_realcheck.cpp` checks Right's strategy on the real boards for every `a` up to
  40.

## 7. Files

| File | Contents |
| --- | --- |
| `Cgt/Col/Runs.lean` | Run lists, explicit Left moves, mirror, Right moves, maximality |
| `Cgt/Col/Key.lean` | Dead runs, entries, keys, witnesses (all computable) |
| `Cgt/Col/Check.lean` | Key trees and the finite check |
| `Cgt/Col/Rel.lean` | `close`, skeletons, `Rel`, `keyOf_eq_of_rel` |
| `Cgt/Col/Dead.lean` | Characterisations of dead runs and entries |
| `Cgt/Col/Margin.lean` | The structure of a Left move, origins of entries, `margin_left` |
| `Cgt/Col/Mirror.lean` | `Rel` under mirroring, `margin_right` |
| `Cgt/Col/Wit.lean` | `wit_complete` |
| `Cgt/Col/Sound.lean` | The soundness theorem |
| `Cgt/Col/B3Data.lean`, `B3Check*.lean`, `B3Blocks.lean`, `B3.lean` | The data, the kernel check, the start keys |
| `Cgt/Col/Column3.lean` | `infinitesimal_start_b_three` |

## 8. Other columns

The same framework applies to any fixed `b`; only the data changes. For `b = 4` and `b = 5` the
smallest number of runs Right needs is 12 and 13 for every `a` tested
([docs/RESEARCH_NOTES.md](RESEARCH_NOTES.md) §13). Whether their shape searches close, and at what
size, is untested.

## References

* **[E96]** Jeff Erickson, *New Toads and Frogs Results*. In R. J. Nowakowski (ed.), *Games of No
  Chance*, MSRI Publications 29, Cambridge University Press, 1996, pp. 299–310.
* **[T11]** Thotsaporn Thanatipanonda, *Further Hopping with Toads and Frogs*. Electronic Journal
  of Combinatorics 18(1), 2011, #P67. arXiv:0804.0640.
