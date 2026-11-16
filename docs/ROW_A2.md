# The row `a = 2`: `TT □ᵇ FF` is infinitesimal for every `b`

This note explains the Lean proof of

```lean
theorem Cgt.infinitesimal_start_two (b : Nat) : Infinitesimal (tf (start 2 b))
```

in `Cgt/RowA2.lean`, the case `a = 2` of Erickson's Conjecture 5 for every number `b` of empty
squares. The proof uses Lean core only, has no `sorry`, and depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The argument has three parts:

1. A reduction to one normal-play claim, `T□T□ᵐFF ≤ 0`.
2. A strategy for Right in that game, found by computer, in which every position falls into one
   of 1,543 *shapes*.
3. A general theorem saying that such a strategy can be checked on finitely many positions,
   followed by that check, done by the Lean kernel.

## 1. Background

`tf p` is the game of the Toads and Frogs position `p` (`Cgt/ToadsFrogs.lean`). Left moves toads
(`T`) rightwards, Right moves frogs (`F`) leftwards; a piece slides into an adjacent empty square
`□` or jumps over one opposing piece into the empty square behind it.

A game is *infinitesimal* if it lies strictly between `−2⁻ⁿ` and `2⁻ⁿ` for every `n`. The start
`Tᵃ□ᵇFᵃ` is its own mirror image with the colours swapped, so its game equals its own negative.
Then it is infinitesimal exactly when its **Left stop is `≤ 0`** (`infinitesimal_start_iff`).
`Cgt/Infinitesimal.lean` turns this into a purely combinatorial recursion with no numbers:

* `UpperZero G` (Left stop `≤ 0`) holds iff `LfZero G` holds and `LfZero Gᴸ` holds for every Left
  option `Gᴸ`.
* `LfZero G` (Right stop `≤ 0`) holds iff `G ≤ 0` or `UpperZero Gᴿ` holds for some Right option
  `Gᴿ`.

Informally: Right may answer a Left move by *passing*, but only once, and only if the position
is then `≤ 0`. Here `G ≤ 0` is ordinary normal play: Right, moving second, wins. A symmetric
position always satisfies `LfZero`.

## 2. Reduction to one normal-play claim

For `b ≥ 2`, the start `TT□ᵇFF` has a single Left move: the front toad slides, giving
`T□T□ᵐFF` with `m = b − 1`. So `UpperZero (TT□ᵇFF)` follows from two facts:

* `LfZero (TT□ᵇFF)`, which holds because the start is symmetric;
* `LfZero (T□T□ᵐFF)`, which holds if `T□T□ᵐFF ≤ 0`, because then Right passes.

The cases `b = 0` and `b = 1` are covered by earlier theorems (`infinitesimal_start_b_zero`,
`infinitesimal_start_b_one`). So the row reduces to:

> **Claim.** For every `m ≥ 1`, `T□T□ᵐFF ≤ 0`: Left moves first and loses.

(It is false for `m = 0`. An exact search for every `m ≤ 39` was the first sign that it holds.)

## 3. Right's strategy

A position with two toads and two frogs is a *piece order* (one of `TTFF`, `TFTF`, `TFFT`, `FTTF`,
`FTFT`, `FFTT`; toads never pass toads) together with five gaps:

```
□^g₀ c₁ □^g₁ c₂ □^g₂ c₃ □^g₃ c₄ □^g₄
```

Pair each gap with its mirror image: `g₀` with `g₄`, `g₁` with `g₃`, and `g₂` with itself.
Right's strategy keeps the two **mirrored differences** `g₄ − g₀` and `g₃ − g₁` between `−2` and
`2`. This is always possible (with look-ahead), and it wins.

Here is a typical line from `T□T□⁶FF`. Left moves first in each row, then Right answers:

```
T.T......FF
.TT......FF  ->  .TT.....F.F
.T.T....F.F  ->  .T.T....FF.
..TT....FF.  ->  ..TT...F.F.
..T.T..F.F.  ->  ..T.T..FF..
...TT..FF..  ->  ...TT.F.F..
...T.TF.F..  ->  ...TFT..F..
...TF.T.F..  ->  ...TF.TF...
....FTTF...  ->  ...F.TTF...
...F.T.FT..  ->  ...F.TF.T..
...F..FTT..  ->  ...F.F.TT..
```

During the approach, the replies above are exactly *delayed mirroring*: Right copies Left's
previous move, mirrored. Two simpler strategies fail:

* **Delayed mirroring throughout** breaks down when the pieces meet. From `□ⁱTTF□F□ⁱ⁻¹` a Left
  jump makes the copy illegal, and from `□ⁱTT□F□F□ⁱ⁻¹` a Left slide makes the copy lose.
* **Greedily choosing the reply closest to symmetric** keeps the mirrored differences small when
  `m` is odd, but lets them grow without bound when `m` is even.

## 4. Shapes

The *shape* of a four-piece position (`P4.shape` in `Cgt/Shape4.lean`) records:

* the piece order;
* the mirrored differences `g₄ − g₀` and `g₃ − g₁`, exactly;
* `min(g₀, g₄)`, `min(g₁, g₃)` and `g₂`, each **capped** at 4. Values below 4 are kept; above 4
  only the parity is kept.

The shape of `T□T□ᵐFF` is `(TTFF, 0, −1, 0, 0, cap m)`, so every claim position has one of five
shapes (`cap m ∈ {1, 2, 3, 4, 5}`, where 4 and 5 mean "at least 4, even" and "at least 5, odd").

Positions of the same shape behave the same way under a few moves. To say this precisely, define
`Rel j p q`, *same shape with margin `j`*, to mean:

* the piece orders and mirrored differences agree;
* each capped quantity is either equal in `p` and `q`, or at least `4 + j` in both with the same
  parity.

**Margin lemma.** If `Rel (j + 1) p q` and `p` has a move of a given piece, then `q` has the move
of the same piece, and the results satisfy `Rel j`. (`lm1_rel` … `rm4_rel`, `lms_rel`,
`rms_rel`.)

The reasons:

* A move changes each gap by at most one, so every capped quantity changes by at most one, and
  the mirrored differences change identically in `p` and `q`.
* A move is legal depending only on which gaps are zero and on the piece order, and these agree
  in `p` and `q`, since a capped quantity of at least `4 + j + 1` is never zero.

**Equal shapes.** `Rel 0 p q` implies `shape p = shape q` (`shape_eq_of_rel`).

**Normal forms.** Lowering a capped quantity by an even amount while keeping it at least 6
(and shifting both gaps of a mirrored pair together) gives `P4.norm p`, with `Rel 2 p (norm p)`
(`rel_norm`). The normal form takes only finitely many values per shape: the *witnesses* `wit s`,
at most eight per shape (`norm_mem_wit`).

## 5. The finite check and the soundness theorem

Let `t` be a set of shapes. The finite check `checkAll t` (`Cgt/Shape4.lean`) says:

> For every shape `s` in `t`, every witness `w` of `s`, and every Left move `w → q`, some Right
> move `q → r` leads to a position `r` whose shape is in `t`.

```lean
theorem le_zero_of_good (t : KTree) (ht : checkAll t = true) :
    ∀ (n : Nat) (p : P4), pot p.toList < n → good t p = true → le (tf p.toList) zero
```

**Proof sketch** (by induction on `pot`, the number of moves left):

1. Take a position `p` whose shape is in `t`, and a Left move `p → q`. Let `w = norm p`, so
   `Rel 2 p w`, and `w` is a witness of a shape in `t`.
2. By the margin lemma, the same piece moves in `w`, giving `w → q_w` with `Rel 1 q q_w`.
3. The finite check gives a Right reply `q_w → r_w` with the shape of `r_w` in `t`.
4. By the margin lemma again, the same frog moves in `q`, giving `q → r` with `Rel 0 r r_w`. So
   `r` has the same shape as `r_w`, which is in `t`.
5. `r` has fewer moves left than `p`, so by induction `r ≤ 0`. Hence every Left move from `p`
   has a Right reply that is `≤ 0`, i.e. `p ≤ 0`.

The bridge to the actual game is `leftMoves_toList` / `rightMoves_toList` in `Cgt/Four.lean`.
They show that the explicit moves of a four-piece position are exactly the moves of `TF.leftMoves`
and `TF.rightMoves` on the corresponding list of cells.

## 6. The data and the kernel check

`scripts/gen_row2.py` computes the set of shapes:

* It starts from the five shapes of `T□T□ᵐFF` and repeatedly takes every witness and every Left
  move.
* It chooses Right's reply with an exact solver, preferring shapes already found, then replies
  that keep the mirrored differences within 2 for ever.
* It adds the reply's shape, until nothing new appears.

| | |
| --- | --- |
| Shapes | 1,543 |
| …by piece order | `FTFT` 527, `FFTT` 469, `TTFF` 246, `TFTF` 238, `TFFT` 52, `FTTF` 11 |
| Witnesses | 3,599 |
| Left moves checked | 6,661 |
| Mirrored differences | `g₄ − g₀ ∈ [−2, 0]`, `g₃ − g₁ ∈ [−2, 2]` |

The shapes are encoded as numbers (`Shape.key`) and stored in a balanced search tree in
`Cgt/RowA2Data.lean`. `checkA2 : checkAll treeA2 = true` is proved by `decide +kernel`, and
`Cgt/RowA2.lean` takes about 30 seconds to check.

The Lean check does not trust the generator. The kernel recomputes every witness, move and
shape itself; the generator only proposes which shapes to include.

## 7. Files

| File | Contents |
| --- | --- |
| `Cgt/Four.lean` | Four-piece positions `P4`, their moves `lm1..lm4`, `rm1..rm4`, and the lemmas tying them to `TF.leftMoves` / `TF.rightMoves` |
| `Cgt/Shape4.lean` | Shapes, `Rel`, the margin lemma, normal forms and witnesses, keys and `KTree`, `checkAll`, `le_zero_of_good` |
| `Cgt/RowA2Data.lean` | The 1,543 shapes (generated) |
| `Cgt/RowA2.lean` | `checkA2`, the claim `q2_le_zero`, the reduction, and `infinitesimal_start_two` |
| `scripts/gen_row2.py` | Generates `Cgt/RowA2Data.lean` |
| `tools/regular/a2_strategy.py`, `a2_abstract.py` | The exploratory versions of the strategy and of the abstract check |

To check: `lake build Cgt.RowA2` (or `lake build` for everything). To regenerate the data:
`python3 scripts/gen_row2.py > Cgt/RowA2Data.lean`.

## 8. Limits of the method

The same reduction holds for `a = 3`: `TT□T□ᵐFFF ≤ 0` for `5 ≤ m ≤ 20`. But no strategy for Right
keeps the mirrored differences bounded there: the bound needed grows with the board. Shapes
built on the race count instead, and an analysis of the phase before the pieces meet, found no
finite description either. See `docs/RESEARCH_NOTES.md` §10.
