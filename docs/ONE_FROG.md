# Positions with one frog: Thanatipanonda's Conjecture T1

`conjectureT1 : ConjectureT1` (`Cgt/OneFrog/Main.lean`; statement in `Cgt/Statement.lean`, checked
with Comparator) gives the value of `□ˡ Tᵃ □ᵇ F □ʳ` for every `a ≥ 1` and `l ≤ r`. It follows from
a theorem about every position with one frog, with the toads anywhere (`value_room_*`,
`Cgt/OneFrog/T1.lean`). Everything is checked by the kernel; there is no `native_decide`.

## 1. The conjecture

Conjecture 1 of the preprint of [T11] (T1 in the journal version), with `n = (a − 1)(b − 1 + r)`:

| Case | Value of `□ˡ Tᵃ □ᵇ F □ʳ` | Lean |
| --- | --- | --- |
| `r − l ≥ 2` | `(r − l − 1) + n` | `t1_far` |
| `l = r − 1`, `b` even | `n` | `t1_near_even` |
| `l = r − 1`, `b` odd | `n + ½` | `t1_near_odd` |
| `l = r`, `b` even | `n` | `t1_equal_even` |
| `l = r`, `b` odd | `n∗ = {n \| n}` | `t1_equal_odd` |
| `l = r = 0`, `b = 1`, `a ≥ 2` (`Tᵃ□F`) | `{{a − 2 \| 1} \| 0}` | `t1_exception` |

Two remarks on the statement.

* **`Tᵃ F`.** For `l = r = 0`, `b = 0` and `a ≥ 2` the formula `(a − 1)(b − 1 + r)` is negative,
  but `Tᵃ F = 0` (nobody can move). The preprint states the conjecture for `b ≥ 0`, so as printed
  it is false there. `valueT1` uses the subtraction of natural numbers, which gives `0`, and
  `ConjectureT1` is true as stated for every `a ≥ 1`, `l ≤ r`.
* **Sources.** We read the statement in the arXiv preprint (0804.0640v1). We could not extract the
  text of the journal version to compare the wording.

**What was known.** Erickson [E96] proved two families of these values, by counting arguments:

* `l = r = 0`, the starting positions `Tᵃ□ᵇF`: his Theorem 5.2, which already has the exception
  `Tᵃ□F = {{a − 2 | 1} | 0}` (from *Winning Ways*) and `T□ᵇF = b·∗` (his Lemma 5.1);
* `b = 0`, the blocks `□ˡTᵃF□ʳ`, for every `l` and `r`: his Lemmas 4.3 and 4.4
  (`□ˡTᵃF□ʳ = (a − 2)(r − 1) + □ˡTTF□ʳ`, with four cases for `□ˡTTF□ʳ`), and Lemma 4.1 for one
  toad.

A third family is known from Thanatipanonda's library of results found by the symbolic
finite-state method of [TZ07]: one frog with at most five empty squares on the board, any number
of toads, in any order. We have not seen the library, only three values quoted from it in a
manuscript, *Three Results of Combinatorial Game Toads and Frogs* (2011, private communication):
`Tᵃ□TᵇF□ = a` and `Tᵃ□□F = a − 1`, which are cases of §2 with `room = 0`, and `Tᵃ□□TF = a`, which
has `room = −2`.

Conjecture T1 joins Erickson's two families: a gap `b ≥ 1` together with empty squares at the
ends, for any number of empty squares. That is what is new here, with the general theorem of §2;
the known cases are covered by the same proof. The preprint of [T11] proves nothing about
positions with one frog and lists the class as future work.

## 2. The general theorem

Take any position with exactly one frog and at least one toad to its left. The toads right of the
frog have been *passed*. Define

* **`phi`**: Left's moves minus Right's moves if every toad left of the frog jumps it and the frog
  walks to the left end. With `k` toads on a board of `N` squares, the toads at `x₁ < … < x_k` and
  the frog at `f` (squares numbered from 0), and `m` toads left of the frog,
  `phi = Σᵢ (N − k + i − 1 − xᵢ) − m − f`;
* **`room`**: the number of empty squares right of the frog minus the number of empty squares left
  of the toad nearest the frog on its left;
* **`gap`**: the number of empty squares between that toad and the frog.

| `room` | `gap` even | `gap` odd |
| --- | --- | --- |
| `≥ 2` | `phi` | `phi` |
| `1` | `phi` | `phi + ½` |
| `0` | `phi + 1` (if `phi ≥ −1`) | `(phi + 1)∗` (if `phi ≥ 0`) |

(`value_room_ge_two`, `value_room_one_even`, `value_room_one_odd`, `value_room_zero_even`,
`value_room_zero_odd`; `value_one_toad_odd` covers one toad with `phi = −1`, which is `∗`.)

For `□ˡ Tᵃ □ᵇ F □ʳ`: `room = r − l`, `gap = b` and `phi = (a − 1)(b − 1 + r) + (r − l − 1)`.

For `room < 0` the values are not this regular: with `room = −1` and an odd gap they include
`3/2`, `7/4` and `{2 | 2}` above `phi`. The proof needs only bounds there.

## 3. Why it works

* **The frog never has a choice.** It can slide if the square on its left is empty, or jump if
  that square holds a toad and the next one is empty. So Right's only decision is whether to move.
* **Comparing with a number is a one-step recursion.** For an integer `n ≥ 1`, `G ≤ n` if and only
  if every Left option `Gᴸ` satisfies `Gᴸ ≤ n − 1` or has a Right option `≤ n`; `G ≤ 0` if and only
  if every `Gᴸ` has a Right option `≤ 0`. There are similar rules for `≥ n` and for `n + ½` and
  `n∗` (`Cgt/OneFrog/Num.lean`). No sums of games are needed.
* **Every move changes `phi` by a fixed amount.** A Left move lowers `phi` by 1. A slide of the
  frog raises it by 1, and a jump of the frog raises it by 3: the frog has spent one move on two
  squares, and the toad it jumped will not jump. Jumping is bad for the player who jumps.

### Lower bounds (`Cgt/OneFrog/Lower.lean`)

* **`V ≥ phi` for every one-frog position with `phi ≥ 0`** (`lower0`). If Left has no move, the
  position is `Tⁱ F Tᵏ` against the right end with some empty squares on the far left, and
  `phi ≤ 0`. So Left has a move whenever `phi > 0`, and any move keeps the bound.
* **`V ≥ phi + k` for `k = 1, 2`** (`lowerK`) on the set `room ≤ −k`, or `room = 1 − k` with an
  even gap. Left slides the nearest toad when there is a gap; otherwise he makes any other slide,
  or jumps when the toads are packed. After a slide of the frog he restores the set in the same
  way. After a jump of the frog `phi` is up by 3 and `lower0` is enough.
* `phi + ½` and `(phi + 1)∗` (`lower_half`, `lower_star`) follow in one step from these.

### Upper bounds (`Cgt/OneFrog/Upper.lean`)

One induction proves all of these together (`upper`, the structure `UC`):

| Set | Bound |
| --- | --- |
| no toad left of the frog | `max(phi, 0)` |
| `room ≥ 2`, or `room = 1` and an even gap | `phi` |
| `room = 1`, odd gap | `phi + ½` |
| `room = 0`, even gap | `max(phi + 1, 0)` |
| `room = 0`, odd gap, `phi ≥ 0` | `(phi + 1)∗` |
| `room = −1`, no gap, `phi ≥ −1` | `phi + 2` |
| `room = −1`, no gap, `phi = −2`, and (an empty square right of the frog, or one toad) | `0` |
| one toad, `room = 0`, odd gap, `phi = −1` | `∗` |

Right answers a Left move with a slide of the frog, or not at all; he never jumps. A slide of the
nearest toad lowers `room` by 1 and a slide of the frog raises it by 1. A jump by the nearest toad
followed by a slide of the frog raises `room` by the distance to the next toad. Other Left moves
leave `room` and the gap alone and simply cost Left a move.

The last two rows are the degenerate cases where `phi` is negative. They need a few inequalities
(`phi ≥ room − 1` when there is an empty square right of the frog, and variants), proved at the
start of `Upper.lean`.

### The exception (`Cgt/OneFrog/Exception.lean`)

`Tᵃ□F` has `room = 0`, gap 1 and `phi = −1` with `a ≥ 2` toads, outside the table. Left's only
move is to `Tᵃ⁻¹□TF = {Tᵃ⁻²□TTF | Tᵃ⁻¹FT□} = {a − 2 | 1}`: in `Tᵃ⁻²□TTF` the frog can never move
(`dead_frog`), and `Tᵃ⁻¹FT□ = 1` and Right's option `TᵃF□ = 0` are instances of the general
theorem.

## 4. How it was found

`tools/onefrog/bounds.py` computes, for every one-frog position, the least integer `≥` the value
and the greatest integer `≤` it by the recursions above (checked against canonical forms on the
20,480 positions of at most 11 squares). Against `phi`, the upper bound depends only on `room`
when `room ≥ 2`, and the lower bound `phi` never fails. `tools/onefrog/check_rules.py` then checks
each step of the induction, exactly as the proof uses it, on every position of at most 15 squares
(1.09 million claims). Its first run failed only at positions with `phi = −1`, which is how the two
degenerate families were found.

## 5. Files

| File | Contents |
| --- | --- |
| `Cgt/Statement.lean` | `Game.int`, `half`, `starN`, `oneFrog`, `valueT1`, `ConjectureT1` |
| `Cgt/OneFrog/Num.lean` | one-step rules for comparing with `n`, `n + ½`, `n∗`; order between them |
| `Cgt/OneFrog/Pos.lean` | one-frog positions as two lists around the frog; their moves; `phi`, `gap`, `behind` and the effect of each move |
| `Cgt/OneFrog/Rules.lean` | the rules for positions; the three kinds of Left move |
| `Cgt/OneFrog/Lower.lean` | lower bounds |
| `Cgt/OneFrog/Upper.lean` | upper bounds |
| `Cgt/OneFrog/T1.lean` | the general theorem and the cases of T1 |
| `Cgt/OneFrog/Exception.lean` | `Tᵃ□F` |
| `Cgt/OneFrog/Main.lean` | `conjectureT1` |
| `tools/onefrog/` | `bounds.py`, `check_rules.py` |

[T11]: Thotsaporn Thanatipanonda, *Further Hopping with Toads and Frogs*, Electronic Journal of
Combinatorics 18(1), 2011, #P67; preprint arXiv:0804.0640.

[E96]: Jeff Erickson, *New Toads and Frogs Results*, Games of No Chance, MSRI Publications 29,
1996, pp. 299–310.
