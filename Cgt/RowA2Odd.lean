import Cgt.RowA2Values
import Cgt.RowA2Odd.CloseTTFF
import Cgt.RowA2Odd.CloseTFTF
import Cgt.RowA2Odd.CloseFTTF
import Cgt.RowA2Odd.CloseTFFT
import Cgt.RowA2Odd.CloseFTFT
import Cgt.RowA2Odd.CloseFFTT

/-!
# Exact values in the row `a = 2` for every `b` (Thanatipanonda's Conjecture T2)

`TT□ᵇFF = ∗` if `2 ≤ b ≤ 4` or `b ≡ 1 (mod 6)`, and `TT□ᵇFF = 0` otherwise (`exactValuesA2`).

`Cgt/RowA2Values.lean` reduces the odd `b ≥ 31` to two normal-play claims, `T□T□ᵏF□F ≤ 0` for
`k ≡ 1, 3 (mod 6)` and `TT□ᵏF□F ≤ 0` for `k ≡ 0 (mod 6)`. Both follow from one invariant:

* `inv2` (`Cgt/RowA2Odd/Inv.lean`) is a finite union of cases, each a conjunction of linear
  inequalities, equalities and congruences in the five gaps of a four-piece position, separately for
  each order of the pieces. It was found from exact play (`tools/presburger`).
* `inv2_closed`: from every position in `inv2`, every Left move has a Right reply back into
  `inv2`. The generated lemmas `close_TTFF`, …, `close_FFTT` prove this case by case with `omega`,
  for every board size.
* So every position in `inv2` is `≤ 0` (`le_zero_of_closed`), and the two families of starting
  positions lie in `inv2`.

Right's strategy, in words: while the toads and frogs approach each other, always move the front
frog. This keeps the race count (empty squares in front of the toads minus those in front of the
frogs) constant and the rear frog at the edge of the board. After the first contact, Right moves into
the exact set of losing positions for Left, which for each order of the pieces is described by the
cases of `inv2`.
-/

namespace Cgt
open Cell TF Game

/-- If `I` is closed under a Left move followed by a Right reply, every position in `I` is `≤ 0`. -/
theorem le_zero_of_closed (I : P4 → Prop)
    (hI : ∀ p, I p → ∀ q, q ∈ p.lms → ∃ r, r ∈ q.rms ∧ I r) :
    ∀ (n : Nat) (p : P4), pot p.toList < n → I p → le (tf p.toList) zero := by
  intro n
  induction n with
  | zero => intro p h; omega
  | succ n ih =>
    intro p hn hp
    rw [le_zero_iff_tf, leftMoves_toList p]
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    obtain ⟨r, hr, hgood⟩ := hI p hp q' hq'
    have hmem := toList_mem_rightMoves hr
    refine ⟨r.toList, hmem, ih r ?_ hgood⟩
    have h1 := pot_lt_of_mem_leftMoves (leftMoves_toList p ▸ hq)
    have h2 := pot_lt_of_mem_rightMoves hmem
    omega

/-- `inv2` is closed under a Left move followed by a Right reply. -/
theorem inv2_closed (p : P4) (hp : inv2 p) (q : P4) (hq : q ∈ p.lms) : ∃ r, r ∈ q.rms ∧ inv2 r := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp only [inv2] at hp
  · exact close_FFTT g0 g1 g2 g3 g4 hp q hq
  · exact close_FTFT g0 g1 g2 g3 g4 hp q hq
  · exact close_FTTF g0 g1 g2 g3 g4 hp q hq
  · exact close_TFFT g0 g1 g2 g3 g4 hp q hq
  · exact close_TFTF g0 g1 g2 g3 g4 hp q hq
  · exact close_TTFF g0 g1 g2 g3 g4 hp q hq

/-- Every position in `inv2` is `≤ 0`: Right, moving second, wins it. -/
theorem le_zero_of_inv2 (p : P4) (hp : inv2 p) : le (tf p.toList) zero :=
  le_zero_of_closed inv2 inv2_closed _ p (Nat.lt_succ_self _) hp

/-- `T□T□ᵏF□F ≤ 0` for `k ≥ 7` with `k ≡ 1, 3 (mod 6)`. -/
theorem p0_le_zero_odd (k : Nat) (hk : 7 ≤ k) (hm : k % 6 = 1 ∨ k % 6 = 3) :
    le (tf (p0 k).toList) zero := by
  refine le_zero_of_inv2 _ ?_
  simp only [p0, inv2, goodTTFF]
  rcases hm with hm | hm
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

/-- `TT□ᵐF□F ≤ 0` for `m ≥ 6` with `m ≡ 0 (mod 6)`. -/
theorem r2_le_zero (m : Nat) (hm : 6 ≤ m) (h6 : m % 6 = 0) : le (tf (r2 m).toList) zero := by
  refine le_zero_of_inv2 _ ?_
  simp only [r2, inv2, goodTTFF]
  exact Or.inr (Or.inr (Or.inl (by omega)))

/-- `TT□ᵇFF` for odd `b ≥ 9`. -/
theorem start_two_value_of_odd (b : Nat) (hb : 9 ≤ b) (ho : b % 2 = 1) :
    Equiv (tf (start 2 b)) (valueA2 b) := by
  by_cases h1 : b % 6 = 1
  · have hv : valueA2 b = star := by unfold valueA2; simp [h1]
    rw [hv]
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
    exact start_two_equiv_star_of m (by omega) (r2_le_zero m (by omega) (by omega))
  · have hv : valueA2 b = zero := by
      unfold valueA2
      split
      · next h => exact absurd h (by omega)
      · rfl
    rw [hv]
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
    exact start_two_equiv_zero_of k (p0_le_zero_odd k (by omega) (by omega))

/-- **Thanatipanonda's Conjecture T2**: `TT□ᵇFF = ∗` if `2 ≤ b ≤ 4` or `b ≡ 1 (mod 6)`, and
`TT□ᵇFF = 0` otherwise. -/
theorem exactValuesA2 : ExactValuesA2 := by
  intro b
  by_cases h : b % 2 = 0 ∨ b ≤ 30
  · exact start_two_value b h
  · exact start_two_value_of_odd b (by omega) (by omega)

end Cgt
