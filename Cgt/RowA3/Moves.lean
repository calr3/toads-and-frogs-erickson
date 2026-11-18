import Cgt.Six

/-!
# Single moves of six-piece positions, with explicit results

Each lemma computes one move of `P6` (a slide or a jump) under the conditions that make it legal, as
`Cgt/RowA2Odd/Moves.lean` does for `P4`. `mem_lms6` and `mem_rms6` list the moves of a position, and
`le_zero_of_closed6` is the induction that turns a set of positions closed under "a Left move followed
by a Right reply" into positions `≤ 0`.
-/

namespace Cgt
open Cell TF Game

theorem mem_lms6 {p q : P6} : q ∈ p.lms ↔
    p.lm1 = some q ∨ p.lm2 = some q ∨ p.lm3 = some q ∨ p.lm4 = some q ∨ p.lm5 = some q ∨ p.lm6 = some q := by
  simp [P6.lms, List.mem_append, Option.mem_toList, or_assoc]

theorem mem_rms6 {p q : P6} : q ∈ p.rms ↔
    p.rm1 = some q ∨ p.rm2 = some q ∨ p.rm3 = some q ∨ p.rm4 = some q ∨ p.rm5 = some q ∨ p.rm6 = some q := by
  simp [P6.rms, List.mem_append, Option.mem_toList, or_assoc]

section
variable {c1 c2 c3 c4 c5 c6 : Bool} {g0 g1 g2 g3 g4 g5 g6 : Nat}

theorem lm1_slide6 (h : g1 ≠ 0) :
    (⟨true, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm1 = some (⟨true, c2, c3, c4, c5, c6, g0 + 1, g1 - 1, g2, g3, g4, g5, g6⟩ : P6) := by
  simp [P6.lm1, h]

theorem lm1_jump6 (h : g1 = 0) (h' : g2 ≠ 0) :
    (⟨true, false, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm1 = some (⟨false, true, c3, c4, c5, c6, g0 + 1, g1, g2 - 1, g3, g4, g5, g6⟩ : P6) := by
  simp [P6.lm1, h, h']

theorem lm2_slide6 (h : g2 ≠ 0) :
    (⟨c1, true, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm2 = some (⟨c1, true, c3, c4, c5, c6, g0, g1 + 1, g2 - 1, g3, g4, g5, g6⟩ : P6) := by
  simp [P6.lm2, h]

theorem lm2_jump6 (h : g2 = 0) (h' : g3 ≠ 0) :
    (⟨c1, true, false, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm2 = some (⟨c1, false, true, c4, c5, c6, g0, g1 + 1, g2, g3 - 1, g4, g5, g6⟩ : P6) := by
  simp [P6.lm2, h, h']

theorem lm3_slide6 (h : g3 ≠ 0) :
    (⟨c1, c2, true, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm3 = some (⟨c1, c2, true, c4, c5, c6, g0, g1, g2 + 1, g3 - 1, g4, g5, g6⟩ : P6) := by
  simp [P6.lm3, h]

theorem lm3_jump6 (h : g3 = 0) (h' : g4 ≠ 0) :
    (⟨c1, c2, true, false, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm3 = some (⟨c1, c2, false, true, c5, c6, g0, g1, g2 + 1, g3, g4 - 1, g5, g6⟩ : P6) := by
  simp [P6.lm3, h, h']

theorem lm4_slide6 (h : g4 ≠ 0) :
    (⟨c1, c2, c3, true, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm4 = some (⟨c1, c2, c3, true, c5, c6, g0, g1, g2, g3 + 1, g4 - 1, g5, g6⟩ : P6) := by
  simp [P6.lm4, h]

theorem lm4_jump6 (h : g4 = 0) (h' : g5 ≠ 0) :
    (⟨c1, c2, c3, true, false, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm4 = some (⟨c1, c2, c3, false, true, c6, g0, g1, g2, g3 + 1, g4, g5 - 1, g6⟩ : P6) := by
  simp [P6.lm4, h, h']

theorem lm5_slide6 (h : g5 ≠ 0) :
    (⟨c1, c2, c3, c4, true, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm5 = some (⟨c1, c2, c3, c4, true, c6, g0, g1, g2, g3, g4 + 1, g5 - 1, g6⟩ : P6) := by
  simp [P6.lm5, h]

theorem lm5_jump6 (h : g5 = 0) (h' : g6 ≠ 0) :
    (⟨c1, c2, c3, c4, true, false, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm5 = some (⟨c1, c2, c3, c4, false, true, g0, g1, g2, g3, g4 + 1, g5, g6 - 1⟩ : P6) := by
  simp [P6.lm5, h, h']

theorem lm6_slide6 (h : g6 ≠ 0) :
    (⟨c1, c2, c3, c4, c5, true, g0, g1, g2, g3, g4, g5, g6⟩ : P6).lm6 = some (⟨c1, c2, c3, c4, c5, true, g0, g1, g2, g3, g4, g5 + 1, g6 - 1⟩ : P6) := by
  simp [P6.lm6, h]

theorem rm1_slide6 (h : g0 ≠ 0) :
    (⟨false, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm1 = some (⟨false, c2, c3, c4, c5, c6, g0 - 1, g1 + 1, g2, g3, g4, g5, g6⟩ : P6) := by
  simp [P6.rm1, h]

theorem rm2_slide6 (h : g1 ≠ 0) :
    (⟨c1, false, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm2 = some (⟨c1, false, c3, c4, c5, c6, g0, g1 - 1, g2 + 1, g3, g4, g5, g6⟩ : P6) := by
  simp [P6.rm2, h]

theorem rm2_jump6 (h : g1 = 0) (h' : g0 ≠ 0) :
    (⟨true, false, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm2 = some (⟨false, true, c3, c4, c5, c6, g0 - 1, g1, g2 + 1, g3, g4, g5, g6⟩ : P6) := by
  simp [P6.rm2, h, h']

theorem rm3_slide6 (h : g2 ≠ 0) :
    (⟨c1, c2, false, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm3 = some (⟨c1, c2, false, c4, c5, c6, g0, g1, g2 - 1, g3 + 1, g4, g5, g6⟩ : P6) := by
  simp [P6.rm3, h]

theorem rm3_jump6 (h : g2 = 0) (h' : g1 ≠ 0) :
    (⟨c1, true, false, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm3 = some (⟨c1, false, true, c4, c5, c6, g0, g1 - 1, g2, g3 + 1, g4, g5, g6⟩ : P6) := by
  simp [P6.rm3, h, h']

theorem rm4_slide6 (h : g3 ≠ 0) :
    (⟨c1, c2, c3, false, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm4 = some (⟨c1, c2, c3, false, c5, c6, g0, g1, g2, g3 - 1, g4 + 1, g5, g6⟩ : P6) := by
  simp [P6.rm4, h]

theorem rm4_jump6 (h : g3 = 0) (h' : g2 ≠ 0) :
    (⟨c1, c2, true, false, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm4 = some (⟨c1, c2, false, true, c5, c6, g0, g1, g2 - 1, g3, g4 + 1, g5, g6⟩ : P6) := by
  simp [P6.rm4, h, h']

theorem rm5_slide6 (h : g4 ≠ 0) :
    (⟨c1, c2, c3, c4, false, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm5 = some (⟨c1, c2, c3, c4, false, c6, g0, g1, g2, g3, g4 - 1, g5 + 1, g6⟩ : P6) := by
  simp [P6.rm5, h]

theorem rm5_jump6 (h : g4 = 0) (h' : g3 ≠ 0) :
    (⟨c1, c2, c3, true, false, c6, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm5 = some (⟨c1, c2, c3, false, true, c6, g0, g1, g2, g3 - 1, g4, g5 + 1, g6⟩ : P6) := by
  simp [P6.rm5, h, h']

theorem rm6_slide6 (h : g5 ≠ 0) :
    (⟨c1, c2, c3, c4, c5, false, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm6 = some (⟨c1, c2, c3, c4, c5, false, g0, g1, g2, g3, g4, g5 - 1, g6 + 1⟩ : P6) := by
  simp [P6.rm6, h]

theorem rm6_jump6 (h : g5 = 0) (h' : g4 ≠ 0) :
    (⟨c1, c2, c3, c4, true, false, g0, g1, g2, g3, g4, g5, g6⟩ : P6).rm6 = some (⟨c1, c2, c3, c4, false, true, g0, g1, g2, g3, g4 - 1, g5, g6 + 1⟩ : P6) := by
  simp [P6.rm6, h, h']

end

/-- If `I` is closed under a Left move followed by a Right reply, every position in `I` is `≤ 0`. -/
theorem le_zero_of_closed6 (I : P6 → Prop)
    (hI : ∀ p, I p → ∀ q, q ∈ p.lms → ∃ r, r ∈ q.rms ∧ I r) :
    ∀ (n : Nat) (p : P6), pot p.toList < n → I p → le (tf p.toList) zero := by
  intro n
  induction n with
  | zero => intro p h; omega
  | succ n ih =>
    intro p hn hp
    rw [le_zero_iff_tf, leftMoves_toList6 p]
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    obtain ⟨r, hr, hgood⟩ := hI p hp q' hq'
    have hmem := toList_mem_rightMoves6 hr
    refine ⟨r.toList, hmem, ih r ?_ hgood⟩
    have h1 := pot_lt_of_mem_leftMoves (leftMoves_toList6 p ▸ hq)
    have h2 := pot_lt_of_mem_rightMoves hmem
    omega

end Cgt
