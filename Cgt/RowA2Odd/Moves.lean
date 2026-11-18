import Cgt.RowA2Odd.Inv

/-!
# Single moves of four-piece positions, with explicit results

Each lemma computes one move of `P4` (a slide or a jump) under the conditions that make it legal.
They are used by the generated closure lemmas in `Cgt/RowA2Odd/Close*.lean`.
-/

namespace Cgt

section
variable {c1 c2 c3 c4 : Bool} {a b x d e : Nat}

theorem lm1_slide (h : b ≠ 0) :
    (⟨true, c2, c3, c4, a, b, x, d, e⟩ : P4).lm1 = some ⟨true, c2, c3, c4, a + 1, b - 1, x, d, e⟩ := by
  simp [P4.lm1, h]

theorem lm1_jump (hb : b = 0) (hx : x ≠ 0) :
    (⟨true, false, c3, c4, a, b, x, d, e⟩ : P4).lm1 = some ⟨false, true, c3, c4, a + 1, b, x - 1, d, e⟩ := by
  simp [P4.lm1, hb, hx]

theorem lm2_slide (h : x ≠ 0) :
    (⟨c1, true, c3, c4, a, b, x, d, e⟩ : P4).lm2 = some ⟨c1, true, c3, c4, a, b + 1, x - 1, d, e⟩ := by
  simp [P4.lm2, h]

theorem lm2_jump (hx : x = 0) (hd : d ≠ 0) :
    (⟨c1, true, false, c4, a, b, x, d, e⟩ : P4).lm2 = some ⟨c1, false, true, c4, a, b + 1, x, d - 1, e⟩ := by
  simp [P4.lm2, hx, hd]

theorem lm3_slide (h : d ≠ 0) :
    (⟨c1, c2, true, c4, a, b, x, d, e⟩ : P4).lm3 = some ⟨c1, c2, true, c4, a, b, x + 1, d - 1, e⟩ := by
  simp [P4.lm3, h]

theorem lm3_jump (hd : d = 0) (he : e ≠ 0) :
    (⟨c1, c2, true, false, a, b, x, d, e⟩ : P4).lm3 = some ⟨c1, c2, false, true, a, b, x + 1, d, e - 1⟩ := by
  simp [P4.lm3, hd, he]

theorem lm4_slide (h : e ≠ 0) :
    (⟨c1, c2, c3, true, a, b, x, d, e⟩ : P4).lm4 = some ⟨c1, c2, c3, true, a, b, x, d + 1, e - 1⟩ := by
  simp [P4.lm4, h]

theorem rm1_slide (h : a ≠ 0) :
    (⟨false, c2, c3, c4, a, b, x, d, e⟩ : P4).rm1 = some ⟨false, c2, c3, c4, a - 1, b + 1, x, d, e⟩ := by
  simp [P4.rm1, h]

theorem rm2_slide (h : b ≠ 0) :
    (⟨c1, false, c3, c4, a, b, x, d, e⟩ : P4).rm2 = some ⟨c1, false, c3, c4, a, b - 1, x + 1, d, e⟩ := by
  simp [P4.rm2, h]

theorem rm2_jump (hb : b = 0) (ha : a ≠ 0) :
    (⟨true, false, c3, c4, a, b, x, d, e⟩ : P4).rm2 = some ⟨false, true, c3, c4, a - 1, b, x + 1, d, e⟩ := by
  simp [P4.rm2, hb, ha]

theorem rm3_slide (h : x ≠ 0) :
    (⟨c1, c2, false, c4, a, b, x, d, e⟩ : P4).rm3 = some ⟨c1, c2, false, c4, a, b, x - 1, d + 1, e⟩ := by
  simp [P4.rm3, h]

theorem rm3_jump (hx : x = 0) (hb : b ≠ 0) :
    (⟨c1, true, false, c4, a, b, x, d, e⟩ : P4).rm3 = some ⟨c1, false, true, c4, a, b - 1, x, d + 1, e⟩ := by
  simp [P4.rm3, hx, hb]

theorem rm4_slide (h : d ≠ 0) :
    (⟨c1, c2, c3, false, a, b, x, d, e⟩ : P4).rm4 = some ⟨c1, c2, c3, false, a, b, x, d - 1, e + 1⟩ := by
  simp [P4.rm4, h]

theorem rm4_jump (hd : d = 0) (hx : x ≠ 0) :
    (⟨c1, c2, true, false, a, b, x, d, e⟩ : P4).rm4 = some ⟨c1, c2, false, true, a, b, x - 1, d, e + 1⟩ := by
  simp [P4.rm4, hd, hx]

end

end Cgt
