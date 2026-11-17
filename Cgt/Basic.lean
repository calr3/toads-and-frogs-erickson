import Cgt.FamilyA1

/-!
# Trivial families: `a = 0` and `b = 0`
-/

namespace Cgt
open Cell TF Game

theorem leftMoves_eq_nil_of_no_E {p : List Cell} (h : E ∉ p) : leftMoves p = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro q hq
  rcases mem_leftMoves.1 hq with ⟨u, r, rfl, -⟩ | ⟨u, r, rfl, -⟩ <;> simp at h

theorem upperZero_of_no_E {p : List Cell} (h : E ∉ p) : UpperZero (tf p) := by
  rw [upperZero_tf_iff, lfZero_tf_iff, le_zero_iff_tf, leftMoves_eq_nil_of_no_E h]
  simp

/-- **The case `b = 0`**: `Tᵃ Fᵃ` has no moves at all, so it is `0`. -/
theorem infinitesimal_start_b_zero (a : Nat) : Infinitesimal (tf (start a 0)) := by
  rw [infinitesimal_start_iff]
  apply upperZero_of_no_E
  simp [start, List.mem_replicate]

/-- **The case `a = 0`**: the empty strip. -/
theorem infinitesimal_start_a_zero (b : Nat) : Infinitesimal (tf (start 0 b)) := by
  rw [infinitesimal_start_iff, upperZero_tf_iff, lfZero_tf_iff, le_zero_iff_tf]
  simp [start, leftMoves_replicate_E]

end Cgt
