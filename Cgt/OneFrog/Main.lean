import Cgt.OneFrog.Exception

/-!
# Thanatipanonda's Conjecture T1

`conjectureT1 : ConjectureT1` (stated in `Cgt/Statement.lean`): the value of `□ˡ Tᵃ □ᵇ F □ʳ` for
every `a ≥ 1` and `l ≤ r`, assembled from the cases in `Cgt/OneFrog/T1.lean` and
`Cgt/OneFrog/Exception.lean`.
-/

namespace Cgt

open Cell TF Game OneFrog

/-- `Tᵃ⁺¹ F □⁰`, with no empty square at all: the value is `0`. -/
theorem OneFrog.value_block_zero (a : Nat) : Equiv (V (List.replicate (a + 1) true) []) (int 0) := by
  constructor
  · have h := (upper_all (List.replicate (a + 1) true) []).u4
      (by rw [cT_replicate_true]; omega)
      (by unfold room; rw [behind_replicate_true]; simp [cE])
      (by rw [gap_replicate_true])
    rwa [show (phi (List.replicate (a + 1) true) [] + 1).toNat = 0 by
      unfold phi; rw [invL_replicate_true, cT_replicate_true, cE_replicate_true]; simp [invB, cE]
      omega] at h
  · apply int_le_V (Or.inl rfl)
    · intro L₂ h; rw [List.replicate_succ] at h; simp at h
    · intro L₂ h
      cases a with
      | zero => simp at h
      | succ a => rw [List.replicate_succ, List.replicate_succ] at h; simp at h

/-- **Thanatipanonda's Conjecture T1.** -/
theorem conjectureT1 : ConjectureT1 := by
  intro l a b r ha hlr
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  unfold valueT1
  simp only [Nat.add_sub_cancel]
  split
  · exact t1_far l a b r (by assumption)
  · split
    · rename_i h1 h2
      subst h2
      split
      · exact t1_near_even a b l (by assumption)
      · exact t1_near_odd a b l (by omega)
    · have hl : l = r := by omega
      subst hl
      split
      · rename_i hb
        rcases Nat.eq_zero_or_pos (b + l) with h0 | h0
        · have hb0 : b = 0 := by omega
          have hl0 : l = 0 := by omega
          subst hb0; subst hl0
          rw [oneFrog_eq]
          have h : side 0 (a + 1) 0 = List.replicate (a + 1) true := by simp [side]
          rw [h]
          rw [show a * (0 + 0 - 1) = 0 by simp]
          exact value_block_zero a
        · exact t1_equal_even a b l hb h0
      · split
        · rename_i hex
          obtain ⟨hr, hb1, ha2⟩ := hex
          subst hr; subst hb1
          obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          simpa using t1_exception a
        · rename_i hb hex
          refine t1_equal_odd a b l (by omega) ?_
          by_cases h2 : 2 ≤ b + l
          · exact Or.inr h2
          · left
            have : l = 0 ∧ b = 1 := by omega
            apply Classical.byContradiction
            intro ha0
            exact hex ⟨this.1, this.2, by omega⟩

end Cgt
