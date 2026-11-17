import Cgt.Col.B4SChecks
import Cgt.Col.B4
import Cgt.Col.Wit
import Cgt.Col.RuleF2

/-!
# The exact values of the column `b = 4`

**Theorem.** `Tᵃ □⁴ Fᵃ = ∗` for every `a ≥ 5` (`start_four_equiv_star`); with the small cases,
`Tᵃ □⁴ Fᵃ = 0` for `a = 0, 1, 4` and `∗` otherwise (`start_four_value`). This is the case `b = 4`
of Thanatipanonda's conjecture that `Tᵃ □ᵇ Fᵃ = ∗` whenever `a > b > 0`, `b ≠ 2` [T11].

The proof is that of `Cgt/Col/Value3.lean` with the gap rule `ruleF2` (exact up to 2, "far" above,
no parity) and the 692 + 361,289 keys of `Cgt/Col/B4SData.lean`.

**Trust.** As for `infinitesimal_start_b_four`, the finite check (3.5 million witnesses) and the
start key are evaluated by `native_decide`, which trusts the Lean compiler as well as the kernel.
This file is part of `lake build CgtNative`, not of the default build.
-/

namespace Cgt
namespace Col
open Cell TF Game

/-- The margin relation of the rule `ruleF2` has the three properties the soundness proof needs. -/
theorem marginF2 : Margin ruleF2 := ⟨wit_complete ruleF2, margin_left ruleF2, margin_right ruleF2⟩

/-- From `a = 5` on, the start keys under `ruleF2` are all equal. -/
theorem rel_s4F2 {a : Nat} (ha : 5 ≤ a) : Rel ruleF2 0 (s4 a) (s4 (a + 1)) := by
  refine ⟨⟨rfl, fun i => ⟨cellAt_s4 a i, ?_, ?_⟩⟩, fun i _ => ?_, fun i k hi hk => ?_⟩
  · rw [lenAt_s4, lenAt_s4]; split <;> (try split) <;> omega
  · intro h; rw [lenAt_s4, lenAt_s4]
    match i with
    | 0 => simp [cellAt, runAt, s4] at h
    | 1 => rfl
    | 2 => simp [cellAt, runAt, s4] at h
    | i + 3 => simp
  · rw [lenAt_s4, lenAt_s4]; unfold close; simp only [ruleF2, true_or, and_true]
    split <;> (try split) <;> omega
  · rcases isEnt_s4 hi with rfl | rfl <;> rcases isEnt_s4 hk with rfl | rfl <;>
      exact Or.inl (by simp [lenAt_s4])

theorem key_s4S : ∀ a, 5 ≤ a → colB4SS.mem (keyOf ruleF2 (s4 a)) = true
  | 5, _ => by native_decide
  | a + 6, _ => by
    rw [← keyOf_eq_of_rel (rel_s4F2 (a := a + 5) (by omega))]
    exact key_s4S (a + 5) (by omega)

theorem start_four_le_star (a : Nat) (ha : 5 ≤ a) : le (tf (start a 4)) star := by
  rw [← expand_s4]
  exact soundS marginF2 colB4SS colB4SN hcS4S hcN4S _ (s4 a) (maxB_s4 (by omega)) (Nat.lt_succ_self _)
    (key_s4S a ha)

end Col

open Cell TF Game

/-- **`Tᵃ □⁴ Fᵃ = ∗` for every `a ≥ 5`** (finite check by `native_decide`). -/
theorem start_four_equiv_star (a : Nat) (ha : 5 ≤ a) : Equiv (tf (start a 4)) star :=
  equiv_star_of_mirror (mirror_start a 4) (Col.start_four_le_star a ha)

/-- The value of `Tᵃ □⁴ Fᵃ`: `0` for `a = 0, 1, 4`, otherwise `∗`. -/
def valueB4 (a : Nat) : Game := if a = 0 ∨ a = 1 ∨ a = 4 then zero else star

/-- **The exact values of the column `b = 4`** (finite check by `native_decide`). -/
theorem start_four_value (a : Nat) : Equiv (tf (start a 4)) (valueB4 a) := by
  match a with
  | 0 => exact equiv_zero_of_mirror (mirror_start 0 4) (le_zero_of_leZeroB (by decide +kernel))
  | 1 => exact equiv_zero_of_mirror (mirror_start 1 4) (le_zero_of_leZeroB (by decide +kernel))
  | 2 =>
    have h := start_two_value 4 (Or.inr (by omega))
    simpa [valueA2, valueB4] using h
  | 3 =>
    -- Left's only move and one Right move both reach positions equal to `0`.
    refine equiv_star_of_mirror (mirror_start 3 4) (le_star_of (fun q hq => ?_) ?_)
    · have h : leftMoves (start 3 4) = [[T, T, E, T, E, E, E, F, F, F]] := by decide +kernel
      rw [h, List.mem_singleton] at hq
      subst hq
      exact not_star_le_of_le_zero (le_zero_of_leZeroB (by decide +kernel))
    · exact ⟨[T, T, T, E, E, E, F, E, F, F], by decide +kernel, le_zero_of_leZeroB (by decide +kernel)⟩
  | 4 => exact equiv_zero_of_mirror (mirror_start 4 4) (le_zero_of_leZeroB (by decide +kernel))
  | a + 5 =>
    have hv : valueB4 (a + 5) = star := by unfold valueB4; rw [if_neg (by omega)]
    rw [hv]; exact start_four_equiv_star (a + 5) (by omega)

end Cgt
