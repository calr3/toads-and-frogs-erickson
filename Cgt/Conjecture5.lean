import Cgt.Basic
import Cgt.FiniteCases
import Cgt.SmallCases

/-!
# Erickson's Conjecture 5 for Toads and Frogs

**Conjecture (Erickson, 1996).** `Tᵃ □ᵇ Fᵃ` is infinitesimal for all `a, b`, except
`(a, b) = (3, 2)`.

This file states the conjecture (`Conjecture5`) and collects what is proved so far:

* the exceptional case `(3, 2)` is indeed *not* infinitesimal (`not_infinitesimal_3_2`);
* `a = 0`, `a = 1` and `b = 0` hold for every value of the other parameter;
* every case with `2a + b ≤ 12` (other than `(3, 2)`) is checked by the kernel.

The general case is open.
-/

namespace Cgt
open Game

/-- Erickson's Conjecture 5: `Tᵃ □ᵇ Fᵃ` is infinitesimal unless `(a, b) = (3, 2)`. -/
def Conjecture5 : Prop :=
  ∀ a b : Nat, (a, b) ≠ (3, 2) → Infinitesimal (tf (start a b))

/-- The exception really is an exception: `TTT□□FFF = ±1/8`. -/
theorem not_infinitesimal_3_2 : ¬ Infinitesimal (tf (start 3 2)) := not_inf_3_2

/-- All cases of the conjecture established so far. -/
theorem conjecture5_partial (a b : Nat) (hab : (a, b) ≠ (3, 2))
    (h : a ≤ 1 ∨ b = 0 ∨ 2 * a + b ≤ 12) : Infinitesimal (tf (start a b)) := by
  rcases h with h | h | h
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl
    · exact infinitesimal_start_a_zero b
    · exact infinitesimal_start_one b
  · subst h; exact infinitesimal_start_b_zero a
  · by_cases ha : a ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl
      · exact infinitesimal_start_a_zero b
      · exact infinitesimal_start_one b
    by_cases hb : b = 0
    · subst hb; exact infinitesimal_start_b_zero a
    have ha6 : a ≤ 5 := by omega
    have hb10 : b ≤ 8 := by omega
    have ha' : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
    rcases ha' with rfl | rfl | rfl | rfl
    · have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 := by omega
      rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact infinitesimal_start_2_1
      · exact infinitesimal_start_2_2
      · exact infinitesimal_start_2_3
      · exact infinitesimal_start_2_4
      · exact infinitesimal_start_2_5
      · exact infinitesimal_start_2_6
      · exact infinitesimal_start_2_7
      · exact infinitesimal_start_2_8
    · have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by omega
      rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact infinitesimal_start_3_1
      · exact absurd rfl hab
      · exact infinitesimal_start_3_3
      · exact infinitesimal_start_3_4
      · exact infinitesimal_start_3_5
      · exact infinitesimal_start_3_6
    · have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
      rcases hb' with rfl | rfl | rfl | rfl
      · exact infinitesimal_start_4_1
      · exact infinitesimal_start_4_2
      · exact infinitesimal_start_4_3
      · exact infinitesimal_start_4_4
    · have hb' : b = 1 ∨ b = 2 := by omega
      rcases hb' with rfl | rfl
      · exact infinitesimal_start_5_1
      · exact infinitesimal_start_5_2

end Cgt
