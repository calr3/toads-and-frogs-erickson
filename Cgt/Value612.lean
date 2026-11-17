import Cgt.Tab.V612Checks

/-!
# `T⁶ □¹² F⁶` is neither `0` nor `∗`

Thanatipanonda conjectured that `Tᵃ □ᵇ Fᵃ` is `0` or `∗` whenever `b ≥ a > 0` ([T11],
Conjecture T4; Conjecture 4 in its arXiv preprint). The case `(6, 12)` is a counterexample
(`not_thanatipanonda_conjecture4`).

**Proof.** Right has a single move from `T⁶ □¹² F⁶`, to `r612`. We show `r612 ≤ 0` and
`r612 ≤ ∗` with a strategy table for Right (`Cgt/Table.lean`, data in `Cgt/Tab/V612Data.lean`,
extracted from the exact solver by `tools/strategy.cpp`). Then `0 ≤ T⁶ □¹² F⁶` fails (Right,
moving first, wins), so the start is not `0`; and `∗ ≤ T⁶ □¹² F⁶` fails, so it is not `∗`.

**Trust.** The check of the table is evaluated by `native_decide`, which trusts the Lean compiler
as well as the kernel. This file is part of `lake build CgtNative`, not of the default build.
-/

namespace Cgt
open Cell TF Game Table

/-- Right's only move from `T⁶ □¹² F⁶`: the leading frog slides one square. -/
def r612 : List Cell := List.replicate 6 T ++ List.replicate 11 E ++ [F, E] ++ List.replicate 5 F

theorem r612_mem : r612 ∈ rightMoves (start 6 12) := by decide +kernel

theorem r612_le_zero : le (tf r612) zero := soundN hNV612 (by native_decide)

theorem r612_le_star : le (tf r612) star := soundS hNV612 hSV612 (by native_decide)

/-- **`T⁶ □¹² F⁶` is not `0`.** -/
theorem start_6_12_not_zero : ¬ Equiv (tf (start 6 12)) zero := fun h =>
  not_zero_le_of_right r612_mem r612_le_zero h.2

/-- **`T⁶ □¹² F⁶` is not `∗`.** -/
theorem start_6_12_not_star : ¬ Equiv (tf (start 6 12)) star := fun h =>
  not_star_le_of_right ⟨r612, r612_mem, r612_le_star⟩ h.2

/-- Thanatipanonda's Conjecture 4 [T11]: `Tᵃ □ᵇ Fᵃ` is `0` or `∗` whenever `b ≥ a > 0`. -/
def ThanatipanondaConjecture4 : Prop :=
  ∀ a b : Nat, 0 < a → a ≤ b → Equiv (tf (start a b)) zero ∨ Equiv (tf (start a b)) star

/-- **Thanatipanonda's Conjecture 4 is false**: `(6, 12)` is a counterexample. -/
theorem not_thanatipanonda_conjecture4 : ¬ ThanatipanondaConjecture4 := fun h =>
  (h 6 12 (by decide) (by decide)).elim start_6_12_not_zero start_6_12_not_star

end Cgt
