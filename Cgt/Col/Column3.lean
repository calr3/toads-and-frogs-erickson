import Cgt.Col.B3
import Cgt.Col.Wit

/-!
# The column `b = 3`

**Theorem.** `Tᵃ □³ Fᵃ` is infinitesimal for every `a` (`infinitesimal_start_b_three`).

The proof combines:

* the kernel-checked finite check of the 3,031 keys of `Cgt/Col/B3Data.lean`
  (`Cgt/Col/B3.lean`);
* the soundness theorem `sound` (`Cgt/Col/Sound.lean`);
* the three properties of the margin relation it needs: witness completeness (`wit_complete`,
  `Cgt/Col/Wit.lean`) and the margin lemmas for Left and Right moves (`margin_left`,
  `Cgt/Col/Margin.lean`; `margin_right`, `Cgt/Col/Mirror.lean`).
-/

namespace Cgt

namespace Col

/-- The margin relation has the three properties the soundness proof needs. -/
theorem margin : Margin := ⟨wit_complete, margin_left, margin_right⟩

end Col

open Game

/-- **The column `b = 3`.** `Tᵃ □³ Fᵃ` is infinitesimal for every `a`. -/
theorem infinitesimal_start_b_three (a : Nat) : Infinitesimal (tf (start a 3)) :=
  Col.infinitesimal_start_three_of Col.margin a

end Cgt
