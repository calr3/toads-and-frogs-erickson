import Cgt.Col.B4
import Cgt.Col.Wit

/-!
# The column `b = 4`

**Theorem.** `Tᵃ □⁴ Fᵃ` is infinitesimal for every `a` (`infinitesimal_start_b_four`).

The proof is that of the column `b = 3` (`Cgt/Col/Column3.lean`) with the gap rule `ruleF` and the
233,087 keys of `Cgt/Col/B4Data.lean`.

**Trust.** The finite check of those keys (2.8 million witnesses) is too large for the kernel; it
is evaluated by `native_decide`. So this theorem trusts the Lean compiler and runtime as well as
the kernel: `#print axioms` lists, besides `propext`, `Classical.choice` and `Quot.sound`, one
axiom per `native_decide` use (13 in all), each asserting the result of a compiled evaluation.
It is therefore kept out of the default build and of `Cgt.Conjecture5`: build it with
`lake build CgtNative`.
-/

namespace Cgt

namespace Col

/-- The margin relation of the rule `ruleF` has the three properties the soundness proof needs. -/
theorem marginF : Margin ruleF := ⟨wit_complete ruleF, margin_left ruleF, margin_right ruleF⟩

end Col

open Game

/-- **The column `b = 4`** (finite check by `native_decide`). `Tᵃ □⁴ Fᵃ` is infinitesimal for
every `a`. -/
theorem infinitesimal_start_b_four (a : Nat) : Infinitesimal (tf (start a 4)) :=
  Col.infinitesimal_start_four_of Col.marginF a

end Cgt
