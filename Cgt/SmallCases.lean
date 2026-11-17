import Cgt.Decide

/-! Kernel-checked small cases. -/
namespace Cgt

theorem inf_1_1 : Game.Infinitesimal (tf (start 1 1)) :=
  infinitesimal_start_of_decide (by decide)

theorem inf_2_2 : Game.Infinitesimal (tf (start 2 2)) :=
  infinitesimal_start_of_decide (by decide)

/-- The exceptional case: `TTT□□FFF = ±1/8` is not infinitesimal. -/
theorem not_inf_3_2 : ¬ Game.Infinitesimal (tf (start 3 2)) :=
  not_infinitesimal_start_of_decide (by decide)

end Cgt
