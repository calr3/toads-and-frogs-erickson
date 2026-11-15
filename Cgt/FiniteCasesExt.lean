import Cgt.FiniteCases

/-!
# More kernel-checked cases (`a = 2`, `b ≤ 16`)

Checked by the Lean kernel through the verified decision procedure `startInfinitesimalB`.
Larger cases are feasible in principle but need more than 8 GB of memory in the kernel.
-/

namespace Cgt

theorem infinitesimal_start_2_9 : Game.Infinitesimal (tf (start 2 9)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_10 : Game.Infinitesimal (tf (start 2 10)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_11 : Game.Infinitesimal (tf (start 2 11)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_12 : Game.Infinitesimal (tf (start 2 12)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_13 : Game.Infinitesimal (tf (start 2 13)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_14 : Game.Infinitesimal (tf (start 2 14)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_15 : Game.Infinitesimal (tf (start 2 15)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_16 : Game.Infinitesimal (tf (start 2 16)) :=
  infinitesimal_start_of_decide (by decide +kernel)

end Cgt
