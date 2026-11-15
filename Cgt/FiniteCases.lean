import Cgt.Decide

/-!
# Kernel-checked finite cases

Each case is checked by evaluating the verified decision procedure `startInfinitesimalB`
in the Lean kernel (`decide +kernel`).
-/

namespace Cgt

theorem infinitesimal_start_2_1 : Game.Infinitesimal (tf (start 2 1)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_2 : Game.Infinitesimal (tf (start 2 2)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_3 : Game.Infinitesimal (tf (start 2 3)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_4 : Game.Infinitesimal (tf (start 2 4)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_5 : Game.Infinitesimal (tf (start 2 5)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_6 : Game.Infinitesimal (tf (start 2 6)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_7 : Game.Infinitesimal (tf (start 2 7)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_2_8 : Game.Infinitesimal (tf (start 2 8)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_3_1 : Game.Infinitesimal (tf (start 3 1)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_3_3 : Game.Infinitesimal (tf (start 3 3)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_3_4 : Game.Infinitesimal (tf (start 3 4)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_3_5 : Game.Infinitesimal (tf (start 3 5)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_3_6 : Game.Infinitesimal (tf (start 3 6)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_4_1 : Game.Infinitesimal (tf (start 4 1)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_4_2 : Game.Infinitesimal (tf (start 4 2)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_4_3 : Game.Infinitesimal (tf (start 4 3)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_4_4 : Game.Infinitesimal (tf (start 4 4)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_5_1 : Game.Infinitesimal (tf (start 5 1)) :=
  infinitesimal_start_of_decide (by decide +kernel)

theorem infinitesimal_start_5_2 : Game.Infinitesimal (tf (start 5 2)) :=
  infinitesimal_start_of_decide (by decide +kernel)

end Cgt
