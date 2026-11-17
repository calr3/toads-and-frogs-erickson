import Cgt.Certificate

/-! Machine-generated certificate: `T^5 □^3 F^5` is infinitesimal. -/

namespace Cgt.Cert_5_3
open Cell Game

theorem z_0 : le (tf [E, T, T, T, T, T, F, F, E, E, F, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, T, F, F, E, E, F, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1 : le (tf [E, F, E, T, T, T, T, T, F, F, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, T, T, T, F, F, E, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_2 : le (tf [E, T, F, E, T, T, T, T, F, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, T, T, T, F, F, E, F, F] [([E, E, F, T, T, T, T, T, F, F, E, F, F], [E, F, E, T, T, T, T, T, F, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_3 : le (tf [E, T, T, F, E, T, T, T, F, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, T, T, T, F, F, E, F, F] [([E, T, E, F, T, T, T, T, F, F, E, F, F], [E, T, F, E, T, T, T, T, F, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 trivial)

theorem z_4 : le (tf [E, T, T, T, F, E, T, T, F, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, E, T, T, F, F, E, F, F] [([E, T, T, E, F, T, T, T, F, F, E, F, F], [E, T, T, F, E, T, T, T, F, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 trivial)

theorem z_5 : le (tf [E, T, T, T, T, F, E, T, F, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, E, T, F, F, E, F, F] [([E, T, T, T, E, F, T, T, F, F, E, F, F], [E, T, T, T, F, E, T, T, F, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_4 trivial)

theorem z_6 : le (tf [E, T, T, T, F, T, F, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, E, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_7 : le (tf [E, T, T, T, F, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, E, T, F, E, F] [([E, T, T, T, F, T, F, F, E, E, F, T, F], [E, T, T, T, F, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_6 trivial)

theorem z_8 : le (tf [E, T, T, T, F, T, F, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, T, E, E, F, F] [([E, T, T, T, F, T, F, F, E, T, E, F, F], [E, T, T, T, F, T, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_7 trivial)

theorem z_9 : le (tf [E, T, T, T, F, T, F, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, T, E, F, E, F, F] [([E, T, T, T, F, T, F, E, T, F, E, F, F], [E, T, T, T, F, T, F, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_8 trivial)

theorem z_10 : le (tf [E, F, E, T, T, T, T, T, F, F, F, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, T, T, T, T, F, F, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_11 : le (tf [E, T, F, E, T, T, T, T, F, F, F, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, T, T, T, T, F, F, F, F, E] [([E, E, F, T, T, T, T, T, F, F, F, F, E], [E, F, E, T, T, T, T, T, F, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_10 trivial)

theorem z_12 : le (tf [E, T, T, F, E, T, T, T, F, F, F, F, E]) zero :=
  le_zero_of_pairs [E, T, T, F, E, T, T, T, F, F, F, F, E] [([E, T, E, F, T, T, T, T, F, F, F, F, E], [E, T, F, E, T, T, T, T, F, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 trivial)

theorem z_13 : le (tf [E, T, T, T, F, E, T, T, F, F, F, F, E]) zero :=
  le_zero_of_pairs [E, T, T, T, F, E, T, T, F, F, F, F, E] [([E, T, T, E, F, T, T, T, F, F, F, F, E], [E, T, T, F, E, T, T, T, F, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 trivial)

theorem z_14 : le (tf [T, E, F, E, T, T, T, T, F, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, T, T, T, T, F, F, F, E, F] [([E, T, F, E, T, T, T, T, F, F, F, E, F], [E, T, F, E, T, T, T, T, F, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 trivial)

theorem z_15 : le (tf [T, E, T, F, E, T, T, T, F, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, T, T, T, F, F, F, E, F] [([E, T, T, F, E, T, T, T, F, F, F, E, F], [E, T, T, F, E, T, T, T, F, F, F, F, E]), ([T, E, E, F, T, T, T, T, F, F, F, E, F], [T, E, F, E, T, T, T, T, F, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 (And.intro z_14 trivial))

theorem z_16 : le (tf [T, E, T, T, F, E, T, T, F, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, T, F, E, T, T, F, F, F, E, F] [([E, T, T, T, F, E, T, T, F, F, F, E, F], [E, T, T, T, F, E, T, T, F, F, F, F, E]), ([T, E, T, E, F, T, T, T, F, F, F, E, F], [T, E, T, F, E, T, T, T, F, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_15 trivial))

theorem z_17 : le (tf [T, E, T, T, F, T, E, T, F, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, F, T, E, T, F, F, E, F, F] [([E, T, T, T, F, T, E, T, F, F, E, F, F], [E, T, T, T, F, T, F, T, E, F, E, F, F]), ([T, E, T, T, F, E, T, T, F, F, E, F, F], [T, E, T, T, F, E, T, T, F, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_9 (And.intro z_16 trivial))

theorem z_18 : le (tf [T, E, T, T, T, E, F, T, F, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, E, F, T, F, F, E, F, F] [([E, T, T, T, T, E, F, T, F, F, E, F, F], [E, T, T, T, T, F, E, T, F, F, E, F, F]), ([T, E, T, T, E, T, F, T, F, F, E, F, F], [T, E, T, T, F, T, E, T, F, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_5 (And.intro z_17 trivial))

theorem z_19 : le (tf [T, E, T, T, T, T, F, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, T, F, E, F, E, F, F, F] [([E, T, T, T, T, T, F, E, F, E, F, F, F], [E, T, T, T, T, T, F, F, E, E, F, F, F]), ([T, E, T, T, T, E, F, T, F, E, F, F, F], [T, E, T, T, T, E, F, T, F, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_0 (And.intro z_18 trivial))

theorem z_20 : le (tf [E, T, T, T, T, F, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, E, F, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_21 : le (tf [E, T, T, T, T, F, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, E, T, F, E, F, F] [([E, T, T, T, T, F, F, E, E, F, T, F, F], [E, T, T, T, T, F, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_20 trivial)

theorem z_22 : le (tf [E, T, T, T, T, F, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, T, F, E, F, E, F, F] [([E, T, T, T, T, F, E, F, T, F, E, F, F], [E, T, T, T, T, F, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_21 trivial)

theorem z_23 : le (tf [E, T, T, T, T, F, F, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, F, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_24 : le (tf [E, T, T, T, T, F, F, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, F, E, F, T, E, F] [([E, T, T, T, T, F, F, F, E, F, E, T, F], [E, T, T, T, T, F, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_23 trivial)

theorem z_25 : le (tf [E, T, T, T, T, F, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, F, E, T, E, F, F] [([E, T, T, T, T, F, F, F, E, E, T, F, F], [E, T, T, T, T, F, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 trivial)

theorem z_26 : le (tf [T, E, T, T, T, F, F, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, F, F, E, E, T, F, F] [([E, T, T, T, T, F, F, F, E, E, T, F, F], [E, T, T, T, T, F, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 trivial)

theorem z_27 : le (tf [T, E, T, T, T, F, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, F, E, F, T, E, F, F] [([E, T, T, T, T, F, F, E, F, T, E, F, F], [E, T, T, T, T, F, F, F, E, T, E, F, F]), ([T, E, T, T, T, F, F, E, F, E, T, F, F], [T, E, T, T, T, F, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 (And.intro z_26 trivial))

theorem z_28 : le (tf [T, E, T, T, T, F, F, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, F, E, T, E, F, F, F] [([E, T, T, T, T, F, F, E, T, E, F, F, F], [E, T, T, T, T, F, F, E, T, F, E, F, F]), ([T, E, T, T, T, F, F, E, E, T, F, F, F], [T, E, T, T, T, F, F, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_21 (And.intro z_27 trivial))

theorem z_29 : le (tf [T, E, T, T, T, F, T, F, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, T, F, E, E, F, F, F] [([E, T, T, T, T, F, T, F, E, E, F, F, F], [E, T, T, T, T, F, T, F, E, F, E, F, F]), ([T, E, T, T, T, F, E, F, T, E, F, F, F], [T, E, T, T, T, F, F, E, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 (And.intro z_28 trivial))

theorem z_30 : le (tf [E, T, T, T, T, F, F, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, T, F, E, E, F, F] [([E, T, T, T, T, F, F, E, F, T, E, F, F], [E, T, T, T, T, F, F, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 trivial)

theorem z_31 : le (tf [E, T, T, T, T, F, F, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, F, F, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_32 : le (tf [E, T, T, T, T, F, F, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, F, F, E, T, F, E] [([E, T, T, T, T, F, F, F, F, E, E, F, T], [E, T, T, T, T, F, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_31 trivial)

theorem z_33 : le (tf [E, T, T, T, T, F, F, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, F, F, T, E, E, F] [([E, T, T, T, T, F, F, F, F, E, T, E, F], [E, T, T, T, T, F, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 trivial)

theorem z_34 : le (tf [E, T, T, T, T, F, F, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, T, T, F, F, F, T, E, F, E, F] [([E, T, T, T, T, F, F, F, E, T, F, E, F], [E, T, T, T, T, F, F, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_33 trivial)

theorem z_35 : le (tf [T, E, T, T, T, F, F, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, F, F, E, F, E, T, F] [([E, T, T, T, T, F, F, F, E, F, E, T, F], [E, T, T, T, T, F, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_23 trivial)

theorem z_36 : le (tf [T, E, T, T, T, F, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, F, F, E, T, F, E, F] [([E, T, T, T, T, F, F, F, E, T, F, E, F], [E, T, T, T, T, F, F, F, F, T, E, E, F]), ([T, E, T, T, T, F, F, F, E, E, F, T, F], [T, E, T, T, T, F, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_33 (And.intro z_35 trivial))

theorem z_37 : le (tf [T, E, T, T, T, F, F, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, F, F, T, E, E, F, F] [([E, T, T, T, T, F, F, F, T, E, E, F, F], [E, T, T, T, T, F, F, F, T, E, F, E, F]), ([T, E, T, T, T, F, F, F, E, T, E, F, F], [T, E, T, T, T, F, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_34 (And.intro z_36 trivial))

theorem z_38 : le (tf [T, E, T, T, T, F, F, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, T, F, F, T, E, F, E, F, F] [([E, T, T, T, T, F, F, T, E, F, E, F, F], [E, T, T, T, T, F, F, T, F, E, E, F, F]), ([T, E, T, T, T, F, F, E, T, F, E, F, F], [T, E, T, T, T, F, F, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_30 (And.intro z_37 trivial))

theorem z_39 : le (tf [T, T, E, T, T, F, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, T, F, F, E, F, E, T, F, F] [([T, E, T, T, T, F, F, E, F, E, T, F, F], [T, E, T, T, T, F, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_26 trivial)

theorem z_40 : le (tf [T, T, E, T, T, F, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, T, F, F, E, T, F, E, F, F] [([T, E, T, T, T, F, F, E, T, F, E, F, F], [T, E, T, T, T, F, F, F, T, E, E, F, F]), ([T, T, E, T, T, F, F, E, E, F, T, F, F], [T, T, E, T, T, F, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_37 (And.intro z_39 trivial))

theorem z_41 : le (tf [T, T, E, T, T, F, F, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, T, F, F, T, E, E, F, F, F] [([T, E, T, T, T, F, F, T, E, E, F, F, F], [T, E, T, T, T, F, F, T, E, F, E, F, F]), ([T, T, E, T, T, F, F, E, T, E, F, F, F], [T, T, E, T, T, F, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_38 (And.intro z_40 trivial))

theorem z_42 : le (tf [T, T, E, T, T, F, T, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, T, F, T, E, F, E, F, F, F] [([T, E, T, T, T, F, T, E, F, E, F, F, F], [T, E, T, T, T, F, T, F, E, E, F, F, F]), ([T, T, E, T, T, F, E, T, F, E, F, F, F], [T, T, E, T, T, F, F, T, E, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_29 (And.intro z_41 trivial))

theorem z_43 : le (tf [T, T, E, T, T, T, E, F, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, T, T, E, F, F, E, F, F, F] [([T, E, T, T, T, T, E, F, F, E, F, F, F], [T, E, T, T, T, T, F, E, F, E, F, F, F]), ([T, T, E, T, T, E, T, F, F, E, F, F, F], [T, T, E, T, T, F, T, E, F, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_19 (And.intro z_42 trivial))

theorem z_44 : le (tf [T, T, T, F, T, F, T, F, F, F, E, E, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, T, F, F, F, E, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_45 : le (tf [T, T, T, F, F, F, F, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, F, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_46 : le (tf [T, T, T, F, F, F, F, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, T, F, E, T] [([T, T, T, F, F, F, F, E, E, E, F, T, T], [T, T, T, F, F, F, F, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_45 trivial)

theorem z_47 : le (tf [T, T, T, F, F, F, E, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, E, T, F, T, E] [([T, T, T, F, F, F, E, F, E, T, F, E, T], [T, T, T, F, F, F, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 trivial)

theorem z_48 : le (tf [T, T, T, F, F, F, E, F, E, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, E, T, T, E, F] [([T, T, T, F, F, F, E, F, E, T, E, T, F], [T, T, T, F, F, F, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 trivial)

theorem z_49 : le (tf [T, T, T, F, F, F, F, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, F, E, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_50 : le (tf [T, T, T, F, F, F, F, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, F, E, T, E, T] [([T, T, T, F, F, F, F, E, F, E, E, T, T], [T, T, T, F, F, F, F, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_49 trivial)

theorem z_51 : le (tf [T, T, T, F, F, F, F, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, T, F, E, E, T] [([T, T, T, F, F, F, F, E, E, F, T, E, T], [T, T, T, F, F, F, F, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_50 trivial)

theorem z_52 : le (tf [T, T, T, F, F, F, F, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, T, E, E, F, E, T] [([T, T, T, F, F, F, F, E, T, E, F, E, T], [T, T, T, F, F, F, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 trivial)

theorem z_53 : le (tf [T, T, T, F, F, F, E, T, F, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, F, E, F, T, E] [([T, T, T, F, F, F, E, E, F, T, F, T, E], [T, T, T, F, F, F, E, F, E, T, F, T, E]), ([T, T, T, F, F, F, E, T, F, E, F, E, T], [T, T, T, F, F, F, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 (And.intro z_52 trivial))

theorem z_54 : le (tf [T, T, T, F, F, F, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, F, E, T, E, F] [([T, T, T, F, F, F, E, E, F, T, T, E, F], [T, T, T, F, F, F, E, F, E, T, T, E, F]), ([T, T, T, F, F, F, E, T, F, E, E, T, F], [T, T, T, F, F, F, E, T, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_53 trivial))

theorem z_55 : le (tf [T, T, T, F, F, F, T, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, T, E, F, E, E, T, F] [([T, T, T, F, F, F, E, T, F, E, E, T, F], [T, T, T, F, F, F, E, T, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_53 trivial)

theorem z_56 : le (tf [T, T, T, F, F, F, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, T, E, E, F, T, E, F] [([T, T, T, F, F, F, E, T, E, F, T, E, F], [T, T, T, F, F, F, E, T, F, E, T, E, F]), ([T, T, T, F, F, F, T, E, E, F, E, T, F], [T, T, T, F, F, F, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_54 (And.intro z_55 trivial))

theorem z_57 : le (tf [T, T, T, F, F, E, T, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, F, T, F, E, E, F] [([T, T, T, F, F, E, T, F, E, F, T, E, F], [T, T, T, F, F, F, T, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 trivial)

theorem z_58 : le (tf [T, T, T, F, T, F, F, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_59 : le (tf [T, T, T, F, T, F, F, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, E, F, T, E, F] [([T, T, T, F, T, F, F, E, E, F, E, T, F], [T, T, T, F, T, F, F, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_58 trivial)

theorem z_60 : le (tf [T, T, T, F, T, F, E, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, F, T, F, E, E, F] [([T, T, T, F, E, F, T, F, T, F, E, E, F], [T, T, T, F, F, E, T, F, T, F, E, E, F]), ([T, T, T, F, T, F, E, F, E, F, T, E, F], [T, T, T, F, T, F, F, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_57 (And.intro z_59 trivial))

theorem z_61 : le (tf [T, T, T, F, F, F, F, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, F, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_62 : le (tf [T, T, T, F, F, F, F, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, F, T, E, T] [([T, T, T, F, F, F, F, E, E, F, E, T, T], [T, T, T, F, F, F, F, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_61 trivial)

theorem z_63 : le (tf [T, T, T, F, F, F, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, T, E, F, T] [([T, T, T, F, F, F, F, E, E, E, T, F, T], [T, T, T, F, F, F, F, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_62 trivial)

theorem z_64 : le (tf [T, T, T, F, F, F, E, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, E, T, T, F, E] [([T, T, T, F, F, F, E, F, E, T, E, F, T], [T, T, T, F, F, F, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_63 trivial)

theorem z_65 : le (tf [T, T, T, F, F, F, F, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, E, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_66 : le (tf [T, T, T, F, F, F, E, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, E, T, F, E, T] [([T, T, T, F, F, F, E, F, E, E, F, T, T], [T, T, T, F, F, F, F, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_65 trivial)

theorem z_67 : le (tf [T, T, T, F, F, F, E, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, F, E, F, E, T] [([T, T, T, F, F, F, E, E, F, T, F, E, T], [T, T, T, F, F, F, E, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 trivial)

theorem z_68 : le (tf [T, T, T, F, F, F, E, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, F, E, T, F, E] [([T, T, T, F, F, F, E, E, F, T, T, F, E], [T, T, T, F, F, F, E, F, E, T, T, F, E]), ([T, T, T, F, F, F, E, T, F, E, E, F, T], [T, T, T, F, F, F, E, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_64 (And.intro z_67 trivial))

theorem z_69 : le (tf [T, T, T, F, F, F, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, F, T, E, E, F] [([T, T, T, F, F, F, E, T, F, E, T, E, F], [T, T, T, F, F, F, E, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_68 trivial)

theorem z_70 : le (tf [T, T, T, F, F, F, F, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_71 : le (tf [T, T, T, F, F, F, E, F, E, T, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, E, T, E, T, F] [([T, T, T, F, F, F, E, F, E, E, T, T, F], [T, T, T, F, F, F, F, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 trivial)

theorem z_72 : le (tf [T, T, T, F, F, F, E, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, F, E, E, T, F] [([T, T, T, F, F, F, E, E, F, T, E, T, F], [T, T, T, F, F, F, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_71 trivial)

theorem z_73 : le (tf [T, T, T, F, F, F, T, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, T, E, E, F, E, T, F] [([T, T, T, F, F, F, E, T, E, F, E, T, F], [T, T, T, F, F, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_72 trivial)

theorem z_74 : le (tf [T, T, T, F, F, F, T, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, T, E, E, T, F, E, F] [([T, T, T, F, F, F, E, T, E, T, F, E, F], [T, T, T, F, F, F, E, T, F, T, E, E, F]), ([T, T, T, F, F, F, T, E, E, E, F, T, F], [T, T, T, F, F, F, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 (And.intro z_73 trivial))

theorem z_75 : le (tf [T, T, T, F, F, E, T, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, F, T, E, F, E, F] [([T, T, T, F, F, E, T, F, E, T, F, E, F], [T, T, T, F, F, F, T, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_74 trivial)

theorem z_76 : le (tf [T, T, T, F, T, F, F, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, E, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_77 : le (tf [T, T, T, F, T, F, F, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, E, T, F, E, F] [([T, T, T, F, T, F, F, E, E, E, F, T, F], [T, T, T, F, T, F, F, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_76 trivial)

theorem z_78 : le (tf [T, T, T, F, T, F, E, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, F, T, E, F, E, F] [([T, T, T, F, E, F, T, F, T, E, F, E, F], [T, T, T, F, F, E, T, F, T, E, F, E, F]), ([T, T, T, F, T, F, E, F, E, T, F, E, F], [T, T, T, F, T, F, F, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_75 (And.intro z_77 trivial))

theorem z_79 : le (tf [T, T, T, F, F, F, E, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_80 : le (tf [T, T, T, F, F, F, E, F, T, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, T, E, E, T, F] [([T, T, T, F, F, F, E, F, E, T, E, T, F], [T, T, T, F, F, F, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 trivial)

theorem z_81 : le (tf [T, T, T, F, F, F, E, T, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, E, F, E, T, F] [([T, T, T, F, F, F, E, E, T, F, E, T, F], [T, T, T, F, F, F, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 trivial)

theorem z_82 : le (tf [T, T, T, F, F, F, E, T, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, E, T, F, E, F] [([T, T, T, F, F, F, E, E, T, T, F, E, F], [T, T, T, F, F, F, E, E, T, T, F, F, E]), ([T, T, T, F, F, F, E, T, E, E, F, T, F], [T, T, T, F, F, F, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 (And.intro z_81 trivial))

theorem z_83 : le (tf [T, T, T, F, F, F, T, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, T, E, E, T, E, F, F] [([T, T, T, F, F, F, E, T, E, T, E, F, F], [T, T, T, F, F, F, E, T, E, T, F, E, F]), ([T, T, T, F, F, F, T, E, E, E, T, F, F], [T, T, T, F, F, F, T, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_56 trivial))

theorem z_84 : le (tf [T, T, T, F, F, E, T, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, F, T, E, E, F, F] [([T, T, T, F, F, E, T, F, E, T, E, F, F], [T, T, T, F, F, F, T, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 trivial)

theorem z_85 : le (tf [T, T, T, F, T, F, F, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, E, T, E, F, F] [([T, T, T, F, T, F, F, E, E, E, T, F, F], [T, T, T, F, T, F, F, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_59 trivial)

theorem z_86 : le (tf [T, T, T, F, T, F, E, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, F, T, E, E, F, F] [([T, T, T, F, E, F, T, F, T, E, E, F, F], [T, T, T, F, F, E, T, F, T, E, E, F, F]), ([T, T, T, F, T, F, E, F, E, T, E, F, F], [T, T, T, F, T, F, F, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 (And.intro z_85 trivial))

theorem z_87 : le (tf [T, T, T, F, F, F, E, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, F, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_88 : le (tf [T, T, T, F, F, F, E, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, T, F, E, T, F] [([T, T, T, F, F, F, E, E, E, F, T, T, F], [T, T, T, F, F, F, E, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_87 trivial)

theorem z_89 : le (tf [T, T, T, F, F, E, F, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, E, T, F, T, E, F] [([T, T, T, F, F, E, F, E, T, F, E, T, F], [T, T, T, F, F, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 trivial)

theorem z_90 : le (tf [T, T, T, F, F, E, F, E, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, E, T, T, E, F, F] [([T, T, T, F, F, E, F, E, T, E, T, F, F], [T, T, T, F, F, E, F, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_89 trivial)

theorem z_91 : le (tf [T, T, T, F, F, F, E, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, T, E, E, F, T] [([T, T, T, F, F, F, E, F, E, T, E, F, T], [T, T, T, F, F, F, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_63 trivial)

theorem z_92 : le (tf [T, T, T, F, F, F, E, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, T, F, T, F, E] [([T, T, T, F, F, F, E, E, T, F, E, F, T], [T, T, T, F, F, F, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_91 trivial)

theorem z_93 : le (tf [T, T, T, F, F, F, E, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, E, F, T, E, F] [([T, T, T, F, F, F, E, E, T, F, T, E, F], [T, T, T, F, F, F, E, E, T, F, T, F, E]), ([T, T, T, F, F, F, E, T, E, F, E, T, F], [T, T, T, F, F, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 (And.intro z_72 trivial))

theorem z_94 : le (tf [T, T, T, F, F, F, T, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, T, E, E, E, T, F, F] [([T, T, T, F, F, F, E, T, E, E, T, F, F], [T, T, T, F, F, F, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 trivial)

theorem z_95 : le (tf [T, T, T, F, F, E, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, F, E, T, E, F, F] [([T, T, T, F, F, E, E, F, T, T, E, F, F], [T, T, T, F, F, E, F, E, T, T, E, F, F]), ([T, T, T, F, F, E, T, F, E, E, T, F, F], [T, T, T, F, F, F, T, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_90 (And.intro z_94 trivial))

theorem z_96 : le (tf [T, T, T, F, F, E, T, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, T, F, E, E, F, F] [([T, T, T, F, F, E, T, E, F, T, E, F, F], [T, T, T, F, F, E, T, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_95 trivial)

theorem z_97 : le (tf [T, T, T, F, T, F, F, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, E, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_98 : le (tf [T, T, T, F, T, F, E, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, F, E, T, E, F, F] [([T, T, T, F, E, F, T, F, E, T, E, F, F], [T, T, T, F, F, E, T, F, E, T, E, F, F]), ([T, T, T, F, T, F, E, F, E, E, T, F, F], [T, T, T, F, T, F, F, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_95 (And.intro z_97 trivial))

theorem z_99 : le (tf [T, T, T, F, T, F, E, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, T, F, E, E, F, F] [([T, T, T, F, E, F, T, T, F, E, E, F, F], [T, T, T, F, F, E, T, T, F, E, E, F, F]), ([T, T, T, F, T, F, E, E, F, T, E, F, F], [T, T, T, F, T, F, E, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_96 (And.intro z_98 trivial))

theorem z_100 : le (tf [T, T, T, F, F, E, T, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, T, E, F, E, F, F] [([T, T, T, F, F, E, T, E, T, F, E, F, F], [T, T, T, F, F, E, T, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 trivial)

theorem z_101 : le (tf [T, T, T, F, T, F, E, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, T, E, F, E, F, F] [([T, T, T, F, E, F, T, T, E, F, E, F, F], [T, T, T, F, F, E, T, T, E, F, E, F, F]), ([T, T, T, F, T, F, E, E, T, F, E, F, F], [T, T, T, F, T, F, E, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_100 (And.intro z_86 trivial))

theorem z_102 : le (tf [T, T, T, F, F, E, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, T, T, F, F, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_103 : le (tf [T, T, T, F, F, E, F, T, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, E, E, T, F, F] [([T, T, T, F, F, E, F, E, T, E, T, F, F], [T, T, T, F, F, E, F, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_89 trivial)

theorem z_104 : le (tf [T, T, T, F, F, E, T, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, E, F, E, T, F, F] [([T, T, T, F, F, E, E, T, F, E, T, F, F], [T, T, T, F, F, E, F, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_103 trivial)

theorem z_105 : le (tf [T, T, T, F, F, E, T, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, E, T, F, E, F, F] [([T, T, T, F, F, E, E, T, T, F, E, F, F], [T, T, T, F, F, E, E, T, T, F, F, E, F]), ([T, T, T, F, F, E, T, E, E, F, T, F, F], [T, T, T, F, F, E, T, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_102 (And.intro z_104 trivial))

theorem z_106 : le (tf [T, T, T, F, F, E, T, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, T, E, E, F, F, F] [([T, T, T, F, F, E, T, E, T, E, F, F, F], [T, T, T, F, F, E, T, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 trivial)

theorem z_107 : le (tf [T, T, T, F, T, F, E, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, E, F, E, T, F, F] [([T, T, T, F, E, F, T, E, F, E, T, F, F], [T, T, T, F, F, E, T, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 trivial)

theorem z_108 : le (tf [T, T, T, F, T, F, E, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, E, T, F, E, F, F] [([T, T, T, F, E, F, T, E, T, F, E, F, F], [T, T, T, F, F, E, T, E, T, F, E, F, F]), ([T, T, T, F, T, F, E, E, E, F, T, F, F], [T, T, T, F, T, F, E, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_107 trivial))

theorem z_109 : le (tf [T, T, T, F, T, F, E, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, T, E, E, F, F, F] [([T, T, T, F, E, F, T, T, E, E, F, F, F], [T, T, T, F, F, E, T, T, E, E, F, F, F]), ([T, T, T, F, T, F, E, E, T, E, F, F, F], [T, T, T, F, T, F, E, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_108 trivial))

theorem z_110 : le (tf [F, E, T, T, T, T, T, F, F, F, F, E, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, T, F, F, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_111 : le (tf [T, F, E, T, T, T, T, F, F, F, F, E, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, T, F, F, F, F, E, E] [([E, F, T, T, T, T, T, F, F, F, F, E, E], [F, E, T, T, T, T, T, F, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_110 trivial)

theorem z_112 : le (tf [T, T, F, E, T, T, T, F, F, F, F, E, E]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, T, F, F, F, F, E, E] [([T, E, F, T, T, T, T, F, F, F, F, E, E], [T, F, E, T, T, T, T, F, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 trivial)

theorem z_113 : le (tf [T, T, T, F, E, T, T, F, F, F, F, E, E]) zero :=
  le_zero_of_pairs [T, T, T, F, E, T, T, F, F, F, F, E, E] [([T, T, E, F, T, T, T, F, F, F, F, E, E], [T, T, F, E, T, T, T, F, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_112 trivial)

theorem z_114 : le (tf [E, F, T, T, T, T, T, F, F, F, F, E, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, F, F, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_115 : le (tf [T, F, T, E, T, T, T, F, F, F, E, F, E]) zero :=
  le_zero_of_pairs [T, F, T, E, T, T, T, F, F, F, E, F, E] [([T, F, E, T, T, T, T, F, F, F, E, F, E], [T, F, E, T, T, T, T, F, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 trivial)

theorem z_116 : le (tf [T, T, E, F, T, T, T, F, F, F, E, F, E]) zero :=
  le_zero_of_pairs [T, T, E, F, T, T, T, F, F, F, E, F, E] [([T, E, T, F, T, T, T, F, F, F, E, F, E], [T, F, T, E, T, T, T, F, F, F, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_115 trivial)

theorem z_117 : le (tf [T, F, E, T, T, T, T, F, F, F, E, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, T, F, F, F, E, F, E] [([E, F, T, T, T, T, T, F, F, F, E, F, E], [E, F, T, T, T, T, T, F, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_114 trivial)

theorem z_118 : le (tf [T, F, T, E, T, T, T, F, F, F, E, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, T, T, F, F, F, E, E, F] [([T, F, E, T, T, T, T, F, F, F, E, E, F], [T, F, E, T, T, T, T, F, F, F, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 trivial)

theorem z_119 : le (tf [T, T, E, F, T, T, T, F, F, F, E, E, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, T, T, F, F, F, E, E, F] [([T, E, T, F, T, T, T, F, F, F, E, E, F], [T, F, T, E, T, T, T, F, F, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_118 trivial)

theorem z_120 : le (tf [F, E, T, T, T, T, T, F, F, F, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, T, F, F, F, E, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_121 : le (tf [T, F, E, T, T, T, T, F, F, F, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, T, F, F, F, E, E, F] [([E, F, T, T, T, T, T, F, F, F, E, E, F], [F, E, T, T, T, T, T, F, F, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_120 trivial)

theorem z_122 : le (tf [T, F, T, E, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, T, T, F, F, E, F, E, F] [([T, F, E, T, T, T, T, F, F, E, F, E, F], [T, F, E, T, T, T, T, F, F, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_121 trivial)

theorem z_123 : le (tf [T, T, E, F, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, T, T, F, F, E, F, E, F] [([T, E, T, F, T, T, T, F, F, E, F, E, F], [T, F, T, E, T, T, T, F, F, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_122 trivial)

theorem z_124 : le (tf [F, E, T, T, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, T, F, F, E, F, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_125 : le (tf [T, F, E, T, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, T, F, F, E, F, E, F] [([E, F, T, T, T, T, T, F, F, E, F, E, F], [F, E, T, T, T, T, T, F, F, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_124 trivial)

theorem z_126 : le (tf [T, F, T, E, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, T, T, F, F, E, E, F, F] [([T, F, E, T, T, T, T, F, F, E, E, F, F], [T, F, E, T, T, T, T, F, F, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_125 trivial)

theorem z_127 : le (tf [T, T, E, F, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, T, T, F, F, E, E, F, F] [([T, E, T, F, T, T, T, F, F, E, E, F, F], [T, F, T, E, T, T, T, F, F, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_126 trivial)

theorem z_128 : le (tf [E, T, T, F, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, T, F, F, E, F, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_129 : le (tf [T, E, T, F, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, T, T, F, F, E, E, F, F] [([E, T, T, F, T, T, T, F, F, E, E, F, F], [E, T, T, F, T, T, T, F, F, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 trivial)

theorem z_130 : le (tf [E, T, T, F, T, T, F, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, F, F, F, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_131 : le (tf [E, T, T, F, T, T, F, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, F, F, F, E, T, F, E] [([E, T, T, F, T, T, F, F, F, E, E, F, T], [E, T, T, F, T, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_130 trivial)

theorem z_132 : le (tf [E, T, T, F, T, T, F, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, F, F, F, T, E, E, F] [([E, T, T, F, T, T, F, F, F, E, T, E, F], [E, T, T, F, T, T, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 trivial)

theorem z_133 : le (tf [E, T, T, F, T, T, F, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, F, F, T, E, F, E, F] [([E, T, T, F, T, T, F, F, E, T, F, E, F], [E, T, T, F, T, T, F, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_132 trivial)

theorem z_134 : le (tf [E, T, T, F, F, E, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, T, T, T, F, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_135 : le (tf [E, T, T, F, T, F, E, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, E, T, T, F, F, F, E] [([E, T, T, F, E, F, T, T, T, F, F, F, E], [E, T, T, F, F, E, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_134 trivial)

theorem z_136 : le (tf [F, E, F, E, T, T, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, T, F, F, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_137 : le (tf [F, E, T, F, E, T, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, T, F, F, E, F] [([F, E, E, F, T, T, T, T, T, F, F, E, F], [F, E, F, E, T, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_136 trivial)

theorem z_138 : le (tf [F, E, T, T, F, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, T, F, F, E, F] [([F, E, T, E, F, T, T, T, T, F, F, E, F], [F, E, T, F, E, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 trivial)

theorem z_139 : le (tf [T, F, E, F, E, T, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, T, F, F, E, F] [([E, F, T, F, E, T, T, T, T, F, F, E, F], [F, E, T, F, E, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 trivial)

theorem z_140 : le (tf [T, F, E, T, F, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, T, F, F, E, F] [([E, F, T, T, F, E, T, T, T, F, F, E, F], [F, E, T, T, F, E, T, T, T, F, F, E, F]), ([T, F, E, E, F, T, T, T, T, F, F, E, F], [T, F, E, F, E, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_138 (And.intro z_139 trivial))

theorem z_141 : le (tf [T, F, T, E, E, F, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, E, F, T, T, T, F, F, E, F] [([T, F, E, T, E, F, T, T, T, F, F, E, F], [T, F, E, T, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_140 trivial)

theorem z_142 : le (tf [T, E, T, F, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, F, E, T, T, F, F, E, F] [([E, T, T, F, T, F, E, T, T, F, F, E, F], [E, T, T, F, T, F, E, T, T, F, F, F, E]), ([T, E, T, F, E, F, T, T, T, F, F, E, F], [T, F, T, E, E, F, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_135 (And.intro z_141 trivial))

theorem z_143 : le (tf [T, E, T, F, T, T, F, E, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, T, F, E, T, F, F, E, F] [([E, T, T, F, T, T, F, E, T, F, F, E, F], [E, T, T, F, T, T, F, F, T, E, F, E, F]), ([T, E, T, F, T, E, F, T, T, F, F, E, F], [T, E, T, F, T, F, E, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_133 (And.intro z_142 trivial))

theorem z_144 : le (tf [E, T, T, F, T, F, T, F, F, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, F, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_145 : le (tf [E, T, T, F, T, F, T, F, F, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, F, E, F, T, E] [([E, T, T, F, T, F, T, F, F, E, F, E, T], [E, T, T, F, T, F, T, F, F, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_144 trivial)

theorem z_146 : le (tf [E, T, T, F, T, F, T, F, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, F, E, T, E, F] [([E, T, T, F, T, F, T, F, F, E, E, T, F], [E, T, T, F, T, F, T, F, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_145 trivial)

theorem z_147 : le (tf [E, T, T, F, T, F, T, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, T, F, E, E, F] [([E, T, T, F, T, F, T, F, E, F, T, E, F], [E, T, T, F, T, F, T, F, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_146 trivial)

theorem z_148 : le (tf [F, E, T, T, T, F, T, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, F, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_149 : le (tf [F, E, T, T, T, F, T, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, F, E, T, F, E] [([F, E, T, T, T, F, T, F, F, E, E, F, T], [F, E, T, T, T, F, T, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_148 trivial)

theorem z_150 : le (tf [F, E, T, T, T, F, T, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, F, T, E, E, F] [([F, E, T, T, T, F, T, F, F, E, T, E, F], [F, E, T, T, T, F, T, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_149 trivial)

theorem z_151 : le (tf [T, F, E, T, T, F, T, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, F, E, F, E, T] [([E, F, T, T, T, F, T, F, F, E, F, E, T], [F, E, T, T, T, F, T, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_148 trivial)

theorem z_152 : le (tf [T, F, E, T, T, F, T, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, F, E, T, F, E] [([E, F, T, T, T, F, T, F, F, E, T, F, E], [F, E, T, T, T, F, T, F, F, E, T, F, E]), ([T, F, E, T, T, F, T, F, F, E, E, F, T], [T, F, E, T, T, F, T, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_149 (And.intro z_151 trivial))

theorem z_153 : le (tf [T, F, E, T, T, F, T, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, F, T, E, E, F] [([E, F, T, T, T, F, T, F, F, T, E, E, F], [F, E, T, T, T, F, T, F, F, T, E, E, F]), ([T, F, E, T, T, F, T, F, F, E, T, E, F], [T, F, E, T, T, F, T, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_150 (And.intro z_152 trivial))

theorem z_154 : le (tf [T, F, F, F, E, F, E, E, T, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, E, T, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_155 : le (tf [T, F, F, F, E, E, F, T, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, F, T, E, T, T, T, F] [([T, F, F, F, E, E, F, E, T, T, T, T, F], [T, F, F, F, E, F, E, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_154 trivial)

theorem z_156 : le (tf [T, F, F, F, E, E, T, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, E, F, T, T, T, F] [([T, F, F, F, E, E, E, T, F, T, T, T, F], [T, F, F, F, E, E, F, T, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_155 trivial)

theorem z_157 : le (tf [T, F, F, E, F, E, T, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, F, E, T, T, F] [([T, F, F, E, F, E, T, E, F, T, T, T, F], [T, F, F, F, E, E, T, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_156 trivial)

theorem z_158 : le (tf [T, F, F, E, F, E, T, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, T, F, E, T, F] [([T, F, F, E, F, E, T, T, E, F, T, T, F], [T, F, F, E, F, E, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_157 trivial)

theorem z_159 : le (tf [T, F, F, E, F, E, T, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, T, T, F, E, F] [([T, F, F, E, F, E, T, T, T, E, F, T, F], [T, F, F, E, F, E, T, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 trivial)

theorem z_160 : le (tf [T, F, F, F, E, E, E, F, T, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, E, F, T, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_161 : le (tf [T, F, F, E, F, E, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, F, E, T, T, T, F] [([T, F, F, E, F, E, E, F, T, T, T, T, F], [T, F, F, F, E, E, E, F, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_160 trivial)

theorem z_162 : le (tf [T, F, F, E, T, F, E, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, F, E, T, T, T, F] [([T, F, F, E, E, F, T, F, E, T, T, T, F], [T, F, F, E, F, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_161 trivial)

theorem z_163 : le (tf [T, F, F, E, T, F, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, F, E, T, T, F] [([T, F, F, E, E, F, T, T, F, E, T, T, F], [T, F, F, E, F, E, T, T, F, E, T, T, F]), ([T, F, F, E, T, F, E, E, F, T, T, T, F], [T, F, F, E, T, F, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_157 (And.intro z_162 trivial))

theorem z_164 : le (tf [T, F, F, E, T, F, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, T, F, E, T, F] [([T, F, F, E, E, F, T, T, T, F, E, T, F], [T, F, F, E, F, E, T, T, T, F, E, T, F]), ([T, F, F, E, T, F, E, T, E, F, T, T, F], [T, F, F, E, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 (And.intro z_163 trivial))

theorem z_165 : le (tf [T, F, F, E, T, F, E, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, T, T, F, E, F] [([T, F, F, E, E, F, T, T, T, T, F, E, F], [T, F, F, E, F, E, T, T, T, T, F, E, F]), ([T, F, F, E, T, F, E, T, T, E, F, T, F], [T, F, F, E, T, F, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_159 (And.intro z_164 trivial))

theorem z_166 : le (tf [T, F, F, E, T, T, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, E, F, E, T, T, F] [([T, F, F, E, T, E, F, T, F, E, T, T, F], [T, F, F, E, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_163 trivial)

theorem z_167 : le (tf [T, F, F, E, T, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, E, T, F, E, T, F] [([T, F, F, E, T, E, F, T, T, F, E, T, F], [T, F, F, E, T, F, E, T, T, F, E, T, F]), ([T, F, F, E, T, T, F, E, E, F, T, T, F], [T, F, F, E, T, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_164 (And.intro z_166 trivial))

theorem z_168 : le (tf [T, F, F, E, T, T, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, E, T, T, F, E, F] [([T, F, F, E, T, E, F, T, T, T, F, E, F], [T, F, F, E, T, F, E, T, T, T, F, E, F]), ([T, F, F, E, T, T, F, E, T, E, F, T, F], [T, F, F, E, T, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_165 (And.intro z_167 trivial))

theorem z_169 : le (tf [T, F, T, F, F, E, F, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, F, E, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_170 : le (tf [T, F, T, F, F, E, E, F, T, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, F, T, E, T, T, F] [([T, F, T, F, F, E, E, F, E, T, T, T, F], [T, F, T, F, F, E, F, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_169 trivial)

theorem z_171 : le (tf [T, F, T, F, F, E, E, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, T, E, F, T, T, F] [([T, F, T, F, F, E, E, E, T, F, T, T, F], [T, F, T, F, F, E, E, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_170 trivial)

theorem z_172 : le (tf [T, F, T, F, E, F, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, F, E, T, T, F, E, T, F] [([T, F, E, F, T, F, E, T, T, F, E, T, F], [T, F, F, E, T, F, E, T, T, F, E, T, F]), ([T, F, T, F, E, F, E, T, E, F, T, T, F], [T, F, T, F, F, E, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_164 (And.intro z_171 trivial))

theorem z_173 : le (tf [T, F, T, F, E, F, E, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, F, E, T, T, T, F, E, F] [([T, F, E, F, T, F, E, T, T, T, F, E, F], [T, F, F, E, T, F, E, T, T, T, F, E, F]), ([T, F, T, F, E, F, E, T, T, E, F, T, F], [T, F, T, F, E, F, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_165 (And.intro z_172 trivial))

theorem z_174 : le (tf [T, F, T, F, F, E, E, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, E, F, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_175 : le (tf [T, F, T, F, E, F, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, F, E, T, F, E, T, T, F] [([T, F, E, F, T, F, E, T, F, E, T, T, F], [T, F, F, E, T, F, E, T, F, E, T, T, F]), ([T, F, T, F, E, F, E, E, F, T, T, T, F], [T, F, T, F, F, E, E, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_163 (And.intro z_174 trivial))

theorem z_176 : le (tf [T, F, T, F, E, T, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, F, E, F, E, T, T, F] [([T, F, E, F, T, T, F, E, F, E, T, T, F], [T, F, F, E, T, T, F, E, F, E, T, T, F]), ([T, F, T, F, E, E, F, T, F, E, T, T, F], [T, F, T, F, E, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_166 (And.intro z_175 trivial))

theorem z_177 : le (tf [T, F, T, F, E, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, F, E, T, F, E, T, F] [([T, F, E, F, T, T, F, E, T, F, E, T, F], [T, F, F, E, T, T, F, E, T, F, E, T, F]), ([T, F, T, F, E, E, F, T, T, F, E, T, F], [T, F, T, F, E, F, E, T, T, F, E, T, F]), ([T, F, T, F, E, T, F, E, E, F, T, T, F], [T, F, T, F, E, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_167 (And.intro z_172 (And.intro z_176 trivial)))

theorem z_178 : le (tf [T, F, T, F, E, T, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, F, E, T, T, F, E, F] [([T, F, E, F, T, T, F, E, T, T, F, E, F], [T, F, F, E, T, T, F, E, T, T, F, E, F]), ([T, F, T, F, E, E, F, T, T, T, F, E, F], [T, F, T, F, E, F, E, T, T, T, F, E, F]), ([T, F, T, F, E, T, F, E, T, E, F, T, F], [T, F, T, F, E, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_168 (And.intro z_173 (And.intro z_177 trivial)))

theorem z_179 : le (tf [T, F, T, F, T, E, F, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, F, E, E, F, T, T, F] [([T, F, T, F, E, T, F, E, E, F, T, T, F], [T, F, T, F, E, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_176 trivial)

theorem z_180 : le (tf [T, F, T, F, T, E, E, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, E, F, T, F, E, T, F] [([T, F, T, F, E, T, E, F, T, F, E, T, F], [T, F, T, F, E, T, F, E, T, F, E, T, F]), ([T, F, T, F, T, E, E, F, E, F, T, T, F], [T, F, T, F, T, E, F, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_177 (And.intro z_179 trivial))

theorem z_181 : le (tf [T, F, T, F, T, E, E, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, E, F, T, T, F, E, F] [([T, F, T, F, E, T, E, F, T, T, F, E, F], [T, F, T, F, E, T, F, E, T, T, F, E, F]), ([T, F, T, F, T, E, E, F, T, E, F, T, F], [T, F, T, F, T, E, E, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_178 (And.intro z_180 trivial))

theorem z_182 : le (tf [T, F, F, E, T, T, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, T, F, E, F, E, T, F] [([T, F, F, E, T, T, E, F, T, F, E, T, F], [T, F, F, E, T, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_167 trivial)

theorem z_183 : le (tf [T, F, T, F, E, T, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, T, F, E, F, E, T, F] [([T, F, E, F, T, T, T, F, E, F, E, T, F], [T, F, F, E, T, T, T, F, E, F, E, T, F]), ([T, F, T, F, E, T, E, F, T, F, E, T, F], [T, F, T, F, E, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_182 (And.intro z_177 trivial))

theorem z_184 : le (tf [T, F, T, F, T, E, T, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, T, F, E, E, F, T, F] [([T, F, T, F, E, T, T, F, E, E, F, T, F], [T, F, T, F, E, T, T, F, E, F, E, T, F]), ([T, F, T, F, T, E, E, F, T, E, F, T, F], [T, F, T, F, T, E, E, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_183 (And.intro z_180 trivial))

theorem z_185 : le (tf [T, F, T, E, T, F, T, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, T, F, E, T, F, E, F] [([T, F, E, T, T, F, T, F, E, T, F, E, F], [T, F, E, T, T, F, T, F, F, T, E, E, F]), ([T, F, T, E, T, F, E, F, T, T, F, E, F], [T, F, T, F, T, E, E, F, T, T, F, E, F]), ([T, F, T, E, T, F, T, F, E, E, F, T, F], [T, F, T, F, T, E, T, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_153 (And.intro z_181 (And.intro z_184 trivial)))

theorem z_186 : le (tf [T, E, T, F, T, F, T, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, F, T, F, T, E, F, E, F] [([E, T, T, F, T, F, T, F, T, E, F, E, F], [E, T, T, F, T, F, T, F, T, F, E, E, F]), ([T, E, T, F, T, F, T, F, E, T, F, E, F], [T, F, T, E, T, F, T, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_147 (And.intro z_185 trivial))

theorem z_187 : le (tf [F, E, T, T, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, T, T, F, F, E, F] [([F, E, T, T, E, F, T, T, T, F, F, E, F], [F, E, T, T, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_138 trivial)

theorem z_188 : le (tf [T, F, E, T, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, T, T, F, F, E, F] [([E, F, T, T, T, F, E, T, T, F, F, E, F], [F, E, T, T, T, F, E, T, T, F, F, E, F]), ([T, F, E, T, E, F, T, T, T, F, F, E, F], [T, F, E, T, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_187 (And.intro z_140 trivial))

theorem z_189 : le (tf [T, T, F, E, F, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, T, T, F, F, E, F] [([T, E, F, T, F, E, T, T, T, F, F, E, F], [T, F, E, T, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_140 trivial)

theorem z_190 : le (tf [T, T, F, E, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, T, T, F, F, E, F] [([T, E, F, T, T, F, E, T, T, F, F, E, F], [T, F, E, T, T, F, E, T, T, F, F, E, F]), ([T, T, F, E, E, F, T, T, T, F, F, E, F], [T, T, F, E, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_188 (And.intro z_189 trivial))

theorem z_191 : le (tf [T, T, E, F, T, F, T, E, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, F, T, E, T, F, F, E, F] [([T, E, T, F, T, F, T, E, T, F, F, E, F], [T, E, T, F, T, F, T, F, T, E, F, E, F]), ([T, T, E, F, T, F, E, T, T, F, F, E, F], [T, T, F, E, T, F, E, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_186 (And.intro z_190 trivial))

theorem z_192 : le (tf [T, T, E, F, T, T, E, F, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, T, E, F, T, F, F, E, F] [([T, E, T, F, T, T, E, F, T, F, F, E, F], [T, E, T, F, T, T, F, E, T, F, F, E, F]), ([T, T, E, F, T, E, T, F, T, F, F, E, F], [T, T, E, F, T, F, T, E, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_143 (And.intro z_191 trivial))

theorem z_193 : le (tf [T, T, E, F, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, T, T, F, E, F, E, F, F] [([T, E, T, F, T, T, T, F, E, F, E, F, F], [T, E, T, F, T, T, T, F, F, E, E, F, F]), ([T, T, E, F, T, T, E, F, T, F, E, F, F], [T, T, E, F, T, T, E, F, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_129 (And.intro z_192 trivial))

theorem z_194 : le (tf [T, T, T, F, F, T, F, F, F, E, E, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_195 : le (tf [T, T, T, F, F, T, F, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, F, E, T, E] [([T, T, T, F, F, T, F, F, E, F, E, E, T], [T, T, T, F, F, T, F, F, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_194 trivial)

theorem z_196 : le (tf [T, T, T, F, F, T, F, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, T, F, E, E] [([T, T, T, F, F, T, F, F, E, E, F, T, E], [T, T, T, F, F, T, F, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_195 trivial)

theorem z_197 : le (tf [T, T, T, F, F, T, F, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, T, E, E, F, E] [([T, T, T, F, F, T, F, F, E, T, E, F, E], [T, T, T, F, F, T, F, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_196 trivial)

theorem z_198 : le (tf [T, T, T, F, F, T, F, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_199 : le (tf [T, T, T, F, F, T, F, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, E, F, T, E] [([T, T, T, F, F, T, F, F, E, E, F, E, T], [T, T, T, F, F, T, F, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_198 trivial)

theorem z_200 : le (tf [T, T, T, F, F, T, F, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_201 : le (tf [T, T, T, F, F, T, F, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, E, T, F, E] [([T, T, T, F, F, T, F, F, E, E, E, F, T], [T, T, T, F, F, T, F, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_200 trivial)

theorem z_202 : le (tf [T, T, T, F, F, T, F, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, T, E, E, F] [([T, T, T, F, F, T, F, F, E, E, T, E, F], [T, T, T, F, F, T, F, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_201 trivial)

theorem z_203 : le (tf [T, T, T, F, F, E, F, T, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, T, F, E, E, F] [([T, T, T, F, F, E, F, T, E, F, T, E, F], [T, T, T, F, F, F, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 trivial)

theorem z_204 : le (tf [T, T, T, F, F, T, F, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, F, E, E, T, F] [([T, T, T, F, F, E, F, T, F, E, E, T, F], [T, T, T, F, F, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_72 trivial)

theorem z_205 : le (tf [T, T, T, F, F, T, F, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, E, F, T, E, F] [([T, T, T, F, F, E, F, T, E, F, T, E, F], [T, T, T, F, F, F, E, T, E, F, T, E, F]), ([T, T, T, F, F, T, F, E, E, F, E, T, F], [T, T, T, F, F, T, F, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 (And.intro z_204 trivial))

theorem z_206 : le (tf [T, T, T, F, F, E, F, T, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, T, E, F, E, F] [([T, T, T, F, F, E, F, T, E, T, F, E, F], [T, T, T, F, F, F, E, T, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 trivial)

theorem z_207 : le (tf [T, T, T, F, F, T, F, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, E, F, E, T, F] [([T, T, T, F, F, E, F, T, E, F, E, T, F], [T, T, T, F, F, F, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 trivial)

theorem z_208 : le (tf [T, T, T, F, F, T, F, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, E, T, F, E, F] [([T, T, T, F, F, E, F, T, E, T, F, E, F], [T, T, T, F, F, F, E, T, E, T, F, E, F]), ([T, T, T, F, F, T, F, E, E, E, F, T, F], [T, T, T, F, F, T, F, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_207 trivial))

theorem z_209 : le (tf [T, T, T, F, F, F, E, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, T, T, F, E, F] [([T, T, T, F, F, F, E, E, T, E, F, T, F], [T, T, T, F, F, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 trivial)

theorem z_210 : le (tf [T, T, T, F, F, F, E, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, E, T, E, F, F] [([T, T, T, F, F, F, E, E, T, T, E, F, F], [T, T, T, F, F, F, E, E, T, T, F, E, F]), ([T, T, T, F, F, F, E, T, E, E, T, F, F], [T, T, T, F, F, F, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_209 (And.intro z_93 trivial))

theorem z_211 : le (tf [T, T, T, F, F, E, F, T, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, T, E, E, F, F] [([T, T, T, F, F, E, F, T, E, T, E, F, F], [T, T, T, F, F, F, E, T, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_210 trivial)

theorem z_212 : le (tf [T, T, T, F, F, T, F, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, E, T, E, F, F] [([T, T, T, F, F, E, F, T, E, T, E, F, F], [T, T, T, F, F, F, E, T, E, T, E, F, F]), ([T, T, T, F, F, T, F, E, E, E, T, F, F], [T, T, T, F, F, T, F, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_210 (And.intro z_205 trivial))

theorem z_213 : le (tf [T, T, T, F, F, F, E, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, T, F, T, E, F] [([T, T, T, F, F, F, E, E, T, F, E, T, F], [T, T, T, F, F, F, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 trivial)

theorem z_214 : le (tf [T, T, T, F, F, F, E, T, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, E, E, T, F, F] [([T, T, T, F, F, F, E, E, T, E, T, F, F], [T, T, T, F, F, F, E, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_213 trivial)

theorem z_215 : le (tf [T, T, T, F, F, T, F, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, E, E, T, F, F] [([T, T, T, F, F, E, F, T, E, E, T, F, F], [T, T, T, F, F, F, E, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_214 trivial)

theorem z_216 : le (tf [T, T, T, F, F, T, E, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, E, F, E, T, E, F, F] [([T, T, T, F, F, E, T, F, E, T, E, F, F], [T, T, T, F, F, F, T, E, E, T, E, F, F]), ([T, T, T, F, F, T, E, F, E, E, T, F, F], [T, T, T, F, F, T, F, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 (And.intro z_215 trivial))

theorem z_217 : le (tf [T, T, T, F, F, T, E, E, E, F, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, E, E, E, F, T, F, F] [([T, T, T, F, F, E, T, E, E, F, T, F, F], [T, T, T, F, F, E, T, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 trivial)

theorem z_218 : le (tf [F, E, T, T, T, T, F, F, T, F, F, E, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, T, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_219 : le (tf [T, F, E, T, T, T, F, F, T, F, F, E, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, T, F, F, E, E] [([E, F, T, T, T, T, F, F, T, F, F, E, E], [F, E, T, T, T, T, F, F, T, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_218 trivial)

theorem z_220 : le (tf [T, T, F, E, T, T, F, F, T, F, F, E, E]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, T, F, F, E, E] [([T, E, F, T, T, T, F, F, T, F, F, E, E], [T, F, E, T, T, T, F, F, T, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_219 trivial)

theorem z_221 : le (tf [E, F, T, T, T, T, F, F, T, F, F, E, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, T, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_222 : le (tf [E, T, F, T, T, T, F, F, T, F, F, E, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, F, T, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_223 : le (tf [F, E, T, T, T, T, F, F, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, F, E, E, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_224 : le (tf [F, E, T, T, T, T, F, F, E, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, E, F, T, F, E] [([F, E, T, T, T, T, F, F, E, F, E, F, T], [F, E, T, T, T, T, F, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 trivial)

theorem z_225 : le (tf [T, F, E, T, T, T, F, F, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, F, E, E, F, T] [([E, F, T, T, T, T, F, F, F, E, E, F, T], [F, E, T, T, T, T, F, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 trivial)

theorem z_226 : le (tf [T, F, E, T, T, T, F, F, E, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, E, F, T, F, E] [([E, F, T, T, T, T, F, F, E, F, T, F, E], [F, E, T, T, T, T, F, F, E, F, T, F, E]), ([T, F, E, T, T, T, F, F, E, F, E, F, T], [T, F, E, T, T, T, F, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_224 (And.intro z_225 trivial))

theorem z_227 : le (tf [T, E, F, T, T, T, F, F, T, F, E, F, E]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, F, T, F, E, F, E] [([E, T, F, T, T, T, F, F, T, F, E, F, E], [E, T, F, T, T, T, F, F, T, F, F, E, E]), ([T, E, F, T, T, T, F, F, E, F, T, F, E], [T, F, E, T, T, T, F, F, E, F, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_222 (And.intro z_226 trivial))

theorem z_228 : le (tf [T, T, F, E, T, T, F, F, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, F, E, E, F, T] [([T, E, F, T, T, T, F, F, F, E, E, F, T], [T, F, E, T, T, T, F, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_225 trivial)

theorem z_229 : le (tf [T, T, F, E, T, T, F, F, E, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, E, F, T, F, E] [([T, E, F, T, T, T, F, F, E, F, T, F, E], [T, F, E, T, T, T, F, F, E, F, T, F, E]), ([T, T, F, E, T, T, F, F, E, F, E, F, T], [T, T, F, E, T, T, F, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_226 (And.intro z_228 trivial))

theorem z_230 : le (tf [F, E, T, T, T, T, F, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, F, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_231 : le (tf [F, E, T, T, T, T, F, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, F, E, T, F, E] [([F, E, T, T, T, T, F, F, F, E, E, F, T], [F, E, T, T, T, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_230 trivial)

theorem z_232 : le (tf [F, E, T, T, T, T, F, F, T, F, E, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, T, F, E, F, E] [([F, E, T, T, T, T, F, F, E, F, T, F, E], [F, E, T, T, T, T, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 trivial)

theorem z_233 : le (tf [F, T, E, T, T, T, F, F, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, F, E, E, F, T] [([F, E, T, T, T, T, F, F, F, E, E, F, T], [F, E, T, T, T, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_230 trivial)

theorem z_234 : le (tf [F, T, E, T, T, T, F, F, E, F, T, F, E]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, E, F, T, F, E] [([F, E, T, T, T, T, F, F, E, F, T, F, E], [F, E, T, T, T, T, F, F, F, E, T, F, E]), ([F, T, E, T, T, T, F, F, E, F, E, F, T], [F, T, E, T, T, T, F, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 (And.intro z_233 trivial))

theorem z_235 : le (tf [F, T, E, T, T, T, F, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, T, F, E, E, F] [([F, E, T, T, T, T, F, F, T, F, E, E, F], [F, E, T, T, T, T, F, F, T, F, E, F, E]), ([F, T, E, T, T, T, F, F, E, F, T, E, F], [F, T, E, T, T, T, F, F, E, F, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_232 (And.intro z_234 trivial))

theorem z_236 : le (tf [F, E, T, T, T, T, F, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_237 : le (tf [F, E, T, T, T, T, F, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, E, F, T, E, F] [([F, E, T, T, T, T, F, F, E, F, E, T, F], [F, E, T, T, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_236 trivial)

theorem z_238 : le (tf [T, F, E, T, T, T, F, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, F, E, E, T, F] [([E, F, T, T, T, T, F, F, F, E, E, T, F], [F, E, T, T, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_236 trivial)

theorem z_239 : le (tf [T, F, E, T, T, T, F, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, E, F, T, E, F] [([E, F, T, T, T, T, F, F, E, F, T, E, F], [F, E, T, T, T, T, F, F, E, F, T, E, F]), ([T, F, E, T, T, T, F, F, E, F, E, T, F], [T, F, E, T, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_237 (And.intro z_238 trivial))

theorem z_240 : le (tf [T, E, F, T, T, T, F, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, F, T, F, E, E, F] [([E, T, F, T, T, T, F, F, T, F, E, E, F], [F, T, E, T, T, T, F, F, T, F, E, E, F]), ([T, E, F, T, T, T, F, F, E, F, T, E, F], [T, F, E, T, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_235 (And.intro z_239 trivial))

theorem z_241 : le (tf [T, T, F, E, T, T, F, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, F, E, E, T, F] [([T, E, F, T, T, T, F, F, F, E, E, T, F], [T, F, E, T, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_238 trivial)

theorem z_242 : le (tf [T, T, F, E, T, T, F, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, E, F, T, E, F] [([T, E, F, T, T, T, F, F, E, F, T, E, F], [T, F, E, T, T, T, F, F, E, F, T, E, F]), ([T, T, F, E, T, T, F, F, E, F, E, T, F], [T, T, F, E, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_239 (And.intro z_241 trivial))

theorem z_243 : le (tf [F, E, T, T, T, T, F, F, F, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, F, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_244 : le (tf [F, E, T, T, T, T, F, F, F, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, F, E, F, T, E] [([F, E, T, T, T, T, F, F, F, E, F, E, T], [F, E, T, T, T, T, F, F, F, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_243 trivial)

theorem z_245 : le (tf [F, T, E, T, T, T, F, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, F, E, E, T, F] [([F, E, T, T, T, T, F, F, F, E, E, T, F], [F, E, T, T, T, T, F, F, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_244 trivial)

theorem z_246 : le (tf [F, T, E, T, T, T, F, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, E, F, T, E, F] [([F, E, T, T, T, T, F, F, E, F, T, E, F], [F, E, T, T, T, T, F, F, E, F, T, F, E]), ([F, T, E, T, T, T, F, F, E, F, E, T, F], [F, T, E, T, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_224 (And.intro z_245 trivial))

theorem z_247 : le (tf [E, T, F, T, T, T, F, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, F, T, F, E, E, F] [([E, T, F, T, T, T, F, F, E, F, T, E, F], [F, T, E, T, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_246 trivial)

theorem z_248 : le (tf [F, E, T, T, T, T, F, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, E, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_249 : le (tf [F, E, T, T, T, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, E, T, F, E, F] [([F, E, T, T, T, T, F, F, E, E, F, T, F], [F, E, T, T, T, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 trivial)

theorem z_250 : le (tf [T, F, E, T, T, T, F, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, E, F, E, T, F] [([E, F, T, T, T, T, F, F, E, F, E, T, F], [F, E, T, T, T, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 trivial)

theorem z_251 : le (tf [T, F, E, T, T, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, E, T, F, E, F] [([E, F, T, T, T, T, F, F, E, T, F, E, F], [F, E, T, T, T, T, F, F, E, T, F, E, F]), ([T, F, E, T, T, T, F, F, E, E, F, T, F], [T, F, E, T, T, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 (And.intro z_250 trivial))

theorem z_252 : le (tf [T, E, F, T, T, T, F, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, F, T, E, F, E, F] [([E, T, F, T, T, T, F, F, T, E, F, E, F], [E, T, F, T, T, T, F, F, T, F, E, E, F]), ([T, E, F, T, T, T, F, F, E, T, F, E, F], [T, F, E, T, T, T, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_247 (And.intro z_251 trivial))

theorem z_253 : le (tf [T, T, F, E, T, T, F, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, E, F, E, T, F] [([T, E, F, T, T, T, F, F, E, F, E, T, F], [T, F, E, T, T, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_250 trivial)

theorem z_254 : le (tf [T, T, F, E, T, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, E, T, F, E, F] [([T, E, F, T, T, T, F, F, E, T, F, E, F], [T, F, E, T, T, T, F, F, E, T, F, E, F]), ([T, T, F, E, T, T, F, F, E, E, F, T, F], [T, T, F, E, T, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_251 (And.intro z_253 trivial))

theorem z_255 : le (tf [F, E, T, T, T, T, F, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, F, T, E, E, F] [([F, E, T, T, T, T, F, F, F, E, T, E, F], [F, E, T, T, T, T, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 trivial)

theorem z_256 : le (tf [F, E, T, T, T, T, F, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, T, E, F, E, F] [([F, E, T, T, T, T, F, F, E, T, F, E, F], [F, E, T, T, T, T, F, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_255 trivial)

theorem z_257 : le (tf [F, T, E, T, T, T, F, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, E, F, E, T, F] [([F, E, T, T, T, T, F, F, E, F, E, T, F], [F, E, T, T, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_236 trivial)

theorem z_258 : le (tf [F, T, E, T, T, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, E, T, F, E, F] [([F, E, T, T, T, T, F, F, E, T, F, E, F], [F, E, T, T, T, T, F, F, F, T, E, E, F]), ([F, T, E, T, T, T, F, F, E, E, F, T, F], [F, T, E, T, T, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_255 (And.intro z_257 trivial))

theorem z_259 : le (tf [F, T, E, T, T, T, F, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, T, E, E, F, F] [([F, E, T, T, T, T, F, F, T, E, E, F, F], [F, E, T, T, T, T, F, F, T, E, F, E, F]), ([F, T, E, T, T, T, F, F, E, T, E, F, F], [F, T, E, T, T, T, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_256 (And.intro z_258 trivial))

theorem z_260 : le (tf [F, E, T, T, T, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, E, T, E, F, F] [([F, E, T, T, T, T, F, F, E, E, T, F, F], [F, E, T, T, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_237 trivial)

theorem z_261 : le (tf [T, F, E, T, T, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, E, T, E, F, F] [([E, F, T, T, T, T, F, F, E, T, E, F, F], [F, E, T, T, T, T, F, F, E, T, E, F, F]), ([T, F, E, T, T, T, F, F, E, E, T, F, F], [T, F, E, T, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 (And.intro z_239 trivial))

theorem z_262 : le (tf [T, E, F, T, T, T, F, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, F, T, E, E, F, F] [([E, T, F, T, T, T, F, F, T, E, E, F, F], [F, T, E, T, T, T, F, F, T, E, E, F, F]), ([T, E, F, T, T, T, F, F, E, T, E, F, F], [T, F, E, T, T, T, F, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_259 (And.intro z_261 trivial))

theorem z_263 : le (tf [T, T, F, E, T, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, E, T, E, F, F] [([T, E, F, T, T, T, F, F, E, T, E, F, F], [T, F, E, T, T, T, F, F, E, T, E, F, F]), ([T, T, F, E, T, T, F, F, E, E, T, F, F], [T, T, F, E, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_261 (And.intro z_242 trivial))

theorem z_264 : le (tf [E, F, T, T, T, T, F, F, T, F, E, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, T, F, E, F, E] [([E, F, T, T, T, T, F, F, E, F, T, F, E], [F, E, T, T, T, T, F, F, E, F, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_224 trivial)

theorem z_265 : le (tf [E, F, T, T, T, T, F, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, T, F, E, E, F] [([E, F, T, T, T, T, F, F, E, F, T, E, F], [F, E, T, T, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_237 trivial)

theorem z_266 : le (tf [E, F, T, T, T, T, F, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, T, E, F, E, F] [([E, F, T, T, T, T, F, F, E, T, F, E, F], [F, E, T, T, T, T, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 trivial)

theorem z_267 : le (tf [E, F, T, T, T, T, F, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, T, E, E, F, F] [([E, F, T, T, T, T, F, F, E, T, E, F, F], [F, E, T, T, T, T, F, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 trivial)

theorem z_268 : le (tf [F, F, E, E, F, E, T, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, T, T, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_269 : le (tf [F, F, E, E, T, F, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, E, T, T, T, T, F, F] [([F, F, E, E, E, F, T, T, T, T, T, F, F], [F, F, E, E, F, E, T, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_268 trivial)

theorem z_270 : le (tf [F, F, E, E, T, T, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, F, E, T, T, T, F, F] [([F, F, E, E, T, E, F, T, T, T, T, F, F], [F, F, E, E, T, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 trivial)

theorem z_271 : le (tf [F, F, E, E, T, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, E, T, T, F, F] [([F, F, E, E, T, T, E, F, T, T, T, F, F], [F, F, E, E, T, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 trivial)

theorem z_272 : le (tf [F, F, E, E, T, T, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, T, F, E, T, F, F] [([F, F, E, E, T, T, T, E, F, T, T, F, F], [F, F, E, E, T, T, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_271 trivial)

theorem z_273 : le (tf [F, F, E, T, E, E, F, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, T, E, E, F, T, T, T, T, F, F] [([F, F, E, E, T, E, F, T, T, T, T, F, F], [F, F, E, E, T, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 trivial)

theorem z_274 : le (tf [F, E, F, T, E, T, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, F, E, T, T, T, F, F] [([F, E, F, E, T, T, F, E, T, T, T, F, F], [F, F, E, E, T, T, F, E, T, T, T, F, F]), ([F, E, F, T, E, E, F, T, T, T, T, F, F], [F, F, E, T, E, E, F, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 (And.intro z_273 trivial))

theorem z_275 : le (tf [F, E, F, T, E, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, F, E, T, T, F, F] [([F, E, F, E, T, T, T, F, E, T, T, F, F], [F, F, E, E, T, T, T, F, E, T, T, F, F]), ([F, E, F, T, E, T, E, F, T, T, T, F, F], [F, E, F, T, E, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_271 (And.intro z_274 trivial))

theorem z_276 : le (tf [F, E, F, T, E, T, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, F, E, T, F, F] [([F, E, F, E, T, T, T, T, F, E, T, F, F], [F, F, E, E, T, T, T, T, F, E, T, F, F]), ([F, E, F, T, E, T, T, E, F, T, T, F, F], [F, E, F, T, E, T, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_272 (And.intro z_275 trivial))

theorem z_277 : le (tf [F, E, F, T, E, T, T, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, T, F, E, F, F] [([F, E, F, E, T, T, T, T, T, F, E, F, F], [F, E, F, E, T, T, T, T, T, F, F, E, F]), ([F, E, F, T, E, T, T, T, E, F, T, F, F], [F, E, F, T, E, T, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_136 (And.intro z_276 trivial))

theorem z_278 : le (tf [F, E, F, E, T, F, T, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, F, T, E, T, T, T, F, F] [([F, E, F, E, T, F, E, T, T, T, T, F, F], [F, F, E, E, T, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 trivial)

theorem z_279 : le (tf [F, E, F, E, T, T, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, E, F, T, T, T, F, F] [([F, E, F, E, T, E, T, F, T, T, T, F, F], [F, E, F, E, T, F, T, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_278 trivial)

theorem z_280 : le (tf [F, F, F, E, E, E, T, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, T, T, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_281 : le (tf [F, F, E, F, E, T, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, E, T, T, T, T, F, F] [([F, F, E, F, E, E, T, T, T, T, T, F, F], [F, F, F, E, E, E, T, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_280 trivial)

theorem z_282 : le (tf [F, F, E, T, F, E, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, E, T, T, T, T, F, F] [([F, F, E, E, F, T, E, T, T, T, T, F, F], [F, F, E, F, E, T, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_281 trivial)

theorem z_283 : le (tf [F, F, T, E, E, F, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, E, T, T, T, T, F, F] [([F, F, E, T, E, F, E, T, T, T, T, F, F], [F, F, E, T, F, E, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_282 trivial)

theorem z_284 : le (tf [F, E, T, F, E, F, T, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, F, T, E, T, T, T, F, F] [([F, E, E, F, T, F, T, E, T, T, T, F, F], [F, E, F, E, T, F, T, E, T, T, T, F, F]), ([F, E, T, F, E, F, E, T, T, T, T, F, F], [F, F, T, E, E, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_278 (And.intro z_283 trivial))

theorem z_285 : le (tf [F, E, T, F, E, T, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, E, F, T, T, T, F, F] [([F, E, E, F, T, T, E, F, T, T, T, F, F], [F, E, F, E, T, T, E, F, T, T, T, F, F]), ([F, E, T, F, E, E, T, F, T, T, T, F, F], [F, E, T, F, E, F, T, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_279 (And.intro z_284 trivial))

theorem z_286 : le (tf [F, E, T, E, F, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, F, E, T, T, F, F] [([F, E, E, T, F, T, T, F, E, T, T, F, F], [F, E, F, T, E, T, T, F, E, T, T, F, F]), ([F, E, T, E, F, T, E, F, T, T, T, F, F], [F, E, T, F, E, T, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_275 (And.intro z_285 trivial))

theorem z_287 : le (tf [F, E, T, E, F, T, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, F, E, T, F, F] [([F, E, E, T, F, T, T, T, F, E, T, F, F], [F, E, F, T, E, T, T, T, F, E, T, F, F]), ([F, E, T, E, F, T, T, E, F, T, T, F, F], [F, E, T, E, F, T, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_276 (And.intro z_286 trivial))

theorem z_288 : le (tf [F, E, T, E, F, T, T, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, T, F, E, F, F] [([F, E, E, T, F, T, T, T, T, F, E, F, F], [F, E, F, T, E, T, T, T, T, F, E, F, F]), ([F, E, T, E, F, T, T, T, E, F, T, F, F], [F, E, T, E, F, T, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_277 (And.intro z_287 trivial))

theorem z_289 : le (tf [F, E, T, T, F, E, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, E, F, T, T, T, F, F] [([F, E, T, E, F, T, E, F, T, T, T, F, F], [F, E, T, F, E, T, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_285 trivial)

theorem z_290 : le (tf [E, F, T, T, F, E, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, F, E, T, T, F, F] [([E, F, T, E, F, T, T, F, E, T, T, F, F], [F, E, T, E, F, T, T, F, E, T, T, F, F]), ([E, F, T, T, F, E, E, F, T, T, T, F, F], [F, E, T, T, F, E, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_286 (And.intro z_289 trivial))

theorem z_291 : le (tf [E, F, T, T, F, E, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, F, E, T, F, F] [([E, F, T, E, F, T, T, T, F, E, T, F, F], [F, E, T, E, F, T, T, T, F, E, T, F, F]), ([E, F, T, T, F, E, T, E, F, T, T, F, F], [E, F, T, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_287 (And.intro z_290 trivial))

theorem z_292 : le (tf [E, F, T, T, F, E, T, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, T, F, E, F, F] [([E, F, T, E, F, T, T, T, T, F, E, F, F], [F, E, T, E, F, T, T, T, T, F, E, F, F]), ([E, F, T, T, F, E, T, T, E, F, T, F, F], [E, F, T, T, F, E, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_288 (And.intro z_291 trivial))

theorem z_293 : le (tf [E, F, T, T, T, F, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, E, F, E, T, T, F, F] [([E, F, T, T, E, F, T, F, E, T, T, F, F], [E, F, T, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_290 trivial)

theorem z_294 : le (tf [E, F, T, T, T, F, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, E, T, F, E, T, F, F] [([E, F, T, T, E, F, T, T, F, E, T, F, F], [E, F, T, T, F, E, T, T, F, E, T, F, F]), ([E, F, T, T, T, F, E, E, F, T, T, F, F], [E, F, T, T, T, F, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_291 (And.intro z_293 trivial))

theorem z_295 : le (tf [E, F, T, T, T, F, E, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, E, T, T, F, E, F, F] [([E, F, T, T, E, F, T, T, T, F, E, F, F], [E, F, T, T, F, E, T, T, T, F, E, F, F]), ([E, F, T, T, T, F, E, T, E, F, T, F, F], [E, F, T, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_292 (And.intro z_294 trivial))

theorem z_296 : le (tf [E, F, T, T, T, T, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, E, F, E, T, F, F] [([E, F, T, T, T, E, F, T, F, E, T, F, F], [E, F, T, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_294 trivial)

theorem z_297 : le (tf [E, F, T, T, T, T, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, E, T, F, E, F, F] [([E, F, T, T, T, E, F, T, T, F, E, F, F], [E, F, T, T, T, F, E, T, T, F, E, F, F]), ([E, F, T, T, T, T, F, E, E, F, T, F, F], [E, F, T, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_295 (And.intro z_296 trivial))

theorem z_298 : le (tf [F, E, F, E, T, T, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, T, F, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_299 : le (tf [F, E, T, F, E, T, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, T, F, F, F, E] [([F, E, E, F, T, T, T, T, T, F, F, F, E], [F, E, F, E, T, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_298 trivial)

theorem z_300 : le (tf [F, E, T, T, F, E, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, T, F, F, F, E] [([F, E, T, E, F, T, T, T, T, F, F, F, E], [F, E, T, F, E, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_299 trivial)

theorem z_301 : le (tf [F, E, T, T, T, F, E, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, T, T, F, F, F, E] [([F, E, T, T, E, F, T, T, T, F, F, F, E], [F, E, T, T, F, E, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_300 trivial)

theorem z_302 : le (tf [T, F, E, F, E, T, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, T, F, F, F, E] [([E, F, T, F, E, T, T, T, T, F, F, F, E], [F, E, T, F, E, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_299 trivial)

theorem z_303 : le (tf [T, F, E, T, F, E, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, T, F, F, F, E] [([E, F, T, T, F, E, T, T, T, F, F, F, E], [F, E, T, T, F, E, T, T, T, F, F, F, E]), ([T, F, E, E, F, T, T, T, T, F, F, F, E], [T, F, E, F, E, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_300 (And.intro z_302 trivial))

theorem z_304 : le (tf [T, F, E, T, T, F, E, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, T, T, F, F, F, E] [([E, F, T, T, T, F, E, T, T, F, F, F, E], [F, E, T, T, T, F, E, T, T, F, F, F, E]), ([T, F, E, T, E, F, T, T, T, F, F, F, E], [T, F, E, T, F, E, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_301 (And.intro z_303 trivial))

theorem z_305 : le (tf [F, F, E, E, T, T, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, T, T, F, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_306 : le (tf [F, E, F, T, E, T, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, T, F, F, F, E] [([F, E, F, E, T, T, T, T, T, F, F, F, E], [F, F, E, E, T, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_305 trivial)

theorem z_307 : le (tf [F, E, T, E, F, T, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, T, F, F, F, E] [([F, E, E, T, F, T, T, T, T, F, F, F, E], [F, E, F, T, E, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_306 trivial)

theorem z_308 : le (tf [E, F, T, T, F, E, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, T, F, F, F, E] [([E, F, T, E, F, T, T, T, T, F, F, F, E], [F, E, T, E, F, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_307 trivial)

theorem z_309 : le (tf [E, F, T, T, T, F, E, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, E, T, T, F, F, F, E] [([E, F, T, T, E, F, T, T, T, F, F, F, E], [E, F, T, T, F, E, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_308 trivial)

theorem z_310 : le (tf [T, F, E, E, F, T, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, T, F, F, F, E] [([E, F, T, E, F, T, T, T, T, F, F, F, E], [F, E, T, E, F, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_307 trivial)

theorem z_311 : le (tf [F, E, T, F, T, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, E, T, T, T, F, F, E, F] [([F, E, T, F, E, T, T, T, T, F, F, E, F], [F, E, T, F, E, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_299 trivial)

theorem z_312 : le (tf [F, E, T, T, E, F, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, E, F, T, T, T, F, F, E, F] [([F, E, T, E, T, F, T, T, T, F, F, E, F], [F, E, T, F, T, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_311 trivial)

theorem z_313 : le (tf [E, F, T, T, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, E, T, T, F, F, E, F] [([E, F, T, T, E, F, T, T, T, F, F, E, F], [F, E, T, T, E, F, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_312 trivial)

theorem z_314 : le (tf [T, F, E, F, T, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, E, T, T, T, F, F, E, F] [([E, F, T, F, T, E, T, T, T, F, F, E, F], [F, E, T, F, T, E, T, T, T, F, F, E, F]), ([T, F, E, F, E, T, T, T, T, F, F, E, F], [T, F, E, F, E, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_311 (And.intro z_302 trivial))

theorem z_315 : le (tf [T, F, E, T, E, F, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, E, F, T, T, T, F, F, E, F] [([E, F, T, T, E, F, T, T, T, F, F, E, F], [F, E, T, T, E, F, T, T, T, F, F, E, F]), ([T, F, E, E, T, F, T, T, T, F, F, E, F], [T, F, E, F, T, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_312 (And.intro z_314 trivial))

theorem z_316 : le (tf [F, E, F, T, E, T, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, T, F, F, E, F] [([F, E, F, E, T, T, T, T, T, F, F, E, F], [F, E, F, E, T, T, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_298 trivial)

theorem z_317 : le (tf [F, E, T, E, F, T, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, T, F, F, E, F] [([F, E, E, T, F, T, T, T, T, F, F, E, F], [F, E, F, T, E, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_316 trivial)

theorem z_318 : le (tf [E, F, T, T, F, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, T, F, F, E, F] [([E, F, T, E, F, T, T, T, T, F, F, E, F], [F, E, T, E, F, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 trivial)

theorem z_319 : le (tf [T, F, E, E, F, T, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, T, F, F, E, F] [([E, F, T, E, F, T, T, T, T, F, F, E, F], [F, E, T, E, F, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 trivial)

theorem z_320 : le (tf [F, E, F, E, T, T, F, T, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, F, T, E, T, T, F, F] [([F, E, F, E, T, T, F, E, T, T, T, F, F], [F, F, E, E, T, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 trivial)

theorem z_321 : le (tf [F, E, F, E, T, T, T, E, F, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, E, F, T, T, F, F] [([F, E, F, E, T, T, E, T, F, T, T, F, F], [F, E, F, E, T, T, F, T, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_320 trivial)

theorem z_322 : le (tf [F, E, E, F, T, T, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, E, F, T, T, T, T, F, E, T, F, F] [([F, E, E, F, T, T, T, E, F, T, T, F, F], [F, E, F, E, T, T, T, E, F, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_321 trivial)

theorem z_323 : le (tf [F, E, E, F, T, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, E, F, T, T, T, F, E, T, T, F, F] [([F, E, E, F, T, T, E, F, T, T, T, F, F], [F, E, F, E, T, T, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_279 trivial)

theorem z_324 : le (tf [E, F, T, F, E, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, F, E, T, T, F, E, T, T, F, F] [([E, F, E, F, T, T, T, F, E, T, T, F, F], [F, E, E, F, T, T, T, F, E, T, T, F, F]), ([E, F, T, F, E, T, E, F, T, T, T, F, F], [F, E, T, F, E, T, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_323 (And.intro z_285 trivial))

theorem z_325 : le (tf [E, F, T, F, E, T, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, F, E, T, T, T, F, E, T, F, F] [([E, F, E, F, T, T, T, T, F, E, T, F, F], [F, E, E, F, T, T, T, T, F, E, T, F, F]), ([E, F, T, F, E, T, T, E, F, T, T, F, F], [E, F, T, F, E, T, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_322 (And.intro z_324 trivial))

theorem z_326 : le (tf [F, F, E, E, F, E, T, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, T, T, T, F, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_327 : le (tf [F, F, E, E, T, F, E, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, E, T, T, F, T, T, F] [([F, F, E, E, E, F, T, T, T, F, T, T, F], [F, F, E, E, F, E, T, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_326 trivial)

theorem z_328 : le (tf [F, F, E, E, T, T, F, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, F, E, T, F, T, T, F] [([F, F, E, E, T, E, F, T, T, F, T, T, F], [F, F, E, E, T, F, E, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 trivial)

theorem z_329 : le (tf [F, F, E, E, T, T, T, F, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, E, F, T, T, F] [([F, F, E, E, T, T, E, F, T, F, T, T, F], [F, F, E, E, T, T, F, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_328 trivial)

theorem z_330 : le (tf [F, E, F, E, T, T, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, T, F, E, T, F] [([F, E, F, E, T, T, T, F, E, F, T, T, F], [F, F, E, E, T, T, T, F, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_329 trivial)

theorem z_331 : le (tf [F, E, E, F, T, T, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, F, T, T, T, F, T, F, T, E, F] [([F, E, E, F, T, T, T, F, T, F, E, T, F], [F, E, F, E, T, T, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_330 trivial)

theorem z_332 : le (tf [F, E, F, E, T, T, T, F, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, F, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_333 : le (tf [F, E, T, F, E, T, T, F, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, F, E, T, T, F] [([F, E, E, F, T, T, T, F, F, E, T, T, F], [F, E, F, E, T, T, T, F, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_332 trivial)

theorem z_334 : le (tf [F, E, T, F, E, T, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, T, F, E, T, F] [([F, E, E, F, T, T, T, F, T, F, E, T, F], [F, E, F, E, T, T, T, F, T, F, E, T, F]), ([F, E, T, F, E, T, T, F, E, F, T, T, F], [F, E, T, F, E, T, T, F, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_330 (And.intro z_333 trivial))

theorem z_335 : le (tf [E, F, T, F, E, T, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, F, E, T, T, F, T, F, T, E, F] [([E, F, E, F, T, T, T, F, T, F, T, E, F], [F, E, E, F, T, T, T, F, T, F, T, E, F]), ([E, F, T, F, E, T, T, F, T, F, E, T, F], [F, E, T, F, E, T, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_331 (And.intro z_334 trivial))

theorem z_336 : le (tf [T, F, F, E, E, F, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, F, E, T, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_337 : le (tf [T, F, F, E, E, T, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, F, E, T, T, T, F, F] [([T, F, F, E, E, E, F, T, T, T, T, F, F], [T, F, F, E, E, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_336 trivial)

theorem z_338 : le (tf [T, F, F, E, E, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, E, T, T, F, F] [([T, F, F, E, E, T, E, F, T, T, T, F, F], [T, F, F, E, E, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_337 trivial)

theorem z_339 : le (tf [T, F, E, F, E, T, T, F, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, T, E, T, F, F] [([E, F, T, F, E, T, T, F, T, E, T, F, F], [E, F, T, F, E, T, T, F, T, F, T, E, F]), ([T, F, E, F, E, T, T, F, E, T, T, F, F], [T, F, F, E, E, T, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_335 (And.intro z_338 trivial))

theorem z_340 : le (tf [T, F, E, F, E, T, T, T, E, F, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, E, F, T, F, F] [([E, F, T, F, E, T, T, T, E, F, T, F, F], [E, F, T, F, E, T, T, T, F, E, T, F, F]), ([T, F, E, F, E, T, T, E, T, F, T, F, F], [T, F, E, F, E, T, T, F, T, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_325 (And.intro z_339 trivial))

theorem z_341 : le (tf [T, F, E, E, F, T, T, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, T, F, E, F, F] [([E, F, T, E, F, T, T, T, T, F, E, F, F], [F, E, T, E, F, T, T, T, T, F, E, F, F]), ([T, F, E, E, F, T, T, T, E, F, T, F, F], [T, F, E, F, E, T, T, T, E, F, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_288 (And.intro z_340 trivial))

theorem z_342 : le (tf [F, F, E, E, T, T, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, T, F, F, E, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_343 : le (tf [F, E, F, E, T, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, F, F, T, F, E] [([F, E, F, E, T, T, T, T, F, F, E, F, T], [F, F, E, E, T, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_342 trivial)

theorem z_344 : le (tf [F, E, F, E, T, T, T, T, F, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, F, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_345 : le (tf [F, E, T, F, E, T, T, T, F, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, F, F, F, E, T] [([F, E, E, F, T, T, T, T, F, F, F, E, T], [F, E, F, E, T, T, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 trivial)

theorem z_346 : le (tf [F, E, T, F, E, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, F, F, T, F, E] [([F, E, E, F, T, T, T, T, F, F, T, F, E], [F, E, F, E, T, T, T, T, F, F, T, F, E]), ([F, E, T, F, E, T, T, T, F, F, E, F, T], [F, E, T, F, E, T, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_345 trivial))

theorem z_347 : le (tf [F, E, T, T, F, E, T, T, F, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, F, F, E, T] [([F, E, T, E, F, T, T, T, F, F, F, E, T], [F, E, T, F, E, T, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_345 trivial)

theorem z_348 : le (tf [F, E, T, T, F, E, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, F, T, F, E] [([F, E, T, E, F, T, T, T, F, F, T, F, E], [F, E, T, F, E, T, T, T, F, F, T, F, E]), ([F, E, T, T, F, E, T, T, F, F, E, F, T], [F, E, T, T, F, E, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_346 (And.intro z_347 trivial))

theorem z_349 : le (tf [T, F, F, E, E, T, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, T, F, F, E, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_350 : le (tf [T, F, E, F, E, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, F, F, T, F, E] [([E, F, T, F, E, T, T, T, F, F, T, F, E], [F, E, T, F, E, T, T, T, F, F, T, F, E]), ([T, F, E, F, E, T, T, T, F, F, E, F, T], [T, F, F, E, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_346 (And.intro z_349 trivial))

theorem z_351 : le (tf [T, F, E, F, E, T, T, T, F, F, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, F, F, F, E, T] [([E, F, T, F, E, T, T, T, F, F, F, E, T], [F, E, T, F, E, T, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_345 trivial)

theorem z_352 : le (tf [T, F, E, T, F, E, T, T, F, F, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, F, F, E, T] [([E, F, T, T, F, E, T, T, F, F, F, E, T], [F, E, T, T, F, E, T, T, F, F, F, E, T]), ([T, F, E, E, F, T, T, T, F, F, F, E, T], [T, F, E, F, E, T, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_347 (And.intro z_351 trivial))

theorem z_353 : le (tf [T, F, E, T, F, E, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, F, T, F, E] [([E, F, T, T, F, E, T, T, F, F, T, F, E], [F, E, T, T, F, E, T, T, F, F, T, F, E]), ([T, F, E, E, F, T, T, T, F, F, T, F, E], [T, F, E, F, E, T, T, T, F, F, T, F, E]), ([T, F, E, T, F, E, T, T, F, F, E, F, T], [T, F, E, T, F, E, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_348 (And.intro z_350 (And.intro z_352 trivial)))

theorem z_354 : le (tf [F, F, E, E, T, T, T, T, F, F, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, T, F, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_355 : le (tf [F, F, E, E, T, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, T, F, F, T, F, E] [([F, F, E, E, T, T, T, T, F, F, E, F, T], [F, F, E, E, T, T, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_354 trivial)

theorem z_356 : le (tf [F, F, E, T, E, T, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, E, T, T, T, F, F, E, F, T] [([F, F, E, E, T, T, T, T, F, F, E, F, T], [F, F, E, E, T, T, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_354 trivial)

theorem z_357 : le (tf [F, E, F, T, E, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, F, F, T, F, E] [([F, E, F, E, T, T, T, T, F, F, T, F, E], [F, F, E, E, T, T, T, T, F, F, T, F, E]), ([F, E, F, T, E, T, T, T, F, F, E, F, T], [F, F, E, T, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_355 (And.intro z_356 trivial))

theorem z_358 : le (tf [F, E, F, E, T, T, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, F, F, E, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_359 : le (tf [F, E, T, F, E, T, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, F, F, E, F, T] [([F, E, E, F, T, T, T, T, F, F, E, F, T], [F, E, F, E, T, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_358 trivial)

theorem z_360 : le (tf [F, E, T, E, F, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, F, F, T, F, E] [([F, E, E, T, F, T, T, T, F, F, T, F, E], [F, E, F, T, E, T, T, T, F, F, T, F, E]), ([F, E, T, E, F, T, T, T, F, F, E, F, T], [F, E, T, F, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_357 (And.intro z_359 trivial))

theorem z_361 : le (tf [F, E, T, T, F, E, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, F, E, F, T] [([F, E, T, E, F, T, T, T, F, F, E, F, T], [F, E, T, F, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_359 trivial)

theorem z_362 : le (tf [E, F, T, T, F, E, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, F, F, T, F, E] [([E, F, T, E, F, T, T, T, F, F, T, F, E], [F, E, T, E, F, T, T, T, F, F, T, F, E]), ([E, F, T, T, F, E, T, T, F, F, E, F, T], [F, E, T, T, F, E, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_360 (And.intro z_361 trivial))

theorem z_363 : le (tf [T, F, E, F, E, T, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, F, F, E, F, T] [([E, F, T, F, E, T, T, T, F, F, E, F, T], [F, E, T, F, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_359 trivial)

theorem z_364 : le (tf [T, F, E, E, F, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, F, F, T, F, E] [([E, F, T, E, F, T, T, T, F, F, T, F, E], [F, E, T, E, F, T, T, T, F, F, T, F, E]), ([T, F, E, E, F, T, T, T, F, F, E, F, T], [T, F, E, F, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_360 (And.intro z_363 trivial))

theorem z_365 : le (tf [T, F, E, T, F, E, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, F, E, F, T] [([E, F, T, T, F, E, T, T, F, F, E, F, T], [F, E, T, T, F, E, T, T, F, F, E, F, T]), ([T, F, E, E, F, T, T, T, F, F, E, F, T], [T, F, E, F, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_361 (And.intro z_363 trivial))

theorem z_366 : le (tf [F, E, F, T, E, T, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, F, F, E, F, T] [([F, E, F, E, T, T, T, T, F, F, E, F, T], [F, F, E, E, T, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_342 trivial)

theorem z_367 : le (tf [F, E, E, T, F, T, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, F, T, T, T, F, F, T, F, E] [([F, E, E, T, F, T, T, T, F, F, E, F, T], [F, E, F, T, E, T, T, T, F, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_366 trivial)

theorem z_368 : le (tf [F, E, F, E, T, T, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, F, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_369 : le (tf [F, E, T, F, E, T, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, F, F, E, T, F] [([F, E, E, F, T, T, T, T, F, F, E, T, F], [F, E, F, E, T, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_368 trivial)

theorem z_370 : le (tf [F, E, T, E, F, T, T, T, F, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, F, F, T, E, F] [([F, E, E, T, F, T, T, T, F, F, T, E, F], [F, E, E, T, F, T, T, T, F, F, T, F, E]), ([F, E, T, E, F, T, T, T, F, F, E, T, F], [F, E, T, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_367 (And.intro z_369 trivial))

theorem z_371 : le (tf [F, E, T, T, F, E, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, F, E, T, F] [([F, E, T, E, F, T, T, T, F, F, E, T, F], [F, E, T, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_369 trivial)

theorem z_372 : le (tf [E, F, T, T, F, E, T, T, F, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, F, F, T, E, F] [([E, F, T, E, F, T, T, T, F, F, T, E, F], [F, E, T, E, F, T, T, T, F, F, T, E, F]), ([E, F, T, T, F, E, T, T, F, F, E, T, F], [F, E, T, T, F, E, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_370 (And.intro z_371 trivial))

theorem z_373 : le (tf [T, F, E, F, E, T, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, F, F, E, T, F] [([E, F, T, F, E, T, T, T, F, F, E, T, F], [F, E, T, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_369 trivial)

theorem z_374 : le (tf [T, F, E, E, F, T, T, T, F, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, F, F, T, E, F] [([E, F, T, E, F, T, T, T, F, F, T, E, F], [F, E, T, E, F, T, T, T, F, F, T, E, F]), ([T, F, E, E, F, T, T, T, F, F, E, T, F], [T, F, E, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_370 (And.intro z_373 trivial))

theorem z_375 : le (tf [T, F, E, T, F, E, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, F, E, T, F] [([E, F, T, T, F, E, T, T, F, F, E, T, F], [F, E, T, T, F, E, T, T, F, F, E, T, F]), ([T, F, E, E, F, T, T, T, F, F, E, T, F], [T, F, E, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_371 (And.intro z_373 trivial))

theorem z_376 : le (tf [T, F, F, E, E, E, T, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, E, T, F, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_377 : le (tf [T, F, E, F, E, T, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, E, F, T, T, T, F, F] [([E, F, T, F, E, T, E, F, T, T, T, F, F], [F, E, T, F, E, T, E, F, T, T, T, F, F]), ([T, F, E, F, E, E, T, F, T, T, T, F, F], [T, F, F, E, E, E, T, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_285 (And.intro z_376 trivial))

theorem z_378 : le (tf [T, F, E, E, F, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, F, E, T, T, F, F] [([E, F, T, E, F, T, T, F, E, T, T, F, F], [F, E, T, E, F, T, T, F, E, T, T, F, F]), ([T, F, E, E, F, T, E, F, T, T, T, F, F], [T, F, E, F, E, T, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_286 (And.intro z_377 trivial))

theorem z_379 : le (tf [T, F, E, E, F, T, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, F, E, T, F, F] [([E, F, T, E, F, T, T, T, F, E, T, F, F], [F, E, T, E, F, T, T, T, F, E, T, F, F]), ([T, F, E, E, F, T, T, E, F, T, T, F, F], [T, F, E, E, F, T, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_287 (And.intro z_378 trivial))

theorem z_380 : le (tf [F, F, E, F, E, E, T, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, E, T, T, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_381 : le (tf [F, F, E, E, F, T, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, F, T, E, T, T, T, T, F, F] [([F, F, E, E, F, E, T, T, T, T, T, F, F], [F, F, E, F, E, E, T, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_380 trivial)

theorem z_382 : le (tf [F, F, E, E, T, E, F, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, F, T, T, T, T, F, F] [([F, F, E, E, E, T, F, T, T, T, T, F, F], [F, F, E, E, F, T, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_381 trivial)

theorem z_383 : le (tf [F, E, F, E, T, T, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, F, E, T, T, T, F, F] [([F, E, F, E, T, E, F, T, T, T, T, F, F], [F, F, E, E, T, E, F, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_382 trivial)

theorem z_384 : le (tf [F, E, F, E, T, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, E, T, T, F, F] [([F, E, F, E, T, T, E, F, T, T, T, F, F], [F, E, F, E, T, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_383 trivial)

theorem z_385 : le (tf [F, F, E, E, E, F, T, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, T, T, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_386 : le (tf [F, E, F, E, T, F, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, F, E, T, T, T, T, F, F] [([F, E, F, E, E, F, T, T, T, T, T, F, F], [F, F, E, E, E, F, T, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_385 trivial)

theorem z_387 : le (tf [F, E, T, F, E, F, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, F, E, T, T, T, T, F, F] [([F, E, E, F, T, F, E, T, T, T, T, F, F], [F, E, F, E, T, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_386 trivial)

theorem z_388 : le (tf [F, E, T, F, E, T, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, F, E, T, T, T, F, F] [([F, E, E, F, T, T, F, E, T, T, T, F, F], [F, E, F, E, T, T, F, E, T, T, T, F, F]), ([F, E, T, F, E, E, F, T, T, T, T, F, F], [F, E, T, F, E, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_383 (And.intro z_387 trivial))

theorem z_389 : le (tf [F, E, T, F, E, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, E, T, T, F, F] [([F, E, E, F, T, T, T, F, E, T, T, F, F], [F, E, F, E, T, T, T, F, E, T, T, F, F]), ([F, E, T, F, E, T, E, F, T, T, T, F, F], [F, E, T, F, E, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_384 (And.intro z_388 trivial))

theorem z_390 : le (tf [F, E, T, T, F, E, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, F, E, T, T, T, F, F] [([F, E, T, E, F, T, F, E, T, T, T, F, F], [F, E, T, F, E, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_388 trivial)

theorem z_391 : le (tf [F, E, T, T, F, E, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, E, T, T, F, F] [([F, E, T, E, F, T, T, F, E, T, T, F, F], [F, E, T, F, E, T, T, F, E, T, T, F, F]), ([F, E, T, T, F, E, E, F, T, T, T, F, F], [F, E, T, T, F, E, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_389 (And.intro z_390 trivial))

theorem z_392 : le (tf [T, F, F, E, F, E, E, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, E, T, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_393 : le (tf [T, F, F, E, E, F, T, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, F, T, E, T, T, T, F, F] [([T, F, F, E, E, F, E, T, T, T, T, F, F], [T, F, F, E, F, E, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_392 trivial)

theorem z_394 : le (tf [T, F, F, E, E, T, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, E, F, T, T, T, F, F] [([T, F, F, E, E, E, T, F, T, T, T, F, F], [T, F, F, E, E, F, T, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_393 trivial)

theorem z_395 : le (tf [T, F, E, F, E, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, E, T, T, F, F] [([E, F, T, F, E, T, T, F, E, T, T, F, F], [F, E, T, F, E, T, T, F, E, T, T, F, F]), ([T, F, E, F, E, T, E, F, T, T, T, F, F], [T, F, F, E, E, T, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_389 (And.intro z_394 trivial))

theorem z_396 : le (tf [T, F, F, E, E, E, F, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, E, F, T, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_397 : le (tf [T, F, E, F, E, T, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, F, E, T, T, T, F, F] [([E, F, T, F, E, T, F, E, T, T, T, F, F], [F, E, T, F, E, T, F, E, T, T, T, F, F]), ([T, F, E, F, E, E, F, T, T, T, T, F, F], [T, F, F, E, E, E, F, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_388 (And.intro z_396 trivial))

theorem z_398 : le (tf [T, F, E, T, F, E, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, F, E, T, T, T, F, F] [([E, F, T, T, F, E, F, E, T, T, T, F, F], [F, E, T, T, F, E, F, E, T, T, T, F, F]), ([T, F, E, E, F, T, F, E, T, T, T, F, F], [T, F, E, F, E, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_390 (And.intro z_397 trivial))

theorem z_399 : le (tf [T, F, E, T, F, E, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, E, T, T, F, F] [([E, F, T, T, F, E, T, F, E, T, T, F, F], [F, E, T, T, F, E, T, F, E, T, T, F, F]), ([T, F, E, E, F, T, T, F, E, T, T, F, F], [T, F, E, F, E, T, T, F, E, T, T, F, F]), ([T, F, E, T, F, E, E, F, T, T, T, F, F], [T, F, E, T, F, E, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_391 (And.intro z_395 (And.intro z_398 trivial)))

theorem z_400 : le (tf [T, F, E, T, F, E, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, E, F, T, T, T, F, F] [([E, F, T, T, F, E, E, F, T, T, T, F, F], [F, E, T, T, F, E, E, F, T, T, T, F, F]), ([T, F, E, E, F, T, E, F, T, T, T, F, F], [T, F, E, F, E, T, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_289 (And.intro z_377 trivial))

theorem z_401 : le (tf [F, E, T, T, T, F, F, F, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, E, F, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_402 : le (tf [F, E, T, T, T, F, F, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, E, T, F, E, T] [([F, E, T, T, T, F, F, F, E, E, F, T, T], [F, E, T, T, T, F, F, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 trivial)

theorem z_403 : le (tf [F, E, T, T, T, F, F, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, E, T, T, F, E] [([F, E, T, T, T, F, F, F, E, T, E, F, T], [F, E, T, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 trivial)

theorem z_404 : le (tf [F, E, T, T, T, F, F, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, F, E, F, E, T] [([F, E, T, T, T, F, F, E, F, T, F, E, T], [F, E, T, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 trivial)

theorem z_405 : le (tf [F, E, T, T, T, F, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, F, E, T, F, E] [([F, E, T, T, T, F, F, E, F, T, T, F, E], [F, E, T, T, T, F, F, F, E, T, T, F, E]), ([F, E, T, T, T, F, F, T, F, E, E, F, T], [F, E, T, T, T, F, F, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_404 trivial))

theorem z_406 : le (tf [T, F, E, T, T, F, F, F, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, E, F, E, T, T] [([E, F, T, T, T, F, F, F, E, F, E, T, T], [F, E, T, T, T, F, F, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 trivial)

theorem z_407 : le (tf [T, F, E, T, T, F, F, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, E, T, F, E, T] [([E, F, T, T, T, F, F, F, E, T, F, E, T], [F, E, T, T, T, F, F, F, E, T, F, E, T]), ([T, F, E, T, T, F, F, F, E, E, F, T, T], [T, F, E, T, T, F, F, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_406 trivial))

theorem z_408 : le (tf [T, F, E, T, T, F, F, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, E, T, T, F, E] [([E, F, T, T, T, F, F, F, E, T, T, F, E], [F, E, T, T, T, F, F, F, E, T, T, F, E]), ([T, F, E, T, T, F, F, F, E, T, E, F, T], [T, F, E, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_407 trivial))

theorem z_409 : le (tf [T, F, E, T, T, F, F, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, F, E, F, E, T] [([E, F, T, T, T, F, F, T, F, E, F, E, T], [F, E, T, T, T, F, F, T, F, E, F, E, T]), ([T, F, E, T, T, F, F, E, F, T, F, E, T], [T, F, E, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_404 (And.intro z_407 trivial))

theorem z_410 : le (tf [T, F, E, T, T, F, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, F, E, T, F, E] [([E, F, T, T, T, F, F, T, F, E, T, F, E], [F, E, T, T, T, F, F, T, F, E, T, F, E]), ([T, F, E, T, T, F, F, E, F, T, T, F, E], [T, F, E, T, T, F, F, F, E, T, T, F, E]), ([T, F, E, T, T, F, F, T, F, E, E, F, T], [T, F, E, T, T, F, F, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_405 (And.intro z_408 (And.intro z_409 trivial)))

theorem z_411 : le (tf [F, E, T, T, T, F, F, F, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, F, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_412 : le (tf [F, E, T, T, T, F, F, F, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, E, F, T, E, T] [([F, E, T, T, T, F, F, F, E, F, E, T, T], [F, E, T, T, T, F, F, F, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_411 trivial)

theorem z_413 : le (tf [F, E, T, T, T, F, F, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, E, T, E, F, T] [([F, E, T, T, T, F, F, F, E, E, T, F, T], [F, E, T, T, T, F, F, F, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_412 trivial)

theorem z_414 : le (tf [F, E, T, T, T, F, F, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, F, T, T, F, E] [([F, E, T, T, T, F, F, E, F, T, E, F, T], [F, E, T, T, T, F, F, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 trivial)

theorem z_415 : le (tf [F, E, T, T, T, F, F, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, F, E, E, F, T] [([F, E, T, T, T, F, F, E, F, T, E, F, T], [F, E, T, T, T, F, F, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 trivial)

theorem z_416 : le (tf [E, F, T, T, T, F, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, F, E, T, F, E] [([E, F, T, T, T, F, F, E, F, T, T, F, E], [F, E, T, T, T, F, F, E, F, T, T, F, E]), ([E, F, T, T, T, F, F, T, F, E, E, F, T], [F, E, T, T, T, F, F, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_414 (And.intro z_415 trivial))

theorem z_417 : le (tf [T, F, E, T, T, F, F, F, F, E, E, T, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, F, E, E, T, T] [([E, F, T, T, T, F, F, F, F, E, E, T, T], [F, E, T, T, T, F, F, F, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_411 trivial)

theorem z_418 : le (tf [T, F, E, T, T, F, F, F, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, E, F, T, E, T] [([E, F, T, T, T, F, F, F, E, F, T, E, T], [F, E, T, T, T, F, F, F, E, F, T, E, T]), ([T, F, E, T, T, F, F, F, E, F, E, T, T], [T, F, E, T, T, F, F, F, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_412 (And.intro z_417 trivial))

theorem z_419 : le (tf [T, F, E, T, T, F, F, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, E, T, E, F, T] [([E, F, T, T, T, F, F, F, E, T, E, F, T], [F, E, T, T, T, F, F, F, E, T, E, F, T]), ([T, F, E, T, T, F, F, F, E, E, T, F, T], [T, F, E, T, T, F, F, F, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 (And.intro z_418 trivial))

theorem z_420 : le (tf [T, F, E, T, T, F, F, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, F, T, T, F, E] [([E, F, T, T, T, F, F, E, F, T, T, F, E], [F, E, T, T, T, F, F, E, F, T, T, F, E]), ([T, F, E, T, T, F, F, E, F, T, E, F, T], [T, F, E, T, T, F, F, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_414 (And.intro z_419 trivial))

theorem z_421 : le (tf [T, F, E, T, T, F, F, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, F, E, E, F, T] [([E, F, T, T, T, F, F, T, F, E, E, F, T], [F, E, T, T, T, F, F, T, F, E, E, F, T]), ([T, F, E, T, T, F, F, E, F, T, E, F, T], [T, F, E, T, T, F, F, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_415 (And.intro z_419 trivial))

theorem z_422 : le (tf [F, E, T, T, T, F, F, E, F, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, F, T, F, T, E] [([F, E, T, T, T, F, F, E, F, T, F, E, T], [F, E, T, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 trivial)

theorem z_423 : le (tf [F, E, T, T, T, F, F, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, F, T, T, E, F] [([F, E, T, T, T, F, F, E, F, T, E, T, F], [F, E, T, T, T, F, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_422 trivial)

theorem z_424 : le (tf [F, E, T, T, T, F, F, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, F, E, E, T, F] [([F, E, T, T, T, F, F, E, F, T, E, T, F], [F, E, T, T, T, F, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_422 trivial)

theorem z_425 : le (tf [E, F, T, T, T, F, F, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, F, E, T, E, F] [([E, F, T, T, T, F, F, E, F, T, T, E, F], [F, E, T, T, T, F, F, E, F, T, T, E, F]), ([E, F, T, T, T, F, F, T, F, E, E, T, F], [F, E, T, T, T, F, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_423 (And.intro z_424 trivial))

theorem z_426 : le (tf [T, F, E, T, T, F, F, E, F, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, F, T, F, T, E] [([E, F, T, T, T, F, F, E, F, T, F, T, E], [F, E, T, T, T, F, F, E, F, T, F, T, E]), ([T, F, E, T, T, F, F, E, F, T, F, E, T], [T, F, E, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_422 (And.intro z_407 trivial))

theorem z_427 : le (tf [T, F, E, T, T, F, F, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, F, T, T, E, F] [([E, F, T, T, T, F, F, E, F, T, T, E, F], [F, E, T, T, T, F, F, E, F, T, T, E, F]), ([T, F, E, T, T, F, F, E, F, T, E, T, F], [T, F, E, T, T, F, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_423 (And.intro z_426 trivial))

theorem z_428 : le (tf [T, F, E, T, T, F, F, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, F, E, E, T, F] [([E, F, T, T, T, F, F, T, F, E, E, T, F], [F, E, T, T, T, F, F, T, F, E, E, T, F]), ([T, F, E, T, T, F, F, E, F, T, E, T, F], [T, F, E, T, T, F, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_424 (And.intro z_426 trivial))

theorem z_429 : le (tf [F, E, T, T, T, F, F, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, F, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_430 : le (tf [F, E, T, T, T, F, F, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, T, F, E, F, T] [([F, E, T, T, T, F, F, E, E, F, T, F, T], [F, E, T, T, T, F, F, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 trivial)

theorem z_431 : le (tf [E, F, T, T, T, F, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, E, T, F, T, F, E] [([E, F, T, T, T, F, F, E, T, F, E, F, T], [F, E, T, T, T, F, F, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_430 trivial)

theorem z_432 : le (tf [F, E, T, T, T, F, F, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_433 : le (tf [F, E, T, T, T, F, F, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, F, T, E, T, F] [([F, E, T, T, T, F, F, E, F, E, T, T, F], [F, E, T, T, T, F, F, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 trivial)

theorem z_434 : le (tf [E, F, T, T, T, F, F, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, F, E, E, T, F] [([E, F, T, T, T, F, F, E, F, T, E, T, F], [F, E, T, T, T, F, F, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 trivial)

theorem z_435 : le (tf [E, F, T, T, T, F, F, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, E, F, T, E, F] [([E, F, T, T, T, F, F, E, T, F, T, E, F], [E, F, T, T, T, F, F, E, T, F, T, F, E]), ([E, F, T, T, T, F, F, T, E, F, E, T, F], [E, F, T, T, T, F, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_431 (And.intro z_434 trivial))

theorem z_436 : le (tf [F, E, T, T, T, F, F, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, T, E, E, F, T] [([F, E, T, T, T, F, F, F, E, T, E, F, T], [F, E, T, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 trivial)

theorem z_437 : le (tf [F, E, T, T, T, F, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, T, F, T, F, E] [([F, E, T, T, T, F, F, E, T, F, E, F, T], [F, E, T, T, T, F, F, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_436 trivial)

theorem z_438 : le (tf [T, F, E, T, T, F, F, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, T, E, E, F, T] [([E, F, T, T, T, F, F, F, T, E, E, F, T], [F, E, T, T, T, F, F, F, T, E, E, F, T]), ([T, F, E, T, T, F, F, F, E, T, E, F, T], [T, F, E, T, T, F, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_436 (And.intro z_407 trivial))

theorem z_439 : le (tf [T, F, E, T, T, F, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, T, F, T, F, E] [([E, F, T, T, T, F, F, E, T, F, T, F, E], [F, E, T, T, T, F, F, E, T, F, T, F, E]), ([T, F, E, T, T, F, F, E, T, F, E, F, T], [T, F, E, T, T, F, F, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_437 (And.intro z_438 trivial))

theorem z_440 : le (tf [T, F, E, T, T, F, F, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, F, E, T, F, T] [([E, F, T, T, T, F, F, E, F, E, T, F, T], [F, E, T, T, T, F, F, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 trivial)

theorem z_441 : le (tf [T, F, E, T, T, F, F, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, T, F, E, F, T] [([E, F, T, T, T, F, F, E, T, F, E, F, T], [F, E, T, T, T, F, F, E, T, F, E, F, T]), ([T, F, E, T, T, F, F, E, E, F, T, F, T], [T, F, E, T, T, F, F, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_430 (And.intro z_440 trivial))

theorem z_442 : le (tf [T, F, E, T, T, F, F, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, F, E, E, T, T, F] [([E, F, T, T, T, F, F, F, E, E, T, T, F], [F, E, T, T, T, F, F, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 trivial)

theorem z_443 : le (tf [T, F, E, T, T, F, F, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, F, T, E, T, F] [([E, F, T, T, T, F, F, E, F, T, E, T, F], [F, E, T, T, T, F, F, E, F, T, E, T, F]), ([T, F, E, T, T, F, F, E, F, E, T, T, F], [T, F, E, T, T, F, F, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 (And.intro z_442 trivial))

theorem z_444 : le (tf [F, E, T, T, T, F, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, F, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_445 : le (tf [F, E, T, T, T, F, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, T, F, E, T, F] [([F, E, T, T, T, F, F, E, E, F, T, T, F], [F, E, T, T, T, F, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_444 trivial)

theorem z_446 : le (tf [E, F, T, T, T, F, F, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, E, T, F, T, E, F] [([E, F, T, T, T, F, F, E, T, F, E, T, F], [F, E, T, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_445 trivial)

theorem z_447 : le (tf [E, F, T, T, T, F, F, T, E, E, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, E, E, T, F, F] [([E, F, T, T, T, F, F, E, T, E, T, F, F], [E, F, T, T, T, F, F, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_446 trivial)

theorem z_448 : le (tf [T, F, E, T, T, F, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, F, E, T, T, F] [([E, F, T, T, T, F, F, E, F, E, T, T, F], [F, E, T, T, T, F, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_444 trivial)

theorem z_449 : le (tf [T, F, E, T, T, F, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, T, F, E, T, F] [([E, F, T, T, T, F, F, E, T, F, E, T, F], [F, E, T, T, T, F, F, E, T, F, E, T, F]), ([T, F, E, T, T, F, F, E, E, F, T, T, F], [T, F, E, T, T, F, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_445 (And.intro z_448 trivial))

theorem z_450 : le (tf [F, E, T, T, T, F, F, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, E, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_451 : le (tf [T, F, E, T, T, F, F, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, E, T, T, F, F] [([E, F, T, T, T, F, F, E, E, T, T, F, F], [F, E, T, T, T, F, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_450 trivial)

theorem z_452 : le (tf [E, F, T, T, T, F, F, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, E, E, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_453 : le (tf [T, F, E, T, T, T, F, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, F, E, F, E, T] [([E, F, T, T, T, T, F, F, F, E, F, E, T], [F, E, T, T, T, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_230 trivial)

theorem z_454 : le (tf [T, F, E, T, T, T, F, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, F, E, T, F, E] [([E, F, T, T, T, T, F, F, F, E, T, F, E], [F, E, T, T, T, T, F, F, F, E, T, F, E]), ([T, F, E, T, T, T, F, F, F, E, E, F, T], [T, F, E, T, T, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 (And.intro z_453 trivial))

theorem z_455 : le (tf [E, F, T, T, T, T, F, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, F, E, T, F, E] [([E, F, T, T, T, T, F, F, F, E, E, F, T], [F, E, T, T, T, T, F, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 trivial)

theorem z_456 : le (tf [E, F, T, T, T, T, F, F, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, F, E, T, E, F] [([E, F, T, T, T, T, F, F, F, E, E, T, F], [F, E, T, T, T, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_236 trivial)

theorem z_457 : le (tf [E, F, T, T, T, T, F, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, E, F, T, E, F] [([E, F, T, T, T, T, F, F, E, F, E, T, F], [F, E, T, T, T, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 trivial)

theorem z_458 : le (tf [E, F, T, T, T, T, F, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, E, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_459 : le (tf [T, T, F, E, F, E, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, T, T, F, F, F, E] [([T, E, F, T, F, E, T, T, T, F, F, F, E], [T, F, E, T, F, E, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_303 trivial)

theorem z_460 : le (tf [T, T, F, E, T, F, E, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, T, T, F, F, F, E] [([T, E, F, T, T, F, E, T, T, F, F, F, E], [T, F, E, T, T, F, E, T, T, F, F, F, E]), ([T, T, F, E, E, F, T, T, T, F, F, F, E], [T, T, F, E, F, E, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_304 (And.intro z_459 trivial))

theorem z_461 : le (tf [T, T, F, F, E, E, T, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, T, F, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_462 : le (tf [T, T, F, E, E, F, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, E, F, T, T, T, F, F, E, F] [([T, E, F, T, E, F, T, T, T, F, F, E, F], [T, F, E, T, E, F, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_315 trivial)

theorem z_463 : le (tf [T, T, F, F, E, E, T, T, F, F, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_464 : le (tf [T, T, F, F, E, E, T, T, F, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, F, T, F, E] [([T, T, F, F, E, E, T, T, F, F, E, F, T], [T, T, F, F, E, E, T, T, F, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_463 trivial)

theorem z_465 : le (tf [T, T, F, F, E, E, T, T, F, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, F, E, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_466 : le (tf [T, T, F, F, E, E, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_467 : le (tf [T, T, F, F, E, F, E, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, E, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_468 : le (tf [T, T, F, F, E, E, F, T, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, T, E, T, T, F, F] [([T, T, F, F, E, E, F, E, T, T, T, F, F], [T, T, F, F, E, F, E, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_467 trivial)

theorem z_469 : le (tf [T, T, F, F, E, E, T, E, F, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, E, F, T, T, F, F] [([T, T, F, F, E, E, E, T, F, T, T, F, F], [T, T, F, F, E, E, F, T, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_468 trivial)

theorem z_470 : le (tf [T, T, F, F, F, F, E, F, E, E, T, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, F, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_471 : le (tf [T, T, F, F, F, F, E, E, F, T, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, F, T, E, T, T] [([T, T, F, F, F, F, E, E, F, E, T, T, T], [T, T, F, F, F, F, E, F, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_470 trivial)

theorem z_472 : le (tf [T, T, F, F, F, F, E, E, T, E, F, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, T, E, F, T, T] [([T, T, F, F, F, F, E, E, E, T, F, T, T], [T, T, F, F, F, F, E, E, F, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_471 trivial)

theorem z_473 : le (tf [T, T, F, F, F, E, F, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, T, T, F, E, T] [([T, T, F, F, F, E, F, E, T, E, F, T, T], [T, T, F, F, F, F, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_472 trivial)

theorem z_474 : le (tf [T, T, F, F, F, E, F, E, T, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, T, T, T, F, E] [([T, T, F, F, F, E, F, E, T, T, E, F, T], [T, T, F, F, F, E, F, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_473 trivial)

theorem z_475 : le (tf [T, T, F, F, F, F, E, E, E, F, T, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, E, F, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_476 : le (tf [T, T, F, F, F, E, F, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, T, F, E, T, T] [([T, T, F, F, F, E, F, E, E, F, T, T, T], [T, T, F, F, F, F, E, E, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_475 trivial)

theorem z_477 : le (tf [T, T, F, F, F, E, T, F, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, E, F, E, T, T] [([T, T, F, F, F, E, E, F, T, F, E, T, T], [T, T, F, F, F, E, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_476 trivial)

theorem z_478 : le (tf [T, T, F, F, F, E, T, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, E, T, F, E, T] [([T, T, F, F, F, E, E, F, T, T, F, E, T], [T, T, F, F, F, E, F, E, T, T, F, E, T]), ([T, T, F, F, F, E, T, F, E, E, F, T, T], [T, T, F, F, F, E, T, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_473 (And.intro z_477 trivial))

theorem z_479 : le (tf [T, T, F, F, F, E, T, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, E, T, T, F, E] [([T, T, F, F, F, E, E, F, T, T, T, F, E], [T, T, F, F, F, E, F, E, T, T, T, F, E]), ([T, T, F, F, F, E, T, F, E, T, E, F, T], [T, T, F, F, F, E, T, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_474 (And.intro z_478 trivial))

theorem z_480 : le (tf [T, T, F, F, F, E, T, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, T, E, E, F, T] [([T, T, F, F, F, E, T, F, E, T, E, F, T], [T, T, F, F, F, E, T, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 trivial)

theorem z_481 : le (tf [T, T, F, F, E, F, T, F, T, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, F, T, E, T, F, E] [([T, T, F, F, E, F, T, F, E, T, T, F, E], [T, T, F, F, F, E, T, F, E, T, T, F, E]), ([T, T, F, F, E, F, T, F, T, E, E, F, T], [T, T, F, F, F, E, T, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_479 (And.intro z_480 trivial))

theorem z_482 : le (tf [T, T, F, F, F, F, E, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, F, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_483 : le (tf [T, T, F, F, F, F, E, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, T, F, E, T, T] [([T, T, F, F, F, F, E, E, E, F, T, T, T], [T, T, F, F, F, F, E, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_482 trivial)

theorem z_484 : le (tf [T, T, F, F, F, E, F, E, T, F, T, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, T, F, T, E, T] [([T, T, F, F, F, E, F, E, T, F, E, T, T], [T, T, F, F, F, F, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_483 trivial)

theorem z_485 : le (tf [T, T, F, F, F, E, F, E, T, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, T, T, E, F, T] [([T, T, F, F, F, E, F, E, T, E, T, F, T], [T, T, F, F, F, E, F, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_484 trivial)

theorem z_486 : le (tf [T, T, F, F, F, E, E, F, T, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, F, T, T, T, F, E] [([T, T, F, F, F, E, E, F, T, T, E, F, T], [T, T, F, F, F, E, F, E, T, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_485 trivial)

theorem z_487 : le (tf [T, T, F, F, F, F, F, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, F, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_488 : le (tf [T, T, F, F, F, F, E, F, E, T, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, F, E, T, E, T, T] [([T, T, F, F, F, F, E, F, E, E, T, T, T], [T, T, F, F, F, F, F, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_487 trivial)

theorem z_489 : le (tf [T, T, F, F, F, F, E, T, F, E, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, T, F, E, E, T, T] [([T, T, F, F, F, F, E, E, F, T, E, T, T], [T, T, F, F, F, F, E, F, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_488 trivial)

theorem z_490 : le (tf [T, T, F, F, F, F, T, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, T, E, E, F, E, T, T] [([T, T, F, F, F, F, E, T, E, F, E, T, T], [T, T, F, F, F, F, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_489 trivial)

theorem z_491 : le (tf [T, T, F, F, F, E, T, F, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, E, F, T, E, T] [([T, T, F, F, F, E, E, F, T, F, T, E, T], [T, T, F, F, F, E, F, E, T, F, T, E, T]), ([T, T, F, F, F, E, T, F, E, F, E, T, T], [T, T, F, F, F, F, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_484 (And.intro z_490 trivial))

theorem z_492 : le (tf [T, T, F, F, F, E, T, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, E, T, E, F, T] [([T, T, F, F, F, E, E, F, T, T, E, F, T], [T, T, F, F, F, E, F, E, T, T, E, F, T]), ([T, T, F, F, F, E, T, F, E, E, T, F, T], [T, T, F, F, F, E, T, F, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_485 (And.intro z_491 trivial))

theorem z_493 : le (tf [T, T, F, F, E, F, T, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, F, E, T, T, F, E] [([T, T, F, F, E, F, E, F, T, T, T, F, E], [T, T, F, F, F, E, E, F, T, T, T, F, E]), ([T, T, F, F, E, F, T, F, E, T, E, F, T], [T, T, F, F, F, E, T, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_486 (And.intro z_492 trivial))

theorem z_494 : le (tf [T, T, F, F, E, F, T, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, F, T, E, E, F, T] [([T, T, F, F, E, F, T, F, E, T, E, F, T], [T, T, F, F, F, E, T, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_492 trivial)

theorem z_495 : le (tf [T, T, F, F, F, E, E, F, T, T, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, F, T, T, F, T, E] [([T, T, F, F, F, E, E, F, T, T, F, E, T], [T, T, F, F, F, E, F, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_473 trivial)

theorem z_496 : le (tf [T, T, F, F, F, E, E, F, T, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, F, T, T, T, E, F] [([T, T, F, F, F, E, E, F, T, T, E, T, F], [T, T, F, F, F, E, E, F, T, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_495 trivial)

theorem z_497 : le (tf [T, T, F, F, E, F, T, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, F, E, T, F, T, E] [([T, T, F, F, E, F, E, F, T, T, F, T, E], [T, T, F, F, F, E, E, F, T, T, F, T, E]), ([T, T, F, F, E, F, T, F, E, T, F, E, T], [T, T, F, F, F, E, T, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_495 (And.intro z_478 trivial))

theorem z_498 : le (tf [T, T, F, F, E, F, T, F, E, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, F, E, T, T, E, F] [([T, T, F, F, E, F, E, F, T, T, T, E, F], [T, T, F, F, F, E, E, F, T, T, T, E, F]), ([T, T, F, F, E, F, T, F, E, T, E, T, F], [T, T, F, F, E, F, T, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_496 (And.intro z_497 trivial))

theorem z_499 : le (tf [T, T, F, F, E, F, T, F, T, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, F, T, E, E, T, F] [([T, T, F, F, E, F, T, F, E, T, E, T, F], [T, T, F, F, E, F, T, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_497 trivial)

theorem z_500 : le (tf [T, T, F, F, F, E, E, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, F, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_501 : le (tf [T, T, F, F, F, E, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, F, E, T, T, F] [([T, T, F, F, F, E, E, E, F, T, T, T, F], [T, T, F, F, F, E, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_500 trivial)

theorem z_502 : le (tf [T, T, F, F, F, E, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, T, F, E, T, F] [([T, T, F, F, F, E, E, T, E, F, T, T, F], [T, T, F, F, F, E, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_501 trivial)

theorem z_503 : le (tf [T, T, F, F, E, F, E, T, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, T, F, T, E, F] [([T, T, F, F, E, F, E, T, T, F, E, T, F], [T, T, F, F, F, E, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_502 trivial)

theorem z_504 : le (tf [T, T, F, F, F, E, T, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, E, E, F, T, T, F] [([T, T, F, F, F, E, E, T, E, F, T, T, F], [T, T, F, F, F, E, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_501 trivial)

theorem z_505 : le (tf [T, T, F, F, E, F, T, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, T, F, E, T, F] [([T, T, F, F, E, F, E, T, T, F, E, T, F], [T, T, F, F, F, E, E, T, T, F, E, T, F]), ([T, T, F, F, E, F, T, E, E, F, T, T, F], [T, T, F, F, F, E, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_502 (And.intro z_504 trivial))

theorem z_506 : le (tf [T, T, F, F, F, E, F, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_507 : le (tf [T, T, F, F, F, E, E, F, T, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, F, T, E, T, T, F] [([T, T, F, F, F, E, E, F, E, T, T, T, F], [T, T, F, F, F, E, F, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_506 trivial)

theorem z_508 : le (tf [T, T, F, F, F, E, E, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, E, F, T, T, F] [([T, T, F, F, F, E, E, E, T, F, T, T, F], [T, T, F, F, F, E, E, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_507 trivial)

theorem z_509 : le (tf [T, T, F, F, E, F, T, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, E, F, T, T, F] [([T, T, F, F, E, F, E, T, E, F, T, T, F], [T, T, F, F, F, E, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_508 trivial)

theorem z_510 : le (tf [T, T, F, F, E, E, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, F, T, F, E, T, F] [([T, T, F, F, E, E, T, F, E, F, T, T, F], [T, T, F, F, E, F, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_509 trivial)

theorem z_511 : le (tf [T, T, F, F, E, E, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, E, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_512 : le (tf [T, T, F, F, E, E, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, F, E, T, T, F, F] [([T, T, F, F, E, E, E, F, T, T, T, F, F], [T, T, F, F, E, E, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_511 trivial)

theorem z_513 : le (tf [T, T, F, F, E, E, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, E, F, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_514 : le (tf [T, T, F, F, E, E, E, T, F, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, E, T, F, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_515 : le (tf [T, T, F, F, E, T, E, E, F, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, E, F, T, T, F, F] [([T, T, F, F, E, E, T, E, F, T, T, F, F], [T, T, F, F, E, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_512 trivial)

theorem z_516 : le (tf [T, T, F, E, T, T, F, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, F, E, F, E, T] [([T, E, F, T, T, T, F, F, F, E, F, E, T], [T, F, E, T, T, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_453 trivial)

theorem z_517 : le (tf [T, T, F, E, T, T, F, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, F, E, T, F, E] [([T, E, F, T, T, T, F, F, F, E, T, F, E], [T, F, E, T, T, T, F, F, F, E, T, F, E]), ([T, T, F, E, T, T, F, F, F, E, E, F, T], [T, T, F, E, T, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_454 (And.intro z_516 trivial))

theorem z_518 : le (tf [T, T, T, F, F, E, E, T, T, F, F, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, T, T, F, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_519 : le (tf [T, T, T, F, F, E, F, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, E, E, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_520 : le (tf [T, T, T, F, F, E, E, F, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, F, T, E, T, F, F] [([T, T, T, F, F, E, E, F, E, T, T, F, F], [T, T, T, F, F, E, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_519 trivial)

theorem z_521 : le (tf [T, T, T, F, F, E, E, T, E, F, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, T, E, F, T, F, F] [([T, T, T, F, F, E, E, E, T, F, T, F, F], [T, T, T, F, F, E, E, F, T, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_520 trivial)

theorem z_522 : le (tf [T, T, T, F, F, F, F, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_523 : le (tf [T, T, T, F, F, F, E, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, E, T, E, F, T] [([T, T, T, F, F, F, E, F, E, E, T, F, T], [T, T, T, F, F, F, F, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_522 trivial)

theorem z_524 : le (tf [T, T, T, F, F, F, E, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, F, T, T, F, E] [([T, T, T, F, F, F, E, E, F, T, E, F, T], [T, T, T, F, F, F, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_523 trivial)

theorem z_525 : le (tf [T, T, T, F, F, F, E, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, F, E, E, F, T] [([T, T, T, F, F, F, E, E, F, T, E, F, T], [T, T, T, F, F, F, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_523 trivial)

theorem z_526 : le (tf [T, T, T, F, F, F, E, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, F, T, T, E, F] [([T, T, T, F, F, F, E, E, F, T, E, T, F], [T, T, T, F, F, F, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_71 trivial)

theorem z_527 : le (tf [T, T, T, F, F, F, F, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, E, T, T, F, E] [([T, T, T, F, F, F, F, E, E, T, E, F, T], [T, T, T, F, F, F, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 trivial)

theorem z_528 : le (tf [T, T, T, F, F, F, F, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, F, E, T, E, E, F, T] [([T, T, T, F, F, F, F, E, E, T, E, F, T], [T, T, T, F, F, F, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 trivial)

theorem z_529 : le (tf [T, T, T, F, F, F, E, F, T, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, F, T, E, T, F, E] [([T, T, T, F, F, F, E, F, E, T, T, F, E], [T, T, T, F, F, F, F, E, E, T, T, F, E]), ([T, T, T, F, F, F, E, F, T, E, E, F, T], [T, T, T, F, F, F, F, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_527 (And.intro z_528 trivial))

theorem z_530 : le (tf [T, T, T, F, F, F, E, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, E, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_531 : le (tf [T, T, T, F, F, E, F, E, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, E, T, E, T, F, F] [([T, T, T, F, F, E, F, E, E, T, T, F, F], [T, T, T, F, F, F, E, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_530 trivial)

theorem z_532 : le (tf [T, T, T, F, F, E, E, E, F, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, E, F, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_533 : le (tf [T, T, T, F, F, E, E, E, T, F, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, E, T, F, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_534 : le (tf [T, T, T, F, F, T, F, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, E, E, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_535 : le (tf [T, T, T, F, F, T, F, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_536 : le (tf [T, T, T, F, F, E, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, F, E, E, T, F, F] [([T, T, T, F, F, E, E, F, T, E, T, F, F], [T, T, T, F, F, E, F, E, T, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_531 trivial)

theorem z_537 : le (tf [T, T, T, F, F, E, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, F, E, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_538 : le (tf [T, T, T, F, F, E, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, T, F, E, T, F, F] [([T, T, T, F, F, E, E, E, F, T, T, F, F], [T, T, T, F, F, E, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_537 trivial)

theorem z_539 : le (tf [T, T, T, F, F, E, T, E, E, F, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, E, E, F, T, F, F] [([T, T, T, F, F, E, E, T, E, F, T, F, F], [T, T, T, F, F, E, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_538 trivial)

theorem z_540 : le (tf [T, T, T, F, T, F, F, F, F, E, E, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_541 : le (tf [T, T, T, F, T, F, F, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, F, E, T, E] [([T, T, T, F, T, F, F, F, E, F, E, E, T], [T, T, T, F, T, F, F, F, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_540 trivial)

theorem z_542 : le (tf [T, T, T, F, T, F, F, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, T, F, E, E] [([T, T, T, F, T, F, F, F, E, E, F, T, E], [T, T, T, F, T, F, F, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_541 trivial)

theorem z_543 : le (tf [T, T, T, F, T, F, F, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, T, E, E, F, E] [([T, T, T, F, T, F, F, F, E, T, E, F, E], [T, T, T, F, T, F, F, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_542 trivial)

theorem z_544 : le (tf [T, T, T, F, T, F, F, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_545 : le (tf [T, T, T, F, T, F, F, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, E, F, T, E] [([T, T, T, F, T, F, F, F, E, E, F, E, T], [T, T, T, F, T, F, F, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_544 trivial)

theorem z_546 : le (tf [T, T, T, F, T, F, F, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_547 : le (tf [T, T, T, F, T, F, F, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, E, T, F, E] [([T, T, T, F, T, F, F, F, E, E, E, F, T], [T, T, T, F, T, F, F, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_546 trivial)

theorem z_548 : le (tf [T, T, T, F, T, F, F, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, T, E, E, F] [([T, T, T, F, T, F, F, F, E, E, T, E, F], [T, T, T, F, T, F, F, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_547 trivial)

theorem z_549 : le (tf [F, E, T, T, T, F, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, T, T, F, E, F] [([F, E, T, T, T, F, F, E, T, E, F, T, F], [F, E, T, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_445 trivial)

theorem z_550 : le (tf [F, E, T, T, T, F, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, E, F, E, T, F] [([F, E, T, T, T, F, E, F, T, F, E, T, F], [F, E, T, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_445 trivial)

theorem z_551 : le (tf [F, E, T, T, T, F, T, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, E, T, F, E, F] [([F, E, T, T, T, F, E, F, T, T, F, E, F], [F, E, T, T, T, F, F, E, T, T, F, E, F]), ([F, E, T, T, T, F, T, F, E, E, F, T, F], [F, E, T, T, T, F, T, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_549 (And.intro z_550 trivial))

theorem z_552 : le (tf [F, E, T, T, T, F, T, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, T, E, E, F, F] [([F, E, T, T, T, F, T, F, E, T, E, F, F], [F, E, T, T, T, F, T, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_551 trivial)

theorem z_553 : le (tf [T, F, E, T, T, F, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, T, T, F, E, F] [([E, F, T, T, T, F, F, E, T, T, F, E, F], [F, E, T, T, T, F, F, E, T, T, F, E, F]), ([T, F, E, T, T, F, F, E, T, E, F, T, F], [T, F, E, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_549 (And.intro z_449 trivial))

theorem z_554 : le (tf [T, F, E, T, T, F, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, E, F, E, T, F] [([E, F, T, T, T, F, T, F, E, F, E, T, F], [F, E, T, T, T, F, T, F, E, F, E, T, F]), ([T, F, E, T, T, F, E, F, T, F, E, T, F], [T, F, E, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_550 (And.intro z_449 trivial))

theorem z_555 : le (tf [T, F, E, T, T, F, T, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, E, T, F, E, F] [([E, F, T, T, T, F, T, F, E, T, F, E, F], [F, E, T, T, T, F, T, F, E, T, F, E, F]), ([T, F, E, T, T, F, E, F, T, T, F, E, F], [T, F, E, T, T, F, F, E, T, T, F, E, F]), ([T, F, E, T, T, F, T, F, E, E, F, T, F], [T, F, E, T, T, F, T, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_551 (And.intro z_553 (And.intro z_554 trivial)))

theorem z_556 : le (tf [T, F, E, T, T, F, T, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, T, E, E, F, F] [([E, F, T, T, T, F, T, F, T, E, E, F, F], [F, E, T, T, T, F, T, F, T, E, E, F, F]), ([T, F, E, T, T, F, T, F, E, T, E, F, F], [T, F, E, T, T, F, T, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_552 (And.intro z_555 trivial))

theorem z_557 : le (tf [T, T, F, F, E, F, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, T, F, E, T, F] [([T, T, F, F, E, F, E, T, E, F, T, T, F], [T, T, F, F, F, E, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_508 trivial)

theorem z_558 : le (tf [T, T, F, F, E, F, E, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, T, T, F, E, F] [([T, T, F, F, E, F, E, T, T, E, F, T, F], [T, T, F, F, E, F, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_557 trivial)

theorem z_559 : le (tf [T, T, F, F, F, E, E, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, E, F, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_560 : le (tf [T, T, F, F, E, F, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, F, E, T, T, F] [([T, T, F, F, E, F, E, E, F, T, T, T, F], [T, T, F, F, F, E, E, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_559 trivial)

theorem z_561 : le (tf [T, T, F, F, E, T, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, F, E, T, T, F] [([T, T, F, F, E, E, F, T, F, E, T, T, F], [T, T, F, F, E, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_560 trivial)

theorem z_562 : le (tf [T, T, F, F, E, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, T, F, E, T, F] [([T, T, F, F, E, E, F, T, T, F, E, T, F], [T, T, F, F, E, F, E, T, T, F, E, T, F]), ([T, T, F, F, E, T, F, E, E, F, T, T, F], [T, T, F, F, E, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_557 (And.intro z_561 trivial))

theorem z_563 : le (tf [T, T, F, F, E, T, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, T, T, F, E, F] [([T, T, F, F, E, E, F, T, T, T, F, E, F], [T, T, F, F, E, F, E, T, T, T, F, E, F]), ([T, T, F, F, E, T, F, E, T, E, F, T, F], [T, T, F, F, E, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_558 (And.intro z_562 trivial))

theorem z_564 : le (tf [T, T, F, F, E, T, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, E, F, E, T, F] [([T, T, F, F, E, T, E, F, T, F, E, T, F], [T, T, F, F, E, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 trivial)

theorem z_565 : le (tf [T, T, F, F, E, T, T, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, E, T, F, E, F] [([T, T, F, F, E, T, E, F, T, T, F, E, F], [T, T, F, F, E, T, F, E, T, T, F, E, F]), ([T, T, F, F, E, T, T, F, E, E, F, T, F], [T, T, F, F, E, T, T, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_563 (And.intro z_564 trivial))

theorem z_566 : le (tf [T, T, F, F, F, E, E, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, F, E, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_567 : le (tf [T, T, F, F, F, E, E, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, F, E, T, F, T] [([T, T, F, F, F, E, E, E, F, T, T, F, T], [T, T, F, F, F, E, E, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_566 trivial)

theorem z_568 : le (tf [T, T, F, F, F, E, E, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, T, F, E, F, T] [([T, T, F, F, F, E, E, T, E, F, T, F, T], [T, T, F, F, F, E, E, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_567 trivial)

theorem z_569 : le (tf [T, T, F, F, E, F, E, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, T, F, T, F, E] [([T, T, F, F, E, F, E, T, T, F, E, F, T], [T, T, F, F, F, E, E, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_568 trivial)

theorem z_570 : le (tf [T, T, F, F, F, F, E, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, E, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_571 : le (tf [T, T, F, F, F, E, F, E, T, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, T, E, T, F, T] [([T, T, F, F, F, E, F, E, E, T, T, F, T], [T, T, F, F, F, F, E, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_570 trivial)

theorem z_572 : le (tf [T, T, F, F, F, E, T, F, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, E, E, T, F, T] [([T, T, F, F, F, E, E, F, T, E, T, F, T], [T, T, F, F, F, E, F, E, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_571 trivial)

theorem z_573 : le (tf [T, T, F, F, F, T, E, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, F, E, T, F, T] [([T, T, F, F, F, E, T, E, F, E, T, F, T], [T, T, F, F, F, E, T, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_572 trivial)

theorem z_574 : le (tf [T, T, F, F, F, T, E, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, T, F, E, F, T] [([T, T, F, F, F, E, T, E, T, F, E, F, T], [T, T, F, F, F, E, T, F, T, E, E, F, T]), ([T, T, F, F, F, T, E, E, E, F, T, F, T], [T, T, F, F, F, T, E, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_480 (And.intro z_573 trivial))

theorem z_575 : le (tf [T, T, F, F, E, T, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, T, F, T, F, E] [([T, T, F, F, E, E, F, T, T, F, T, F, E], [T, T, F, F, E, F, E, T, T, F, T, F, E]), ([T, T, F, F, E, T, F, E, T, F, E, F, T], [T, T, F, F, F, T, E, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_569 (And.intro z_574 trivial))

theorem z_576 : le (tf [T, T, F, F, E, F, T, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, F, E, E, T, T, F] [([T, T, F, F, E, F, E, F, T, E, T, T, F], [T, T, F, F, F, E, E, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_507 trivial)

theorem z_577 : le (tf [T, T, F, F, T, F, E, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, F, E, T, T, F] [([T, T, F, F, E, F, T, E, F, E, T, T, F], [T, T, F, F, E, F, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_576 trivial)

theorem z_578 : le (tf [T, T, F, F, T, F, E, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, T, F, E, T, F] [([T, T, F, F, E, F, T, E, T, F, E, T, F], [T, T, F, F, E, F, T, F, T, E, E, T, F]), ([T, T, F, F, T, F, E, E, E, F, T, T, F], [T, T, F, F, T, F, E, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_499 (And.intro z_577 trivial))

theorem z_579 : le (tf [T, T, F, F, T, E, F, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, F, E, T, F, T, E, F] [([T, T, F, F, E, T, F, E, T, F, T, E, F], [T, T, F, F, E, T, F, E, T, F, T, F, E]), ([T, T, F, F, T, E, F, E, T, F, E, T, F], [T, T, F, F, T, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_575 (And.intro z_578 trivial))

theorem z_580 : le (tf [T, T, F, F, T, E, F, E, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, F, E, T, T, E, F, F] [([T, T, F, F, E, T, F, E, T, T, E, F, F], [T, T, F, F, E, T, F, E, T, T, F, E, F]), ([T, T, F, F, T, E, F, E, T, E, T, F, F], [T, T, F, F, T, E, F, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_563 (And.intro z_579 trivial))

theorem z_581 : le (tf [T, T, F, F, F, E, T, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, T, F, E, F, E, T] [([T, T, F, F, F, E, T, E, F, T, F, E, T], [T, T, F, F, F, E, T, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 trivial)

theorem z_582 : le (tf [T, T, F, F, E, F, T, T, F, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, F, E, F, T, E] [([T, T, F, F, E, F, T, E, F, T, F, T, E], [T, T, F, F, E, F, T, F, E, T, F, T, E]), ([T, T, F, F, E, F, T, T, F, E, F, E, T], [T, T, F, F, F, E, T, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_497 (And.intro z_581 trivial))

theorem z_583 : le (tf [T, T, F, F, E, F, T, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, F, E, T, E, F] [([T, T, F, F, E, F, T, E, F, T, T, E, F], [T, T, F, F, E, F, T, F, E, T, T, E, F]), ([T, T, F, F, E, F, T, T, F, E, E, T, F], [T, T, F, F, E, F, T, T, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_498 (And.intro z_582 trivial))

theorem z_584 : le (tf [T, T, F, F, T, F, F, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, F, E, F, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_585 : le (tf [T, T, F, F, T, F, F, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, F, E, E, F, T, E, T] [([T, T, F, F, T, F, F, E, E, F, E, T, T], [T, T, F, F, T, F, F, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_584 trivial)

theorem z_586 : le (tf [T, T, F, F, T, F, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, F, E, E, T, E, F, T] [([T, T, F, F, T, F, F, E, E, E, T, F, T], [T, T, F, F, T, F, F, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_585 trivial)

theorem z_587 : le (tf [T, T, F, F, T, F, E, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, F, T, E, E, F, T] [([T, T, F, F, E, F, T, F, T, E, E, F, T], [T, T, F, F, F, E, T, F, T, E, E, F, T]), ([T, T, F, F, T, F, E, F, E, T, E, F, T], [T, T, F, F, T, F, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_480 (And.intro z_586 trivial))

theorem z_588 : le (tf [T, T, F, F, T, F, E, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, T, F, T, F, E] [([T, T, F, F, E, F, T, E, T, F, T, F, E], [T, T, F, F, E, F, T, F, T, E, T, F, E]), ([T, T, F, F, T, F, E, E, T, F, E, F, T], [T, T, F, F, T, F, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_481 (And.intro z_587 trivial))

theorem z_589 : le (tf [T, T, F, F, T, F, F, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, F, E, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_590 : le (tf [T, T, F, F, T, F, E, F, E, T, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, F, E, T, E, T, F] [([T, T, F, F, E, F, T, F, E, T, E, T, F], [T, T, F, F, E, F, T, F, E, T, F, T, E]), ([T, T, F, F, T, F, E, F, E, E, T, T, F], [T, T, F, F, T, F, F, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_497 (And.intro z_589 trivial))

theorem z_591 : le (tf [T, T, F, F, T, F, E, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, T, F, E, E, T, F] [([T, T, F, F, E, F, T, T, F, E, E, T, F], [T, T, F, F, E, F, T, T, F, E, F, T, E]), ([T, T, F, F, T, F, E, E, F, T, E, T, F], [T, T, F, F, T, F, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_582 (And.intro z_590 trivial))

theorem z_592 : le (tf [T, T, F, F, T, F, E, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, T, E, F, T, E, F] [([T, T, F, F, E, F, T, T, E, F, T, E, F], [T, T, F, F, E, F, T, T, F, E, T, E, F]), ([T, T, F, F, T, F, E, E, T, F, T, E, F], [T, T, F, F, T, F, E, E, T, F, T, F, E]), ([T, T, F, F, T, F, E, T, E, F, E, T, F], [T, T, F, F, T, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_583 (And.intro z_588 (And.intro z_591 trivial)))

theorem z_593 : le (tf [T, T, F, F, T, F, T, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, T, E, E, E, T, F, F] [([T, T, F, F, T, F, E, T, E, E, T, F, F], [T, T, F, F, T, F, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_592 trivial)

theorem z_594 : le (tf [T, T, F, F, T, E, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, T, F, E, T, E, F, F] [([T, T, F, F, E, T, T, F, E, T, E, F, F], [T, T, F, F, E, T, T, F, E, T, F, E, F]), ([T, T, F, F, T, E, E, F, T, T, E, F, F], [T, T, F, F, T, E, F, E, T, T, E, F, F]), ([T, T, F, F, T, E, T, F, E, E, T, F, F], [T, T, F, F, T, F, T, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_565 (And.intro z_580 (And.intro z_593 trivial)))

theorem z_595 : le (tf [T, T, F, E, T, F, T, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, F, T, E, E, F, F] [([T, E, F, T, T, F, T, F, T, E, E, F, F], [T, F, E, T, T, F, T, F, T, E, E, F, F]), ([T, T, F, E, T, F, T, F, E, T, E, F, F], [T, T, F, F, T, E, T, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_556 (And.intro z_594 trivial))

theorem z_596 : le (tf [T, T, T, F, E, F, T, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, F, T, E, E, F, F] [([T, T, E, F, T, F, T, F, T, E, E, F, F], [T, T, F, E, T, F, T, F, T, E, E, F, F]), ([T, T, T, F, E, F, T, F, E, T, E, F, F], [T, T, T, F, F, E, T, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_595 (And.intro z_95 trivial))

theorem z_597 : le (tf [T, T, T, F, F, E, E, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, T, T, F, E, F, F] [([T, T, T, F, F, E, E, T, E, F, T, F, F], [T, T, T, F, F, E, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_538 trivial)

theorem z_598 : le (tf [T, T, T, F, E, F, T, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, E, T, F, E, F, F] [([T, T, E, F, T, F, T, E, T, F, E, F, F], [T, T, E, F, T, F, T, E, T, F, F, E, F]), ([T, T, T, F, E, F, E, T, T, F, E, F, F], [T, T, T, F, F, E, E, T, T, F, E, F, F]), ([T, T, T, F, E, F, T, E, E, F, T, F, F], [T, T, T, F, F, E, T, E, E, F, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_191 (And.intro z_597 (And.intro z_539 trivial)))

theorem z_599 : le (tf [T, T, T, F, T, F, E, E, E, F, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, E, E, F, T, F, F] [([T, T, T, F, E, F, T, E, E, F, T, F, F], [T, T, T, F, F, E, T, E, E, F, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_539 trivial)

theorem z_600 : le (tf [F, E, T, T, F, E, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, E, T, F, F] [([F, E, T, E, F, T, T, T, F, E, T, F, F], [F, E, T, E, F, T, T, T, F, F, T, E, F]), ([F, E, T, T, F, E, T, E, F, T, T, F, F], [F, E, T, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_370 (And.intro z_391 trivial))

theorem z_601 : le (tf [F, E, T, T, T, F, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, F, E, T, T, F, F] [([F, E, T, T, E, F, T, F, E, T, T, F, F], [F, E, T, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_391 trivial)

theorem z_602 : le (tf [F, E, T, T, T, F, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, T, F, E, T, F, F] [([F, E, T, T, E, F, T, T, F, E, T, F, F], [F, E, T, T, F, E, T, T, F, E, T, F, F]), ([F, E, T, T, T, F, E, E, F, T, T, F, F], [F, E, T, T, T, F, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_600 (And.intro z_601 trivial))

theorem z_603 : le (tf [F, E, T, T, T, F, E, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, T, T, F, E, F, F] [([F, E, T, T, E, F, T, T, T, F, E, F, F], [F, E, T, T, E, F, T, T, T, F, F, E, F]), ([F, E, T, T, T, F, E, T, E, F, T, F, F], [F, E, T, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_312 (And.intro z_602 trivial))

theorem z_604 : le (tf [F, E, T, T, T, F, F, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, E, F, T, E, F] [([F, E, T, T, T, F, F, E, T, F, T, E, F], [F, E, T, T, T, F, F, E, T, F, T, F, E]), ([F, E, T, T, T, F, F, T, E, F, E, T, F], [F, E, T, T, T, F, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_437 (And.intro z_424 trivial))

theorem z_605 : le (tf [F, E, T, T, T, F, F, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, E, T, E, F, F] [([F, E, T, T, T, F, F, E, T, T, E, F, F], [F, E, T, T, T, F, F, E, T, T, F, E, F]), ([F, E, T, T, T, F, F, T, E, E, T, F, F], [F, E, T, T, T, F, F, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_549 (And.intro z_604 trivial))

theorem z_606 : le (tf [F, E, T, T, T, F, T, E, F, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, E, F, F, T, E, F] [([F, E, T, T, T, F, E, T, F, F, T, E, F], [F, E, T, T, T, F, F, T, E, F, T, E, F]), ([F, E, T, T, T, F, T, E, F, F, E, T, F], [F, E, T, T, T, F, T, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_604 (And.intro z_550 trivial))

theorem z_607 : le (tf [F, E, T, T, T, F, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, E, F, T, E, F, F] [([F, E, T, T, T, F, E, T, F, T, E, F, F], [F, E, T, T, T, F, F, T, E, T, E, F, F]), ([F, E, T, T, T, F, T, E, F, E, T, F, F], [F, E, T, T, T, F, T, E, F, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_605 (And.intro z_606 trivial))

theorem z_608 : le (tf [F, E, T, T, T, F, T, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, E, T, E, F, F, F] [([F, E, T, T, T, F, E, T, T, E, F, F, F], [F, E, T, T, T, F, E, T, T, F, E, F, F]), ([F, E, T, T, T, F, T, E, E, T, F, F, F], [F, E, T, T, T, F, T, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_603 (And.intro z_607 trivial))

theorem z_609 : le (tf [T, F, E, T, F, E, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, E, T, F, F] [([E, F, T, T, F, E, T, T, F, E, T, F, F], [F, E, T, T, F, E, T, T, F, E, T, F, F]), ([T, F, E, E, F, T, T, T, F, E, T, F, F], [T, F, E, E, F, T, T, T, F, F, T, E, F]), ([T, F, E, T, F, E, T, E, F, T, T, F, F], [T, F, E, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_600 (And.intro z_374 (And.intro z_399 trivial)))

theorem z_610 : le (tf [T, F, E, T, T, F, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, F, E, T, T, F, F] [([E, F, T, T, T, F, E, F, E, T, T, F, F], [F, E, T, T, T, F, E, F, E, T, T, F, F]), ([T, F, E, T, E, F, T, F, E, T, T, F, F], [T, F, E, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_601 (And.intro z_399 trivial))

theorem z_611 : le (tf [T, F, E, T, T, F, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, T, F, E, T, F, F] [([E, F, T, T, T, F, E, T, F, E, T, F, F], [F, E, T, T, T, F, E, T, F, E, T, F, F]), ([T, F, E, T, E, F, T, T, F, E, T, F, F], [T, F, E, T, F, E, T, T, F, E, T, F, F]), ([T, F, E, T, T, F, E, E, F, T, T, F, F], [T, F, E, T, T, F, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_602 (And.intro z_609 (And.intro z_610 trivial)))

theorem z_612 : le (tf [T, F, E, T, T, F, E, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, T, T, F, E, F, F] [([E, F, T, T, T, F, E, T, T, F, E, F, F], [F, E, T, T, T, F, E, T, T, F, E, F, F]), ([T, F, E, T, E, F, T, T, T, F, E, F, F], [T, F, E, T, E, F, T, T, T, F, F, E, F]), ([T, F, E, T, T, F, E, T, E, F, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_603 (And.intro z_315 (And.intro z_611 trivial)))

theorem z_613 : le (tf [T, F, E, T, T, F, F, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, E, F, T, E, F] [([E, F, T, T, T, F, F, T, E, F, T, E, F], [F, E, T, T, T, F, F, T, E, F, T, E, F]), ([T, F, E, T, T, F, F, E, T, F, T, E, F], [T, F, E, T, T, F, F, E, T, F, T, F, E]), ([T, F, E, T, T, F, F, T, E, F, E, T, F], [T, F, E, T, T, F, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_604 (And.intro z_439 (And.intro z_428 trivial)))

theorem z_614 : le (tf [T, F, E, T, T, F, F, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, E, T, E, F, F] [([E, F, T, T, T, F, F, T, E, T, E, F, F], [F, E, T, T, T, F, F, T, E, T, E, F, F]), ([T, F, E, T, T, F, F, E, T, T, E, F, F], [T, F, E, T, T, F, F, E, T, T, F, E, F]), ([T, F, E, T, T, F, F, T, E, E, T, F, F], [T, F, E, T, T, F, F, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_605 (And.intro z_553 (And.intro z_613 trivial)))

theorem z_615 : le (tf [E, F, T, T, T, F, T, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, T, F, E, F, T, E, F] [([E, F, T, T, T, F, E, F, T, F, T, E, F], [E, F, T, T, T, F, F, E, T, F, T, E, F]), ([E, F, T, T, T, F, T, F, E, F, E, T, F], [F, E, T, T, T, F, T, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_446 (And.intro z_550 trivial))

theorem z_616 : le (tf [F, F, E, E, T, T, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_617 : le (tf [F, F, E, E, T, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, T, F, T, F, E] [([F, F, E, E, T, T, T, F, T, F, E, F, T], [F, F, E, E, T, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_616 trivial)

theorem z_618 : le (tf [F, E, F, T, E, T, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, F, T, F, F, E, T] [([F, E, F, E, T, T, T, F, T, F, F, E, T], [F, F, E, E, T, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_616 trivial)

theorem z_619 : le (tf [F, E, F, T, E, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, F, T, F, T, F, E] [([F, E, F, E, T, T, T, F, T, F, T, F, E], [F, F, E, E, T, T, T, F, T, F, T, F, E]), ([F, E, F, T, E, T, T, F, T, F, E, F, T], [F, E, F, T, E, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_617 (And.intro z_618 trivial))

theorem z_620 : le (tf [F, F, E, E, F, E, T, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, T, T, T, F, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_621 : le (tf [F, F, E, E, T, F, E, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, E, T, T, F, T, F, T] [([F, F, E, E, E, F, T, T, T, F, T, F, T], [F, F, E, E, F, E, T, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_620 trivial)

theorem z_622 : le (tf [F, F, E, E, T, T, F, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, F, E, T, F, T, F, T] [([F, F, E, E, T, E, F, T, T, F, T, F, T], [F, F, E, E, T, F, E, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_621 trivial)

theorem z_623 : le (tf [F, F, E, E, T, T, T, F, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, E, F, T, F, T] [([F, F, E, E, T, T, E, F, T, F, T, F, T], [F, F, E, E, T, T, F, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_622 trivial)

theorem z_624 : le (tf [F, E, F, E, T, T, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, T, F, E, F, T] [([F, E, F, E, T, T, T, F, E, F, T, F, T], [F, F, E, E, T, T, T, F, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_623 trivial)

theorem z_625 : le (tf [F, E, F, E, T, T, T, F, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, F, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_626 : le (tf [F, E, T, F, E, T, T, F, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, F, E, T, F, T] [([F, E, E, F, T, T, T, F, F, E, T, F, T], [F, E, F, E, T, T, T, F, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_625 trivial)

theorem z_627 : le (tf [F, E, T, F, E, T, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, T, F, E, F, T] [([F, E, E, F, T, T, T, F, T, F, E, F, T], [F, E, F, E, T, T, T, F, T, F, E, F, T]), ([F, E, T, F, E, T, T, F, E, F, T, F, T], [F, E, T, F, E, T, T, F, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_624 (And.intro z_626 trivial))

theorem z_628 : le (tf [F, E, T, E, F, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, F, T, F, T, F, E] [([F, E, E, T, F, T, T, F, T, F, T, F, E], [F, E, F, T, E, T, T, F, T, F, T, F, E]), ([F, E, T, E, F, T, T, F, T, F, E, F, T], [F, E, T, F, E, T, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_619 (And.intro z_627 trivial))

theorem z_629 : le (tf [F, E, T, T, F, F, E, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, F, E, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_630 : le (tf [F, E, T, T, F, F, E, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, F, E, T, F, T] [([F, E, T, T, F, F, E, E, F, T, T, F, T], [F, E, T, T, F, F, E, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_629 trivial)

theorem z_631 : le (tf [F, E, T, T, F, F, T, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, T, E, E, F, T, F, T] [([F, E, T, T, F, F, E, T, E, F, T, F, T], [F, E, T, T, F, F, E, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_630 trivial)

theorem z_632 : le (tf [F, E, T, T, F, E, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, T, F, E, F, T] [([F, E, T, E, F, T, T, F, T, F, E, F, T], [F, E, T, F, E, T, T, F, T, F, E, F, T]), ([F, E, T, T, F, E, T, F, E, F, T, F, T], [F, E, T, T, F, F, T, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_627 (And.intro z_631 trivial))

theorem z_633 : le (tf [E, F, T, T, F, E, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, F, T, F, T, F, E] [([E, F, T, E, F, T, T, F, T, F, T, F, E], [F, E, T, E, F, T, T, F, T, F, T, F, E]), ([E, F, T, T, F, E, T, F, T, F, E, F, T], [F, E, T, T, F, E, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_628 (And.intro z_632 trivial))

theorem z_634 : le (tf [F, F, F, E, E, F, E, T, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, E, T, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_635 : le (tf [F, F, F, E, E, T, F, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, F, E, T, T, T, F, T] [([F, F, F, E, E, E, F, T, T, T, T, F, T], [F, F, F, E, E, F, E, T, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_634 trivial)

theorem z_636 : le (tf [F, F, F, E, E, T, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, F, E, T, T, F, T] [([F, F, F, E, E, T, E, F, T, T, T, F, T], [F, F, F, E, E, T, F, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_635 trivial)

theorem z_637 : le (tf [F, F, F, E, E, T, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, T, F, E, T, F, T] [([F, F, F, E, E, T, T, E, F, T, T, F, T], [F, F, F, E, E, T, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_636 trivial)

theorem z_638 : le (tf [F, F, F, E, E, T, T, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, T, T, F, E, F, T] [([F, F, F, E, E, T, T, T, E, F, T, F, T], [F, F, F, E, E, T, T, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_637 trivial)

theorem z_639 : le (tf [F, F, E, F, E, T, T, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, T, F, T, F, E] [([F, F, E, F, E, T, T, T, T, F, E, F, T], [F, F, F, E, E, T, T, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_638 trivial)

theorem z_640 : le (tf [F, F, E, F, E, T, T, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_641 : le (tf [F, F, E, T, F, E, T, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, T, F, F, E, T] [([F, F, E, E, F, T, T, T, T, F, F, E, T], [F, F, E, F, E, T, T, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_640 trivial)

theorem z_642 : le (tf [F, F, E, T, F, E, T, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, T, F, T, F, E] [([F, F, E, E, F, T, T, T, T, F, T, F, E], [F, F, E, F, E, T, T, T, T, F, T, F, E]), ([F, F, E, T, F, E, T, T, T, F, E, F, T], [F, F, E, T, F, E, T, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_639 (And.intro z_641 trivial))

theorem z_643 : le (tf [F, F, T, E, E, F, T, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, T, T, F, F, E, T] [([F, F, E, T, E, F, T, T, T, F, F, E, T], [F, F, E, T, F, E, T, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_641 trivial)

theorem z_644 : le (tf [F, F, T, E, E, F, T, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, T, T, F, T, F, E] [([F, F, E, T, E, F, T, T, T, F, T, F, E], [F, F, E, T, F, E, T, T, T, F, T, F, E]), ([F, F, T, E, E, F, T, T, T, F, E, F, T], [F, F, T, E, E, F, T, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_642 (And.intro z_643 trivial))

theorem z_645 : le (tf [F, E, T, F, T, F, E, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, T, T, F, F, E, T] [([F, E, T, F, E, F, T, T, T, F, F, E, T], [F, F, T, E, E, F, T, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_643 trivial)

theorem z_646 : le (tf [F, E, T, F, T, F, E, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, T, T, F, T, F, E] [([F, E, T, F, E, F, T, T, T, F, T, F, E], [F, F, T, E, E, F, T, T, T, F, T, F, E]), ([F, E, T, F, T, F, E, T, T, F, E, F, T], [F, E, T, F, T, F, E, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_644 (And.intro z_645 trivial))

theorem z_647 : le (tf [F, F, F, E, E, F, E, T, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, E, T, T, F, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_648 : le (tf [F, F, F, E, E, T, F, E, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, F, E, T, F, T, T, T] [([F, F, F, E, E, E, F, T, T, F, T, T, T], [F, F, F, E, E, F, E, T, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_647 trivial)

theorem z_649 : le (tf [F, F, F, E, E, T, T, F, E, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, F, E, F, T, T, T] [([F, F, F, E, E, T, E, F, T, F, T, T, T], [F, F, F, E, E, T, F, E, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_648 trivial)

theorem z_650 : le (tf [F, F, E, F, E, T, T, F, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, F, T, F, E, T, T] [([F, F, E, F, E, T, T, F, E, F, T, T, T], [F, F, F, E, E, T, T, F, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_649 trivial)

theorem z_651 : le (tf [F, F, E, F, E, T, T, F, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, F, T, T, F, E, T] [([F, F, E, F, E, T, T, F, T, E, F, T, T], [F, F, E, F, E, T, T, F, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_650 trivial)

theorem z_652 : le (tf [F, F, F, F, E, F, E, E, T, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, F, E, E, T, T, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_653 : le (tf [F, F, F, F, E, E, F, T, E, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, F, T, E, T, T, T, T] [([F, F, F, F, E, E, F, E, T, T, T, T, T], [F, F, F, F, E, F, E, E, T, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_652 trivial)

theorem z_654 : le (tf [F, F, F, F, E, E, T, E, F, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, T, E, F, T, T, T, T] [([F, F, F, F, E, E, E, T, F, T, T, T, T], [F, F, F, F, E, E, F, T, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_653 trivial)

theorem z_655 : le (tf [F, F, F, E, F, E, T, T, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, T, T, F, E, T, T, T] [([F, F, F, E, F, E, T, E, F, T, T, T, T], [F, F, F, F, E, E, T, E, F, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_654 trivial)

theorem z_656 : le (tf [F, F, F, F, E, E, E, F, T, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, E, F, T, T, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_657 : le (tf [F, F, F, E, F, E, T, F, E, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, T, F, E, T, T, T, T] [([F, F, F, E, F, E, E, F, T, T, T, T, T], [F, F, F, F, E, E, E, F, T, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_656 trivial)

theorem z_658 : le (tf [F, F, F, E, T, F, E, F, E, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, F, E, F, E, T, T, T, T] [([F, F, F, E, E, F, T, F, E, T, T, T, T], [F, F, F, E, F, E, T, F, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_657 trivial)

theorem z_659 : le (tf [F, F, F, E, T, F, E, T, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, F, E, T, F, E, T, T, T] [([F, F, F, E, E, F, T, T, F, E, T, T, T], [F, F, F, E, F, E, T, T, F, E, T, T, T]), ([F, F, F, E, T, F, E, E, F, T, T, T, T], [F, F, F, E, T, F, E, F, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_655 (And.intro z_658 trivial))

theorem z_660 : le (tf [F, F, F, E, T, F, T, E, E, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, F, T, E, E, F, T, T, T] [([F, F, F, E, T, F, E, T, E, F, T, T, T], [F, F, F, E, T, F, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_659 trivial)

theorem z_661 : le (tf [F, F, F, F, E, E, E, T, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, E, T, T, F, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_662 : le (tf [F, F, F, E, F, E, T, E, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, T, E, T, F, T, T, T] [([F, F, F, E, F, E, E, T, T, F, T, T, T], [F, F, F, F, E, E, E, T, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_661 trivial)

theorem z_663 : le (tf [F, F, F, E, T, F, E, E, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, F, E, E, T, F, T, T, T] [([F, F, F, E, E, F, T, E, T, F, T, T, T], [F, F, F, E, F, E, T, E, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_662 trivial)

theorem z_664 : le (tf [F, F, F, T, E, E, F, E, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, T, E, E, F, E, T, F, T, T, T] [([F, F, F, E, T, E, F, E, T, F, T, T, T], [F, F, F, E, T, F, E, E, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_663 trivial)

theorem z_665 : le (tf [F, F, F, T, E, E, T, F, E, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, T, E, E, T, F, E, F, T, T, T] [([F, F, F, E, T, E, T, F, E, F, T, T, T], [F, F, F, E, T, F, T, E, E, F, T, T, T]), ([F, F, F, T, E, E, E, F, T, F, T, T, T], [F, F, F, T, E, E, F, E, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_660 (And.intro z_664 trivial))

theorem z_666 : le (tf [F, F, E, T, F, E, T, F, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, F, T, F, E, T, T] [([F, F, E, E, F, T, T, F, T, F, E, T, T], [F, F, E, F, E, T, T, F, T, F, E, T, T]), ([F, F, E, T, F, E, T, F, E, F, T, T, T], [F, F, F, T, E, E, T, F, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_650 (And.intro z_665 trivial))

theorem z_667 : le (tf [F, F, E, T, F, E, T, F, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, F, T, T, F, E, T] [([F, F, E, E, F, T, T, F, T, T, F, E, T], [F, F, E, F, E, T, T, F, T, T, F, E, T]), ([F, F, E, T, F, E, T, F, T, E, F, T, T], [F, F, E, T, F, E, T, F, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_651 (And.intro z_666 trivial))

theorem z_668 : le (tf [F, F, F, E, E, F, T, T, F, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, T, T, F, T, E, T, T] [([F, F, F, E, E, F, T, T, F, E, T, T, T], [F, F, F, E, F, E, T, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_655 trivial)

theorem z_669 : le (tf [F, F, E, F, T, F, E, T, F, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, T, F, E, T, F, T, E, T, T] [([F, F, E, F, E, F, T, T, F, T, E, T, T], [F, F, F, E, E, F, T, T, F, T, E, T, T]), ([F, F, E, F, T, F, E, T, F, E, T, T, T], [F, F, F, E, T, F, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_668 (And.intro z_659 trivial))

theorem z_670 : le (tf [F, F, E, F, T, F, T, E, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, T, F, T, E, E, T, F, T, T] [([F, F, E, F, T, F, E, T, E, T, F, T, T], [F, F, E, F, T, F, E, T, F, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_669 trivial)

theorem z_671 : le (tf [F, F, F, E, F, E, E, T, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, E, T, T, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_672 : le (tf [F, F, F, E, E, F, T, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, T, E, T, T, F, T, T] [([F, F, F, E, E, F, E, T, T, T, F, T, T], [F, F, F, E, F, E, E, T, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_671 trivial)

theorem z_673 : le (tf [F, F, E, F, T, F, E, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, T, F, E, E, T, T, F, T, T] [([F, F, E, F, E, F, T, E, T, T, F, T, T], [F, F, F, E, E, F, T, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_672 trivial)

theorem z_674 : le (tf [F, F, T, F, E, E, F, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, E, E, F, E, T, T, F, T, T] [([F, F, E, F, T, E, F, E, T, T, F, T, T], [F, F, E, F, T, F, E, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_673 trivial)

theorem z_675 : le (tf [F, F, T, F, E, E, T, F, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, E, E, T, F, E, T, F, T, T] [([F, F, E, F, T, E, T, F, E, T, F, T, T], [F, F, E, F, T, F, T, E, E, T, F, T, T]), ([F, F, T, F, E, E, E, F, T, T, F, T, T], [F, F, T, F, E, E, F, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_670 (And.intro z_674 trivial))

theorem z_676 : le (tf [F, F, T, E, F, E, T, F, T, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, E, F, E, T, F, T, E, F, T, T] [([F, F, E, T, F, E, T, F, T, E, F, T, T], [F, F, E, T, F, E, T, F, T, F, E, T, T]), ([F, F, T, E, F, E, T, F, E, T, F, T, T], [F, F, T, F, E, E, T, F, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_666 (And.intro z_675 trivial))

theorem z_677 : le (tf [F, F, T, E, E, F, T, F, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, F, T, T, F, E, T] [([F, F, E, T, E, F, T, F, T, T, F, E, T], [F, F, E, T, F, E, T, F, T, T, F, E, T]), ([F, F, T, E, E, F, T, F, T, E, F, T, T], [F, F, T, E, F, E, T, F, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_667 (And.intro z_676 trivial))

theorem z_678 : le (tf [F, F, E, T, T, F, F, F, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, F, F, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_679 : le (tf [F, F, E, T, T, F, F, E, F, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, F, E, F, T, E, T, T] [([F, F, E, T, T, F, F, E, F, E, T, T, T], [F, F, E, T, T, F, F, F, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_678 trivial)

theorem z_680 : le (tf [F, F, E, T, T, F, F, E, T, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, F, E, T, E, F, T, T] [([F, F, E, T, T, F, F, E, E, T, F, T, T], [F, F, E, T, T, F, F, E, F, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_679 trivial)

theorem z_681 : le (tf [F, F, F, E, T, T, F, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, T, F, E, F, E, T, T, T] [([F, F, F, E, T, E, F, T, F, E, T, T, T], [F, F, F, E, T, F, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_659 trivial)

theorem z_682 : le (tf [F, F, E, F, T, T, F, E, F, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, T, T, F, E, F, T, E, T, T] [([F, F, E, F, T, E, F, T, F, T, E, T, T], [F, F, E, F, T, F, E, T, F, T, E, T, T]), ([F, F, E, F, T, T, F, E, F, E, T, T, T], [F, F, F, E, T, T, F, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_669 (And.intro z_681 trivial))

theorem z_683 : le (tf [F, F, T, F, F, E, E, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, F, E, E, E, T, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_684 : le (tf [F, F, T, F, E, F, E, T, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, E, F, E, T, E, T, F, T, T] [([F, F, E, F, T, F, E, T, E, T, F, T, T], [F, F, E, F, T, F, E, T, F, T, E, T, T]), ([F, F, T, F, E, F, E, E, T, T, F, T, T], [F, F, T, F, F, E, E, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_669 (And.intro z_683 trivial))

theorem z_685 : le (tf [F, F, T, F, E, T, F, E, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, E, T, F, E, E, T, F, T, T] [([F, F, E, F, T, T, F, E, E, T, F, T, T], [F, F, E, F, T, T, F, E, F, T, E, T, T]), ([F, F, T, F, E, E, F, T, E, T, F, T, T], [F, F, T, F, E, F, E, T, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_682 (And.intro z_684 trivial))

theorem z_686 : le (tf [F, F, T, F, T, E, E, F, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, T, E, E, F, E, T, F, T, T] [([F, F, T, F, E, T, E, F, E, T, F, T, T], [F, F, T, F, E, T, F, E, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_685 trivial)

theorem z_687 : le (tf [F, F, T, E, T, F, E, F, T, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, E, T, F, E, F, T, E, F, T, T] [([F, F, E, T, T, F, E, F, T, E, F, T, T], [F, F, E, T, T, F, F, E, T, E, F, T, T]), ([F, F, T, E, E, F, T, F, T, E, F, T, T], [F, F, T, E, F, E, T, F, T, E, F, T, T]), ([F, F, T, E, T, F, E, F, E, T, F, T, T], [F, F, T, F, T, E, E, F, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_680 (And.intro z_676 (And.intro z_686 trivial)))

theorem z_688 : le (tf [F, E, T, F, T, F, E, F, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, F, T, T, F, E, T] [([F, E, T, F, E, F, T, F, T, T, F, E, T], [F, F, T, E, E, F, T, F, T, T, F, E, T]), ([F, E, T, F, T, F, E, F, T, E, F, T, T], [F, F, T, E, T, F, E, F, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_677 (And.intro z_687 trivial))

theorem z_689 : le (tf [F, E, T, F, T, F, T, F, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, T, F, E, E, F, T, T] [([F, E, T, F, T, F, E, F, T, E, F, T, T], [F, F, T, E, T, F, E, F, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_687 trivial)

theorem z_690 : le (tf [E, F, T, F, T, F, T, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, T, F, E, T, F, E, T] [([E, F, T, F, T, F, E, F, T, T, F, E, T], [F, E, T, F, T, F, E, F, T, T, F, E, T]), ([E, F, T, F, T, F, T, F, E, E, F, T, T], [F, E, T, F, T, F, T, F, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_688 (And.intro z_689 trivial))

theorem z_691 : le (tf [E, F, T, F, T, F, T, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, T, F, T, E, E, F, T] [([E, F, T, F, T, F, T, F, E, T, E, F, T], [E, F, T, F, T, F, T, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_690 trivial)

theorem z_692 : le (tf [E, F, T, F, T, F, T, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, T, E, T, F, T, F, E] [([E, F, T, F, T, F, E, T, T, F, T, F, E], [F, E, T, F, T, F, E, T, T, F, T, F, E]), ([E, F, T, F, T, F, T, E, T, F, E, F, T], [E, F, T, F, T, F, T, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_646 (And.intro z_691 trivial))

theorem z_693 : le (tf [T, F, F, E, E, T, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_694 : le (tf [T, F, F, E, E, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, T, F, T, F, E] [([T, F, F, E, E, T, T, F, T, F, E, F, T], [T, F, F, E, E, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_693 trivial)

theorem z_695 : le (tf [T, F, F, F, E, F, E, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, E, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_696 : le (tf [T, F, F, F, E, E, F, T, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, F, T, E, T, T, F, T] [([T, F, F, F, E, E, F, E, T, T, T, F, T], [T, F, F, F, E, F, E, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_695 trivial)

theorem z_697 : le (tf [T, F, F, F, E, E, T, E, F, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, E, F, T, T, F, T] [([T, F, F, F, E, E, E, T, F, T, T, F, T], [T, F, F, F, E, E, F, T, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_696 trivial)

theorem z_698 : le (tf [T, F, F, E, F, E, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, F, E, T, F, T] [([T, F, F, E, F, E, T, E, F, T, T, F, T], [T, F, F, F, E, E, T, E, F, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_697 trivial)

theorem z_699 : le (tf [T, F, F, F, E, E, E, F, T, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, E, F, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_700 : le (tf [T, F, F, E, F, E, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, F, E, T, T, F, T] [([T, F, F, E, F, E, E, F, T, T, T, F, T], [T, F, F, F, E, E, E, F, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_699 trivial)

theorem z_701 : le (tf [T, F, F, E, T, F, E, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, F, E, T, T, F, T] [([T, F, F, E, E, F, T, F, E, T, T, F, T], [T, F, F, E, F, E, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_700 trivial)

theorem z_702 : le (tf [T, F, F, E, T, F, E, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, F, E, T, F, T] [([T, F, F, E, E, F, T, T, F, E, T, F, T], [T, F, F, E, F, E, T, T, F, E, T, F, T]), ([T, F, F, E, T, F, E, E, F, T, T, F, T], [T, F, F, E, T, F, E, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_698 (And.intro z_701 trivial))

theorem z_703 : le (tf [T, F, F, E, T, F, T, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, T, E, E, F, T, F, T] [([T, F, F, E, T, F, E, T, E, F, T, F, T], [T, F, F, E, T, F, E, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_702 trivial)

theorem z_704 : le (tf [T, F, F, E, T, E, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, E, T, F, T, F, E, F, T] [([T, F, F, E, E, T, T, F, T, F, E, F, T], [T, F, F, E, E, T, T, F, T, F, F, E, T]), ([T, F, F, E, T, E, T, F, E, F, T, F, T], [T, F, F, E, T, F, T, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_693 (And.intro z_703 trivial))

theorem z_705 : le (tf [T, F, E, F, T, E, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, F, T, E, T, F, T, F, T, F, E] [([E, F, T, F, T, E, T, F, T, F, T, F, E], [E, F, T, F, T, F, T, E, T, F, T, F, E]), ([T, F, E, F, E, T, T, F, T, F, T, F, E], [T, F, F, E, E, T, T, F, T, F, T, F, E]), ([T, F, E, F, T, E, T, F, T, F, E, F, T], [T, F, F, E, T, E, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_692 (And.intro z_694 (And.intro z_704 trivial)))

theorem z_706 : le (tf [T, F, F, E, E, F, E, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, E, F, E, T, T, F, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_707 : le (tf [T, F, F, E, E, T, F, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, F, E, T, F, T, F, T] [([T, F, F, E, E, E, F, T, T, F, T, F, T], [T, F, F, E, E, F, E, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_706 trivial)

theorem z_708 : le (tf [T, F, F, E, E, T, T, F, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, E, F, T, F, T] [([T, F, F, E, E, T, E, F, T, F, T, F, T], [T, F, F, E, E, T, F, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_707 trivial)

theorem z_709 : le (tf [T, F, E, F, E, T, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, T, F, E, F, T] [([E, F, T, F, E, T, T, F, T, F, E, F, T], [F, E, T, F, E, T, T, F, T, F, E, F, T]), ([T, F, E, F, E, T, T, F, E, F, T, F, T], [T, F, F, E, E, T, T, F, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_627 (And.intro z_708 trivial))

theorem z_710 : le (tf [T, F, F, F, E, E, E, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, E, T, T, F, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_711 : le (tf [T, F, F, E, F, E, T, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, E, T, F, T, F, T] [([T, F, F, E, F, E, E, T, T, F, T, F, T], [T, F, F, F, E, E, E, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_710 trivial)

theorem z_712 : le (tf [T, F, F, E, T, F, E, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, E, T, F, T, F, T] [([T, F, F, E, E, F, T, E, T, F, T, F, T], [T, F, F, E, F, E, T, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_711 trivial)

theorem z_713 : le (tf [T, F, F, T, E, E, F, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, E, T, F, T, F, T] [([T, F, F, E, T, E, F, E, T, F, T, F, T], [T, F, F, E, T, F, E, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_712 trivial)

theorem z_714 : le (tf [T, F, F, T, E, E, T, F, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, T, F, E, F, T, F, T] [([T, F, F, E, T, E, T, F, E, F, T, F, T], [T, F, F, E, T, F, T, E, E, F, T, F, T]), ([T, F, F, T, E, E, E, F, T, F, T, F, T], [T, F, F, T, E, E, F, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_703 (And.intro z_713 trivial))

theorem z_715 : le (tf [T, F, E, T, F, E, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, T, F, E, F, T] [([E, F, T, T, F, E, T, F, T, F, E, F, T], [F, E, T, T, F, E, T, F, T, F, E, F, T]), ([T, F, E, E, F, T, T, F, T, F, E, F, T], [T, F, E, F, E, T, T, F, T, F, E, F, T]), ([T, F, E, T, F, E, T, F, E, F, T, F, T], [T, F, F, T, E, E, T, F, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_632 (And.intro z_709 (And.intro z_714 trivial)))

theorem z_716 : le (tf [T, F, E, T, E, F, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, E, F, T, F, T, F, T, F, E] [([E, F, T, T, E, F, T, F, T, F, T, F, E], [E, F, T, T, F, E, T, F, T, F, T, F, E]), ([T, F, E, E, T, F, T, F, T, F, T, F, E], [T, F, E, F, T, E, T, F, T, F, T, F, E]), ([T, F, E, T, E, F, T, F, T, F, E, F, T], [T, F, E, T, F, E, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_633 (And.intro z_705 (And.intro z_715 trivial)))

theorem z_717 : le (tf [T, F, E, T, T, F, E, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, F, T, F, T, E, F] [([E, F, T, T, T, F, E, F, T, F, T, E, F], [E, F, T, T, T, F, F, E, T, F, T, E, F]), ([T, F, E, T, E, F, T, F, T, F, T, E, F], [T, F, E, T, E, F, T, F, T, F, T, F, E]), ([T, F, E, T, T, F, E, F, T, F, E, T, F], [T, F, E, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_446 (And.intro z_716 (And.intro z_449 trivial)))

theorem z_718 : le (tf [T, F, E, T, T, F, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, E, E, T, F, F] [([E, F, T, T, T, F, T, F, E, E, T, F, F], [E, F, T, T, T, F, T, F, E, F, T, E, F]), ([T, F, E, T, T, F, E, F, T, E, T, F, F], [T, F, E, T, T, F, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_615 (And.intro z_717 trivial))

theorem z_719 : le (tf [T, F, E, T, T, F, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, E, F, T, E, F, F] [([E, F, T, T, T, F, T, E, F, T, E, F, F], [F, E, T, T, T, F, T, E, F, T, E, F, F]), ([T, F, E, T, T, F, E, T, F, T, E, F, F], [T, F, E, T, T, F, F, T, E, T, E, F, F]), ([T, F, E, T, T, F, T, E, F, E, T, F, F], [T, F, E, T, T, F, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_607 (And.intro z_614 (And.intro z_718 trivial)))

theorem z_720 : le (tf [T, F, E, T, T, F, T, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, E, T, E, F, F, F] [([E, F, T, T, T, F, T, E, T, E, F, F, F], [F, E, T, T, T, F, T, E, T, E, F, F, F]), ([T, F, E, T, T, F, E, T, T, E, F, F, F], [T, F, E, T, T, F, E, T, T, F, E, F, F]), ([T, F, E, T, T, F, T, E, E, T, F, F, F], [T, F, E, T, T, F, T, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_608 (And.intro z_612 (And.intro z_719 trivial)))

theorem z_721 : le (tf [T, T, F, E, F, E, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, T, F, E, T, F, F] [([T, E, F, T, F, E, T, T, F, E, T, F, F], [T, F, E, T, F, E, T, T, F, E, T, F, F]), ([T, T, F, E, F, E, T, E, F, T, T, F, F], [T, T, F, F, E, E, T, E, F, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_609 (And.intro z_469 trivial))

theorem z_722 : le (tf [T, T, F, E, F, E, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, F, E, T, T, F, F] [([T, E, F, T, F, E, T, F, E, T, T, F, F], [T, F, E, T, F, E, T, F, E, T, T, F, F]), ([T, T, F, E, F, E, E, F, T, T, T, F, F], [T, T, F, F, E, E, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 (And.intro z_513 trivial))

theorem z_723 : le (tf [T, T, F, E, T, F, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, F, E, T, T, F, F] [([T, E, F, T, T, F, E, F, E, T, T, F, F], [T, F, E, T, T, F, E, F, E, T, T, F, F]), ([T, T, F, E, E, F, T, F, E, T, T, F, F], [T, T, F, E, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_610 (And.intro z_722 trivial))

theorem z_724 : le (tf [T, T, F, E, T, F, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, T, F, E, T, F, F] [([T, E, F, T, T, F, E, T, F, E, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F]), ([T, T, F, E, E, F, T, T, F, E, T, F, F], [T, T, F, E, F, E, T, T, F, E, T, F, F]), ([T, T, F, E, T, F, E, E, F, T, T, F, F], [T, T, F, E, T, F, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_611 (And.intro z_721 (And.intro z_723 trivial)))

theorem z_725 : le (tf [T, T, F, E, T, F, E, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, T, T, F, E, F, F] [([T, E, F, T, T, F, E, T, T, F, E, F, F], [T, F, E, T, T, F, E, T, T, F, E, F, F]), ([T, T, F, E, E, F, T, T, T, F, E, F, F], [T, T, F, E, E, F, T, T, T, F, F, E, F]), ([T, T, F, E, T, F, E, T, E, F, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_612 (And.intro z_462 (And.intro z_724 trivial)))

theorem z_726 : le (tf [T, T, F, F, F, E, F, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, T, E, E, F, T, T] [([T, T, F, F, F, E, F, E, T, E, F, T, T], [T, T, F, F, F, F, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_472 trivial)

theorem z_727 : le (tf [T, T, F, F, F, E, E, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, F, T, F, E, T] [([T, T, F, F, F, E, E, T, F, E, F, T, T], [T, T, F, F, F, E, F, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_726 trivial)

theorem z_728 : le (tf [T, T, F, F, E, F, E, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, F, T, F, T, E] [([T, T, F, F, E, F, E, T, F, T, F, E, T], [T, T, F, F, F, E, E, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_727 trivial)

theorem z_729 : le (tf [T, T, F, F, F, T, E, F, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, F, E, E, F, T, T] [([T, T, F, F, F, E, T, F, E, E, F, T, T], [T, T, F, F, F, E, T, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_477 trivial)

theorem z_730 : le (tf [T, T, F, F, F, T, E, E, F, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, F, T, F, E, T] [([T, T, F, F, F, E, T, E, F, T, F, E, T], [T, T, F, F, F, E, T, F, E, T, F, E, T]), ([T, T, F, F, F, T, E, E, F, E, F, T, T], [T, T, F, F, F, T, E, F, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 (And.intro z_729 trivial))

theorem z_731 : le (tf [T, T, F, F, E, T, F, E, F, T, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, F, T, F, T, E] [([T, T, F, F, E, E, F, T, F, T, F, T, E], [T, T, F, F, E, F, E, T, F, T, F, T, E]), ([T, T, F, F, E, T, F, E, F, T, F, E, T], [T, T, F, F, F, T, E, E, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_728 (And.intro z_730 trivial))

theorem z_732 : le (tf [T, T, F, F, E, T, F, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, T, F, E, E, T, F] [([T, T, F, F, E, T, F, E, F, T, E, T, F], [T, T, F, F, E, T, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_731 trivial)

theorem z_733 : le (tf [T, T, F, F, E, T, F, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, T, E, F, T, E, F] [([T, T, F, F, E, T, F, E, T, F, T, E, F], [T, T, F, F, E, T, F, E, T, F, T, F, E]), ([T, T, F, F, E, T, F, T, E, F, E, T, F], [T, T, F, F, E, T, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_575 (And.intro z_732 trivial))

theorem z_734 : le (tf [T, T, F, F, E, T, F, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, T, E, T, E, F, F] [([T, T, F, F, E, T, F, E, T, T, E, F, F], [T, T, F, F, E, T, F, E, T, T, F, E, F]), ([T, T, F, F, E, T, F, T, E, E, T, F, F], [T, T, F, F, E, T, F, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_563 (And.intro z_733 trivial))

theorem z_735 : le (tf [T, T, F, F, E, F, T, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, T, F, T, E, F] [([T, T, F, F, E, F, E, T, T, F, T, E, F], [T, T, F, F, E, F, E, T, T, F, T, F, E]), ([T, T, F, F, E, F, T, E, T, F, E, T, F], [T, T, F, F, E, F, T, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_569 (And.intro z_499 trivial))

theorem z_736 : le (tf [T, T, F, F, E, T, E, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, F, T, F, T, E, F] [([T, T, F, F, E, E, T, F, T, F, T, E, F], [T, T, F, F, E, F, T, E, T, F, T, E, F]), ([T, T, F, F, E, T, E, F, T, F, E, T, F], [T, T, F, F, E, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_735 (And.intro z_562 trivial))

theorem z_737 : le (tf [T, T, F, F, E, T, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, E, E, T, F, F] [([T, T, F, F, E, T, E, F, T, E, T, F, F], [T, T, F, F, E, T, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_736 trivial)

theorem z_738 : le (tf [T, T, F, F, E, T, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, E, F, T, E, F, F] [([T, T, F, F, E, T, E, T, F, T, E, F, F], [T, T, F, F, E, T, F, T, E, T, E, F, F]), ([T, T, F, F, E, T, T, E, F, E, T, F, F], [T, T, F, F, E, T, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_734 (And.intro z_737 trivial))

theorem z_739 : le (tf [T, T, F, F, T, E, F, T, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, F, T, E, E, T, F, F] [([T, T, F, F, E, T, F, T, E, E, T, F, F], [T, T, F, F, E, T, F, T, E, F, T, E, F]), ([T, T, F, F, T, E, F, E, T, E, T, F, F], [T, T, F, F, T, E, F, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_733 (And.intro z_579 trivial))

theorem z_740 : le (tf [T, T, F, F, T, E, E, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, T, F, T, E, F, F] [([T, T, F, F, E, T, E, T, F, T, E, F, F], [T, T, F, F, E, T, F, T, E, T, E, F, F]), ([T, T, F, F, T, E, E, T, F, E, T, F, F], [T, T, F, F, T, E, F, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_734 (And.intro z_739 trivial))

theorem z_741 : le (tf [T, T, F, F, T, E, T, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, T, E, E, T, F, F, F] [([T, T, F, F, E, T, T, E, E, T, F, F, F], [T, T, F, F, E, T, T, E, F, T, E, F, F]), ([T, T, F, F, T, E, E, T, E, T, F, F, F], [T, T, F, F, T, E, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_738 (And.intro z_740 trivial))

theorem z_742 : le (tf [T, T, F, E, T, F, T, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, E, T, E, F, F, F] [([T, E, F, T, T, F, T, E, T, E, F, F, F], [T, F, E, T, T, F, T, E, T, E, F, F, F]), ([T, T, F, E, T, F, E, T, T, E, F, F, F], [T, T, F, E, T, F, E, T, T, F, E, F, F]), ([T, T, F, E, T, F, T, E, E, T, F, F, F], [T, T, F, F, T, E, T, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_720 (And.intro z_725 (And.intro z_741 trivial)))

theorem z_743 : le (tf [T, T, T, F, F, E, E, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, T, F, T, E, F, F] [([T, T, T, F, F, E, E, T, F, E, T, F, F], [T, T, T, F, F, E, F, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_103 trivial)

theorem z_744 : le (tf [T, T, T, F, F, E, E, T, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, T, T, E, F, F, F] [([T, T, T, F, F, E, E, T, E, T, F, F, F], [T, T, T, F, F, E, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_743 trivial)

theorem z_745 : le (tf [T, T, T, F, F, E, T, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, E, E, T, F, F, F] [([T, T, T, F, F, E, E, T, E, T, F, F, F], [T, T, T, F, F, E, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_743 trivial)

theorem z_746 : le (tf [T, T, T, F, E, F, T, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, E, T, E, F, F, F] [([T, T, E, F, T, F, T, E, T, E, F, F, F], [T, T, F, E, T, F, T, E, T, E, F, F, F]), ([T, T, T, F, E, F, E, T, T, E, F, F, F], [T, T, T, F, F, E, E, T, T, E, F, F, F]), ([T, T, T, F, E, F, T, E, E, T, F, F, F], [T, T, T, F, F, E, T, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_742 (And.intro z_744 (And.intro z_745 trivial)))

theorem z_747 : le (tf [T, T, T, F, T, F, E, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, E, E, T, F, F, F] [([T, T, T, F, E, F, T, E, E, T, F, F, F], [T, T, T, F, F, E, T, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_745 trivial)

theorem z_748 : le (tf [T, T, T, F, F, F, E, E, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, E, T, T, E, F, F] [([T, T, T, F, F, F, E, E, T, E, T, F, F], [T, T, T, F, F, F, E, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_213 trivial)

theorem z_749 : le (tf [T, T, T, F, F, E, F, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, E, T, E, F, F] [([T, T, T, F, F, E, F, E, T, T, E, F, F], [T, T, T, F, F, F, E, E, T, T, E, F, F]), ([T, T, T, F, F, E, F, T, E, E, T, F, F], [T, T, T, F, F, F, E, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_748 (And.intro z_214 trivial))

theorem z_750 : le (tf [T, T, T, F, F, E, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, T, E, F, T, E, F, F] [([T, T, T, F, F, E, E, T, F, T, E, F, F], [T, T, T, F, F, E, F, T, E, T, E, F, F]), ([T, T, T, F, F, E, T, E, F, E, T, F, F], [T, T, T, F, F, E, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_749 (And.intro z_536 trivial))

theorem z_751 : le (tf [T, T, T, F, F, T, E, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, E, E, E, T, F, F, F] [([T, T, T, F, F, E, T, E, E, T, F, F, F], [T, T, T, F, F, E, T, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_750 trivial)

theorem z_752 : le (tf [T, T, T, F, T, E, F, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, E, F, E, E, T, F, F, F] [([T, T, T, F, E, T, F, E, E, T, F, F, F], [T, T, T, F, F, T, E, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_751 trivial)

theorem z_753 : le (tf [F, E, T, T, T, T, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, E, F, E, T, F, F] [([F, E, T, T, T, E, F, T, F, E, T, F, F], [F, E, T, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_602 trivial)

theorem z_754 : le (tf [F, E, T, T, T, T, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, E, T, F, E, F, F] [([F, E, T, T, T, E, F, T, T, F, E, F, F], [F, E, T, T, T, F, E, T, T, F, E, F, F]), ([F, E, T, T, T, T, F, E, E, F, T, F, F], [F, E, T, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_603 (And.intro z_753 trivial))

theorem z_755 : le (tf [F, E, T, T, T, T, F, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, T, E, E, F, F, F] [([F, E, T, T, T, T, F, E, T, E, F, F, F], [F, E, T, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_754 trivial)

theorem z_756 : le (tf [F, E, T, T, T, T, T, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, T, E, F, E, F, F, F] [([F, E, T, T, T, T, E, T, F, E, F, F, F], [F, E, T, T, T, T, F, T, E, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_755 trivial)

theorem z_757 : le (tf [T, F, E, T, T, T, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, E, F, E, T, F, F] [([E, F, T, T, T, T, F, E, F, E, T, F, F], [F, E, T, T, T, T, F, E, F, E, T, F, F]), ([T, F, E, T, T, E, F, T, F, E, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_753 (And.intro z_611 trivial))

theorem z_758 : le (tf [T, F, E, T, T, T, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, E, T, F, E, F, F] [([E, F, T, T, T, T, F, E, T, F, E, F, F], [F, E, T, T, T, T, F, E, T, F, E, F, F]), ([T, F, E, T, T, E, F, T, T, F, E, F, F], [T, F, E, T, T, F, E, T, T, F, E, F, F]), ([T, F, E, T, T, T, F, E, E, F, T, F, F], [T, F, E, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_754 (And.intro z_612 (And.intro z_757 trivial)))

theorem z_759 : le (tf [T, F, E, T, T, T, F, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, T, E, E, F, F, F] [([E, F, T, T, T, T, F, T, E, E, F, F, F], [F, E, T, T, T, T, F, T, E, E, F, F, F]), ([T, F, E, T, T, T, F, E, T, E, F, F, F], [T, F, E, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_755 (And.intro z_758 trivial))

theorem z_760 : le (tf [T, F, E, T, T, T, T, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, T, E, F, E, F, F, F] [([E, F, T, T, T, T, T, E, F, E, F, F, F], [F, E, T, T, T, T, T, E, F, E, F, F, F]), ([T, F, E, T, T, T, E, T, F, E, F, F, F], [T, F, E, T, T, T, F, T, E, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_756 (And.intro z_759 trivial))

theorem z_761 : le (tf [T, T, F, E, T, T, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, E, F, E, T, F, F] [([T, E, F, T, T, T, F, E, F, E, T, F, F], [T, F, E, T, T, T, F, E, F, E, T, F, F]), ([T, T, F, E, T, E, F, T, F, E, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_757 (And.intro z_724 trivial))

theorem z_762 : le (tf [T, T, F, E, T, T, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, E, T, F, E, F, F] [([T, E, F, T, T, T, F, E, T, F, E, F, F], [T, F, E, T, T, T, F, E, T, F, E, F, F]), ([T, T, F, E, T, E, F, T, T, F, E, F, F], [T, T, F, E, T, F, E, T, T, F, E, F, F]), ([T, T, F, E, T, T, F, E, E, F, T, F, F], [T, T, F, E, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_758 (And.intro z_725 (And.intro z_761 trivial)))

theorem z_763 : le (tf [T, T, F, E, T, T, F, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, T, E, E, F, F, F] [([T, E, F, T, T, T, F, T, E, E, F, F, F], [T, F, E, T, T, T, F, T, E, E, F, F, F]), ([T, T, F, E, T, T, F, E, T, E, F, F, F], [T, T, F, E, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_759 (And.intro z_762 trivial))

theorem z_764 : le (tf [T, T, F, E, T, T, T, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, T, E, F, E, F, F, F] [([T, E, F, T, T, T, T, E, F, E, F, F, F], [T, F, E, T, T, T, T, E, F, E, F, F, F]), ([T, T, F, E, T, T, E, T, F, E, F, F, F], [T, T, F, E, T, T, F, T, E, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_760 (And.intro z_763 trivial))

theorem z_765 : le (tf [T, T, T, F, F, T, E, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, E, F, E, E, T, F, F] [([T, T, T, F, F, E, T, F, E, E, T, F, F], [T, T, T, F, F, F, T, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_94 trivial)

theorem z_766 : le (tf [T, T, T, F, F, T, E, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, E, E, F, T, E, F, F] [([T, T, T, F, F, E, T, E, F, T, E, F, F], [T, T, T, F, F, E, T, F, E, T, E, F, F]), ([T, T, T, F, F, T, E, E, F, E, T, F, F], [T, T, T, F, F, T, E, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_95 (And.intro z_765 trivial))

theorem z_767 : le (tf [T, T, T, F, F, T, E, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, E, E, T, E, F, F, F] [([T, T, T, F, F, E, T, E, T, E, F, F, F], [T, T, T, F, F, E, T, E, T, F, E, F, F]), ([T, T, T, F, F, T, E, E, E, T, F, F, F], [T, T, T, F, F, T, E, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_766 trivial))

theorem z_768 : le (tf [T, T, T, F, E, T, F, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, T, F, T, E, E, F, F, F] [([T, T, E, F, T, T, F, T, E, E, F, F, F], [T, T, F, E, T, T, F, T, E, E, F, F, F]), ([T, T, T, F, E, T, F, E, T, E, F, F, F], [T, T, T, F, F, T, E, E, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_763 (And.intro z_767 trivial))

theorem z_769 : le (tf [T, T, T, F, E, T, T, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, T, T, E, F, E, F, F, F] [([T, T, E, F, T, T, T, E, F, E, F, F, F], [T, T, F, E, T, T, T, E, F, E, F, F, F]), ([T, T, T, F, E, T, E, T, F, E, F, F, F], [T, T, T, F, E, T, F, T, E, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_764 (And.intro z_768 trivial))

theorem z_770 : le (tf [F, E, T, T, T, T, E, F, F, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, E, F, F, T, E, F, F] [([F, E, T, T, T, E, T, F, F, T, E, F, F], [F, E, T, T, T, F, T, E, F, T, E, F, F]), ([F, E, T, T, T, T, E, F, F, E, T, F, F], [F, E, T, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_607 (And.intro z_753 trivial))

theorem z_771 : le (tf [T, F, E, T, T, T, E, F, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, E, F, F, T, E, F, F] [([E, F, T, T, T, T, E, F, F, T, E, F, F], [F, E, T, T, T, T, E, F, F, T, E, F, F]), ([T, F, E, T, T, E, T, F, F, T, E, F, F], [T, F, E, T, T, F, T, E, F, T, E, F, F]), ([T, F, E, T, T, T, E, F, F, E, T, F, F], [T, F, E, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_770 (And.intro z_719 (And.intro z_757 trivial)))

theorem z_772 : le (tf [T, T, F, F, T, E, T, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, T, E, F, E, T, F, F] [([T, T, F, F, E, T, T, E, F, E, T, F, F], [T, T, F, F, E, T, T, F, E, E, T, F, F]), ([T, T, F, F, T, E, E, T, F, E, T, F, F], [T, T, F, F, T, E, F, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_737 (And.intro z_739 trivial))

theorem z_773 : le (tf [T, T, F, E, T, F, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, E, F, T, E, F, F] [([T, E, F, T, T, F, T, E, F, T, E, F, F], [T, F, E, T, T, F, T, E, F, T, E, F, F]), ([T, T, F, E, T, F, E, T, F, T, E, F, F], [T, T, F, F, T, E, E, T, F, T, E, F, F]), ([T, T, F, E, T, F, T, E, F, E, T, F, F], [T, T, F, F, T, E, T, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_719 (And.intro z_740 (And.intro z_772 trivial)))

theorem z_774 : le (tf [T, T, F, E, T, T, E, F, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, E, F, F, T, E, F, F] [([T, E, F, T, T, T, E, F, F, T, E, F, F], [T, F, E, T, T, T, E, F, F, T, E, F, F]), ([T, T, F, E, T, E, T, F, F, T, E, F, F], [T, T, F, E, T, F, T, E, F, T, E, F, F]), ([T, T, F, E, T, T, E, F, F, E, T, F, F], [T, T, F, E, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_771 (And.intro z_773 (And.intro z_761 trivial)))

theorem z_775 : le (tf [T, T, T, F, E, F, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, E, F, T, E, F, F] [([T, T, E, F, T, F, T, E, F, T, E, F, F], [T, T, F, E, T, F, T, E, F, T, E, F, F]), ([T, T, T, F, E, F, E, T, F, T, E, F, F], [T, T, T, F, F, E, E, T, F, T, E, F, F]), ([T, T, T, F, E, F, T, E, F, E, T, F, F], [T, T, T, F, F, E, T, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_773 (And.intro z_743 (And.intro z_104 trivial)))

theorem z_776 : le (tf [T, T, T, F, E, F, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, E, T, F, E, T, F, F] [([T, T, E, F, T, F, E, T, F, E, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F]), ([T, T, T, F, E, F, E, E, F, T, T, F, F], [T, T, T, F, F, E, E, E, F, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_724 (And.intro z_532 trivial))

theorem z_777 : le (tf [T, T, T, F, E, T, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, T, F, E, F, E, T, F, F] [([T, T, E, F, T, T, F, E, F, E, T, F, F], [T, T, F, E, T, T, F, E, F, E, T, F, F]), ([T, T, T, F, E, E, F, T, F, E, T, F, F], [T, T, T, F, E, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_761 (And.intro z_776 trivial))

theorem z_778 : le (tf [T, T, T, F, E, T, E, F, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, T, E, F, F, T, E, F, F] [([T, T, E, F, T, T, E, F, F, T, E, F, F], [T, T, F, E, T, T, E, F, F, T, E, F, F]), ([T, T, T, F, E, E, T, F, F, T, E, F, F], [T, T, T, F, E, F, T, E, F, T, E, F, F]), ([T, T, T, F, E, T, E, F, F, E, T, F, F], [T, T, T, F, E, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_774 (And.intro z_775 (And.intro z_777 trivial)))

theorem z_779 : le (tf [T, T, T, F, T, E, E, F, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, E, E, F, E, T, F, F, F] [([T, T, T, F, E, T, E, F, E, T, F, F, F], [T, T, T, F, E, T, E, F, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_778 trivial)

theorem z_780 : le (tf [T, T, T, F, T, E, E, T, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, E, E, T, F, E, F, F, F] [([T, T, T, F, E, T, E, T, F, E, F, F, F], [T, T, T, F, E, T, F, T, E, E, F, F, F]), ([T, T, T, F, T, E, E, E, F, T, F, F, F], [T, T, T, F, T, E, E, F, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_768 (And.intro z_779 trivial))

theorem z_781 : le (tf [T, T, T, F, T, F, F, T, F, F, E, E, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, T, F, F, E, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_782 : le (tf [T, T, T, F, T, F, F, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, F, T, E, F, E] [([T, T, T, F, T, F, F, E, F, E, T, F, E], [T, T, T, F, T, F, F, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_547 trivial)

theorem z_783 : le (tf [T, T, T, F, T, F, F, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, E, T, E, F] [([T, T, T, F, T, F, F, F, E, E, E, T, F], [T, T, T, F, T, F, F, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_545 trivial)

theorem z_784 : le (tf [T, T, T, F, T, F, F, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, F, T, E, E, F] [([T, T, T, F, T, F, F, E, F, E, T, E, F], [T, T, T, F, T, F, F, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_783 trivial)

theorem z_785 : le (tf [F, E, F, E, T, T, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, T, T, F, E, F] [([F, E, F, E, T, T, T, F, T, E, F, T, F], [F, E, F, E, T, T, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_330 trivial)

theorem z_786 : le (tf [F, E, T, F, E, T, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, T, T, F, E, F] [([F, E, E, F, T, T, T, F, T, T, F, E, F], [F, E, F, E, T, T, T, F, T, T, F, E, F]), ([F, E, T, F, E, T, T, F, T, E, F, T, F], [F, E, T, F, E, T, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_785 (And.intro z_334 trivial))

theorem z_787 : le (tf [F, E, T, T, F, F, E, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, F, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_788 : le (tf [F, E, T, T, F, F, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, F, E, T, T, F] [([F, E, T, T, F, F, E, E, F, T, T, T, F], [F, E, T, T, F, F, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_787 trivial)

theorem z_789 : le (tf [F, E, T, T, F, F, T, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, T, E, E, F, T, T, F] [([F, E, T, T, F, F, E, T, E, F, T, T, F], [F, E, T, T, F, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_788 trivial)

theorem z_790 : le (tf [F, E, T, T, F, E, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, T, F, E, T, F] [([F, E, T, E, F, T, T, F, T, F, E, T, F], [F, E, T, F, E, T, T, F, T, F, E, T, F]), ([F, E, T, T, F, E, T, F, E, F, T, T, F], [F, E, T, T, F, F, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 (And.intro z_789 trivial))

theorem z_791 : le (tf [F, E, T, T, F, E, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, T, T, F, E, F] [([F, E, T, E, F, T, T, F, T, T, F, E, F], [F, E, T, F, E, T, T, F, T, T, F, E, F]), ([F, E, T, T, F, E, T, F, T, E, F, T, F], [F, E, T, T, F, E, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_786 (And.intro z_790 trivial))

theorem z_792 : le (tf [F, E, T, T, T, F, F, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, T, E, F, T, F] [([F, E, T, T, T, F, F, E, E, T, F, T, F], [F, E, T, T, T, F, F, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 trivial)

theorem z_793 : le (tf [F, E, T, T, T, F, E, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, F, T, T, F, E, F] [([F, E, T, T, E, F, T, F, T, T, F, E, F], [F, E, T, T, F, E, T, F, T, T, F, E, F]), ([F, E, T, T, T, F, E, F, T, E, F, T, F], [F, E, T, T, T, F, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_791 (And.intro z_792 trivial))

theorem z_794 : le (tf [F, F, E, E, T, T, T, F, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, F, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_795 : le (tf [F, F, E, E, T, T, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, T, F, E, F, T] [([F, F, E, E, T, T, T, F, E, F, T, F, T], [F, F, E, E, T, T, T, F, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_794 trivial)

theorem z_796 : le (tf [F, E, F, E, T, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, T, F, T, F, E] [([F, E, F, E, T, T, T, F, T, F, E, F, T], [F, F, E, E, T, T, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_795 trivial)

theorem z_797 : le (tf [F, E, F, E, T, T, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_798 : le (tf [F, E, T, F, E, T, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, T, F, F, E, T] [([F, E, E, F, T, T, T, F, T, F, F, E, T], [F, E, F, E, T, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_797 trivial)

theorem z_799 : le (tf [F, E, T, F, E, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, T, F, T, F, E] [([F, E, E, F, T, T, T, F, T, F, T, F, E], [F, E, F, E, T, T, T, F, T, F, T, F, E]), ([F, E, T, F, E, T, T, F, T, F, E, F, T], [F, E, T, F, E, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_796 (And.intro z_798 trivial))

theorem z_800 : le (tf [F, E, T, T, F, E, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, T, F, F, E, T] [([F, E, T, E, F, T, T, F, T, F, F, E, T], [F, E, T, F, E, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_798 trivial)

theorem z_801 : le (tf [F, E, T, T, F, E, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, T, F, T, F, E] [([F, E, T, E, F, T, T, F, T, F, T, F, E], [F, E, T, F, E, T, T, F, T, F, T, F, E]), ([F, E, T, T, F, E, T, F, T, F, E, F, T], [F, E, T, T, F, E, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_799 (And.intro z_800 trivial))

theorem z_802 : le (tf [F, E, T, T, T, F, E, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, F, T, F, T, F, E] [([F, E, T, T, E, F, T, F, T, F, T, F, E], [F, E, T, T, F, E, T, F, T, F, T, F, E]), ([F, E, T, T, T, F, E, F, T, F, E, F, T], [F, E, T, T, T, F, F, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_801 (And.intro z_430 trivial))

theorem z_803 : le (tf [F, E, T, T, T, F, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_804 : le (tf [F, E, T, T, T, F, T, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, E, F, T, E, F] [([F, E, T, T, T, F, E, F, T, F, T, E, F], [F, E, T, T, T, F, E, F, T, F, T, F, E]), ([F, E, T, T, T, F, T, F, E, F, E, T, F], [F, E, T, T, T, F, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_802 (And.intro z_803 trivial))

theorem z_805 : le (tf [F, E, T, T, T, F, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, E, T, E, F, F] [([F, E, T, T, T, F, E, F, T, T, E, F, F], [F, E, T, T, T, F, E, F, T, T, F, E, F]), ([F, E, T, T, T, F, T, F, E, E, T, F, F], [F, E, T, T, T, F, T, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_793 (And.intro z_804 trivial))

theorem z_806 : le (tf [F, E, T, T, T, F, T, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, T, F, E, E, F, F] [([F, E, T, T, T, F, T, E, F, T, E, F, F], [F, E, T, T, T, F, T, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_805 trivial)

theorem z_807 : le (tf [T, F, F, E, E, F, E, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, F, E, T, T, F, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_808 : le (tf [T, F, F, E, E, T, F, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, F, E, T, F, T, T, F] [([T, F, F, E, E, E, F, T, T, F, T, T, F], [T, F, F, E, E, F, E, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_807 trivial)

theorem z_809 : le (tf [T, F, F, E, E, T, T, F, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, E, F, T, T, F] [([T, F, F, E, E, T, E, F, T, F, T, T, F], [T, F, F, E, E, T, F, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_808 trivial)

theorem z_810 : le (tf [T, F, E, F, E, T, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, T, F, E, T, F] [([E, F, T, F, E, T, T, F, T, F, E, T, F], [F, E, T, F, E, T, T, F, T, F, E, T, F]), ([T, F, E, F, E, T, T, F, E, F, T, T, F], [T, F, F, E, E, T, T, F, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 (And.intro z_809 trivial))

theorem z_811 : le (tf [T, F, E, F, E, T, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, T, T, F, E, F] [([E, F, T, F, E, T, T, F, T, T, F, E, F], [F, E, T, F, E, T, T, F, T, T, F, E, F]), ([T, F, E, F, E, T, T, F, T, E, F, T, F], [T, F, E, F, E, T, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_786 (And.intro z_810 trivial))

theorem z_812 : le (tf [T, F, F, E, T, F, T, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, T, E, E, F, T, T, F] [([T, F, F, E, T, F, E, T, E, F, T, T, F], [T, F, F, E, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_163 trivial)

theorem z_813 : le (tf [T, F, F, F, E, E, E, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, E, T, T, F, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_814 : le (tf [T, F, F, E, F, E, T, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, E, T, F, T, T, F] [([T, F, F, E, F, E, E, T, T, F, T, T, F], [T, F, F, F, E, E, E, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_813 trivial)

theorem z_815 : le (tf [T, F, F, E, T, F, E, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, E, T, F, T, T, F] [([T, F, F, E, E, F, T, E, T, F, T, T, F], [T, F, F, E, F, E, T, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_814 trivial)

theorem z_816 : le (tf [T, F, F, T, E, E, F, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, E, T, F, T, T, F] [([T, F, F, E, T, E, F, E, T, F, T, T, F], [T, F, F, E, T, F, E, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_815 trivial)

theorem z_817 : le (tf [T, F, F, T, E, E, T, F, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, T, F, E, F, T, T, F] [([T, F, F, E, T, E, T, F, E, F, T, T, F], [T, F, F, E, T, F, T, E, E, F, T, T, F]), ([T, F, F, T, E, E, E, F, T, F, T, T, F], [T, F, F, T, E, E, F, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_812 (And.intro z_816 trivial))

theorem z_818 : le (tf [T, F, E, T, F, E, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, T, F, E, T, F] [([E, F, T, T, F, E, T, F, T, F, E, T, F], [F, E, T, T, F, E, T, F, T, F, E, T, F]), ([T, F, E, E, F, T, T, F, T, F, E, T, F], [T, F, E, F, E, T, T, F, T, F, E, T, F]), ([T, F, E, T, F, E, T, F, E, F, T, T, F], [T, F, F, T, E, E, T, F, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_790 (And.intro z_810 (And.intro z_817 trivial)))

theorem z_819 : le (tf [T, F, E, T, F, E, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, T, T, F, E, F] [([E, F, T, T, F, E, T, F, T, T, F, E, F], [F, E, T, T, F, E, T, F, T, T, F, E, F]), ([T, F, E, E, F, T, T, F, T, T, F, E, F], [T, F, E, F, E, T, T, F, T, T, F, E, F]), ([T, F, E, T, F, E, T, F, T, E, F, T, F], [T, F, E, T, F, E, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_791 (And.intro z_811 (And.intro z_818 trivial)))

theorem z_820 : le (tf [T, F, E, T, T, F, F, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, T, E, F, T, F] [([E, F, T, T, T, F, F, E, T, E, F, T, F], [F, E, T, T, T, F, F, E, T, E, F, T, F]), ([T, F, E, T, T, F, F, E, E, T, F, T, F], [T, F, E, T, T, F, F, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_792 (And.intro z_443 trivial))

theorem z_821 : le (tf [T, F, E, T, T, F, E, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, F, T, T, F, E, F] [([E, F, T, T, T, F, E, F, T, T, F, E, F], [F, E, T, T, T, F, E, F, T, T, F, E, F]), ([T, F, E, T, E, F, T, F, T, T, F, E, F], [T, F, E, T, F, E, T, F, T, T, F, E, F]), ([T, F, E, T, T, F, E, F, T, E, F, T, F], [T, F, E, T, T, F, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_793 (And.intro z_819 (And.intro z_820 trivial)))

theorem z_822 : le (tf [T, F, F, E, E, T, T, F, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, F, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_823 : le (tf [T, F, F, E, E, T, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, T, F, E, F, T] [([T, F, F, E, E, T, T, F, E, F, T, F, T], [T, F, F, E, E, T, T, F, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_822 trivial)

theorem z_824 : le (tf [T, F, E, F, E, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, T, F, T, F, E] [([E, F, T, F, E, T, T, F, T, F, T, F, E], [F, E, T, F, E, T, T, F, T, F, T, F, E]), ([T, F, E, F, E, T, T, F, T, F, E, F, T], [T, F, F, E, E, T, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_799 (And.intro z_823 trivial))

theorem z_825 : le (tf [T, F, E, F, E, T, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, T, F, F, E, T] [([E, F, T, F, E, T, T, F, T, F, F, E, T], [F, E, T, F, E, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_798 trivial)

theorem z_826 : le (tf [T, F, E, T, F, E, T, F, T, F, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, T, F, F, E, T] [([E, F, T, T, F, E, T, F, T, F, F, E, T], [F, E, T, T, F, E, T, F, T, F, F, E, T]), ([T, F, E, E, F, T, T, F, T, F, F, E, T], [T, F, E, F, E, T, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_800 (And.intro z_825 trivial))

theorem z_827 : le (tf [T, F, E, T, F, E, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, T, F, T, F, E] [([E, F, T, T, F, E, T, F, T, F, T, F, E], [F, E, T, T, F, E, T, F, T, F, T, F, E]), ([T, F, E, E, F, T, T, F, T, F, T, F, E], [T, F, E, F, E, T, T, F, T, F, T, F, E]), ([T, F, E, T, F, E, T, F, T, F, E, F, T], [T, F, E, T, F, E, T, F, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_801 (And.intro z_824 (And.intro z_826 trivial)))

theorem z_828 : le (tf [T, F, E, T, T, F, E, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, F, T, F, T, F, E] [([E, F, T, T, T, F, E, F, T, F, T, F, E], [F, E, T, T, T, F, E, F, T, F, T, F, E]), ([T, F, E, T, E, F, T, F, T, F, T, F, E], [T, F, E, T, F, E, T, F, T, F, T, F, E]), ([T, F, E, T, T, F, E, F, T, F, E, F, T], [T, F, E, T, T, F, F, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_802 (And.intro z_827 (And.intro z_441 trivial)))

theorem z_829 : le (tf [T, F, E, T, T, F, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, F, E, E, T, F] [([E, F, T, T, T, F, T, F, F, E, E, T, F], [F, E, T, T, T, F, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_803 trivial)

theorem z_830 : le (tf [T, F, E, T, T, F, T, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, E, F, T, E, F] [([E, F, T, T, T, F, T, F, E, F, T, E, F], [F, E, T, T, T, F, T, F, E, F, T, E, F]), ([T, F, E, T, T, F, E, F, T, F, T, E, F], [T, F, E, T, T, F, E, F, T, F, T, F, E]), ([T, F, E, T, T, F, T, F, E, F, E, T, F], [T, F, E, T, T, F, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_804 (And.intro z_828 (And.intro z_829 trivial)))

theorem z_831 : le (tf [T, F, E, T, T, F, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, E, T, E, F, F] [([E, F, T, T, T, F, T, F, E, T, E, F, F], [F, E, T, T, T, F, T, F, E, T, E, F, F]), ([T, F, E, T, T, F, E, F, T, T, E, F, F], [T, F, E, T, T, F, E, F, T, T, F, E, F]), ([T, F, E, T, T, F, T, F, E, E, T, F, F], [T, F, E, T, T, F, T, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_805 (And.intro z_821 (And.intro z_830 trivial)))

theorem z_832 : le (tf [T, F, E, T, T, F, T, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, T, F, E, E, F, F] [([E, F, T, T, T, F, T, T, F, E, E, F, F], [F, E, T, T, T, F, T, T, F, E, E, F, F]), ([T, F, E, T, T, F, T, E, F, T, E, F, F], [T, F, E, T, T, F, T, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_806 (And.intro z_831 trivial))

theorem z_833 : le (tf [T, T, F, F, E, F, E, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, F, T, E, T, F] [([T, T, F, F, E, F, E, T, F, E, T, T, F], [T, T, F, F, F, E, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_501 trivial)

theorem z_834 : le (tf [T, T, F, F, E, F, T, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, E, T, F, T, F] [([T, T, F, F, E, F, E, T, E, T, F, T, F], [T, T, F, F, E, F, E, T, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_833 trivial)

theorem z_835 : le (tf [T, T, F, F, E, E, T, F, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, F, T, E, F, T, F] [([T, T, F, F, E, E, T, F, E, T, F, T, F], [T, T, F, F, E, F, T, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_834 trivial)

theorem z_836 : le (tf [T, T, F, E, F, E, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, F, T, T, F, E, F] [([T, E, F, T, F, E, T, F, T, T, F, E, F], [T, F, E, T, F, E, T, F, T, T, F, E, F]), ([T, T, F, E, F, E, T, F, T, E, F, T, F], [T, T, F, F, E, E, T, F, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_819 (And.intro z_835 trivial))

theorem z_837 : le (tf [T, T, F, F, E, F, E, T, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, T, E, F, T, F] [([T, T, F, F, E, F, E, T, E, T, F, T, F], [T, T, F, F, E, F, E, T, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_833 trivial)

theorem z_838 : le (tf [T, T, F, F, F, F, E, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, T, T, F, E, T] [([T, T, F, F, F, F, E, E, T, E, F, T, T], [T, T, F, F, F, F, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_483 trivial)

theorem z_839 : le (tf [T, T, F, F, F, F, E, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, T, E, E, F, T, T] [([T, T, F, F, F, F, E, E, T, E, F, T, T], [T, T, F, F, F, F, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_483 trivial)

theorem z_840 : le (tf [T, T, F, F, F, E, F, T, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, T, E, T, F, E, T] [([T, T, F, F, F, E, F, E, T, T, F, E, T], [T, T, F, F, F, F, E, E, T, T, F, E, T]), ([T, T, F, F, F, E, F, T, E, E, F, T, T], [T, T, F, F, F, F, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_838 (And.intro z_839 trivial))

theorem z_841 : le (tf [T, T, F, F, F, E, E, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, F, T, F, T, E] [([T, T, F, F, F, E, E, T, F, T, F, E, T], [T, T, F, F, F, E, F, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_840 trivial)

theorem z_842 : le (tf [T, T, F, F, F, F, E, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, F, E, E, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_843 : le (tf [T, T, F, F, F, E, F, E, T, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, T, E, T, T, F] [([T, T, F, F, F, E, F, E, E, T, T, T, F], [T, T, F, F, F, F, E, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_842 trivial)

theorem z_844 : le (tf [T, T, F, F, F, E, T, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, F, E, E, T, T, F] [([T, T, F, F, F, E, E, F, T, E, T, T, F], [T, T, F, F, F, E, F, E, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_843 trivial)

theorem z_845 : le (tf [T, T, F, F, F, E, T, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, E, F, T, E, T, F] [([T, T, F, F, F, E, E, T, F, T, E, T, F], [T, T, F, F, F, E, E, T, F, T, F, T, E]), ([T, T, F, F, F, E, T, E, F, E, T, T, F], [T, T, F, F, F, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_841 (And.intro z_844 trivial))

theorem z_846 : le (tf [T, T, F, F, F, T, E, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, E, T, F, T, F] [([T, T, F, F, F, E, T, E, E, T, F, T, F], [T, T, F, F, F, E, T, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_845 trivial)

theorem z_847 : le (tf [T, T, F, F, E, T, F, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, T, E, F, T, F] [([T, T, F, F, E, E, F, T, T, E, F, T, F], [T, T, F, F, E, F, E, T, T, E, F, T, F]), ([T, T, F, F, E, T, F, E, E, T, F, T, F], [T, T, F, F, F, T, E, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_837 (And.intro z_846 trivial))

theorem z_848 : le (tf [T, T, F, F, T, E, F, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, F, E, E, T, F, T, F] [([T, T, F, F, E, T, F, E, E, T, F, T, F], [T, T, F, F, F, T, E, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_846 trivial)

theorem z_849 : le (tf [T, T, F, F, T, E, E, F, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, F, T, E, F, T, F] [([T, T, F, F, E, T, E, F, T, E, F, T, F], [T, T, F, F, E, T, F, E, T, E, F, T, F]), ([T, T, F, F, T, E, E, F, E, T, F, T, F], [T, T, F, F, T, E, F, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_847 (And.intro z_848 trivial))

theorem z_850 : le (tf [T, T, F, E, T, F, E, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, F, T, T, F, E, F] [([T, E, F, T, T, F, E, F, T, T, F, E, F], [T, F, E, T, T, F, E, F, T, T, F, E, F]), ([T, T, F, E, E, F, T, F, T, T, F, E, F], [T, T, F, E, F, E, T, F, T, T, F, E, F]), ([T, T, F, E, T, F, E, F, T, E, F, T, F], [T, T, F, F, T, E, E, F, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_821 (And.intro z_836 (And.intro z_849 trivial)))

theorem z_851 : le (tf [T, T, F, F, F, E, F, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, E, E, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_852 : le (tf [T, T, F, F, F, E, E, F, T, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, F, T, E, T, F, T] [([T, T, F, F, F, E, E, F, E, T, T, F, T], [T, T, F, F, F, E, F, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_851 trivial)

theorem z_853 : le (tf [T, T, F, F, F, E, E, T, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, E, F, T, F, T] [([T, T, F, F, F, E, E, E, T, F, T, F, T], [T, T, F, F, F, E, E, F, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_852 trivial)

theorem z_854 : le (tf [T, T, F, F, E, F, T, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, E, F, T, F, T] [([T, T, F, F, E, F, E, T, E, F, T, F, T], [T, T, F, F, F, E, E, T, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_853 trivial)

theorem z_855 : le (tf [T, T, F, F, E, E, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, F, T, F, E, F, T] [([T, T, F, F, E, E, T, F, E, F, T, F, T], [T, T, F, F, E, F, T, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_854 trivial)

theorem z_856 : le (tf [T, T, F, E, F, E, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, F, T, F, T, F, E] [([T, E, F, T, F, E, T, F, T, F, T, F, E], [T, F, E, T, F, E, T, F, T, F, T, F, E]), ([T, T, F, E, F, E, T, F, T, F, E, F, T], [T, T, F, F, E, E, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_827 (And.intro z_855 trivial))

theorem z_857 : le (tf [T, T, F, F, E, F, E, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, T, F, E, F, T] [([T, T, F, F, E, F, E, T, E, F, T, F, T], [T, T, F, F, F, E, E, T, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_853 trivial)

theorem z_858 : le (tf [T, T, F, F, F, E, F, T, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, F, T, E, E, T, F, T] [([T, T, F, F, F, E, F, E, T, E, T, F, T], [T, T, F, F, F, E, F, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_484 trivial)

theorem z_859 : le (tf [T, T, F, F, F, E, T, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, E, F, E, T, F, T] [([T, T, F, F, F, E, E, T, F, E, T, F, T], [T, T, F, F, F, E, F, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_858 trivial)

theorem z_860 : le (tf [T, T, F, F, F, T, E, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, E, F, T, F, T] [([T, T, F, F, F, E, T, E, E, F, T, F, T], [T, T, F, F, F, E, T, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_859 trivial)

theorem z_861 : le (tf [T, T, F, F, E, T, F, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, T, F, E, F, T] [([T, T, F, F, E, E, F, T, T, F, E, F, T], [T, T, F, F, E, F, E, T, T, F, E, F, T]), ([T, T, F, F, E, T, F, E, E, F, T, F, T], [T, T, F, F, F, T, E, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_857 (And.intro z_860 trivial))

theorem z_862 : le (tf [T, T, F, F, T, E, F, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, F, E, E, F, T, F, T] [([T, T, F, F, E, T, F, E, E, F, T, F, T], [T, T, F, F, F, T, E, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_860 trivial)

theorem z_863 : le (tf [T, T, F, F, T, E, E, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, F, T, F, E, F, T] [([T, T, F, F, E, T, E, F, T, F, E, F, T], [T, T, F, F, E, T, F, E, T, F, E, F, T]), ([T, T, F, F, T, E, E, F, E, F, T, F, T], [T, T, F, F, T, E, F, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_861 (And.intro z_862 trivial))

theorem z_864 : le (tf [T, T, F, E, T, F, E, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, F, T, F, T, F, E] [([T, E, F, T, T, F, E, F, T, F, T, F, E], [T, F, E, T, T, F, E, F, T, F, T, F, E]), ([T, T, F, E, E, F, T, F, T, F, T, F, E], [T, T, F, E, F, E, T, F, T, F, T, F, E]), ([T, T, F, E, T, F, E, F, T, F, E, F, T], [T, T, F, F, T, E, E, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_828 (And.intro z_856 (And.intro z_863 trivial)))

theorem z_865 : le (tf [T, T, F, E, T, F, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, F, F, E, E, T, F] [([T, E, F, T, T, F, T, F, F, E, E, T, F], [T, F, E, T, T, F, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_829 trivial)

theorem z_866 : le (tf [T, T, F, E, T, F, T, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, F, E, F, T, E, F] [([T, E, F, T, T, F, T, F, E, F, T, E, F], [T, F, E, T, T, F, T, F, E, F, T, E, F]), ([T, T, F, E, T, F, E, F, T, F, T, E, F], [T, T, F, E, T, F, E, F, T, F, T, F, E]), ([T, T, F, E, T, F, T, F, E, F, E, T, F], [T, T, F, E, T, F, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_830 (And.intro z_864 (And.intro z_865 trivial)))

theorem z_867 : le (tf [T, T, F, E, T, F, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, F, E, T, E, F, F] [([T, E, F, T, T, F, T, F, E, T, E, F, F], [T, F, E, T, T, F, T, F, E, T, E, F, F]), ([T, T, F, E, T, F, E, F, T, T, E, F, F], [T, T, F, E, T, F, E, F, T, T, F, E, F]), ([T, T, F, E, T, F, T, F, E, E, T, F, F], [T, T, F, E, T, F, T, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_831 (And.intro z_850 (And.intro z_866 trivial)))

theorem z_868 : le (tf [T, T, F, E, T, F, T, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, T, F, E, E, F, F] [([T, E, F, T, T, F, T, T, F, E, E, F, F], [T, F, E, T, T, F, T, T, F, E, E, F, F]), ([T, T, F, E, T, F, T, E, F, T, E, F, F], [T, T, F, E, T, F, T, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_832 (And.intro z_867 trivial))

theorem z_869 : le (tf [T, T, T, F, E, F, T, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, T, F, E, E, F, F] [([T, T, E, F, T, F, T, T, F, E, E, F, F], [T, T, F, E, T, F, T, T, F, E, E, F, F]), ([T, T, T, F, E, F, T, E, F, T, E, F, F], [T, T, T, F, F, E, T, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_868 (And.intro z_750 trivial))

theorem z_870 : le (tf [T, T, T, F, T, F, E, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, F, E, E, T, F, F] [([T, T, T, F, E, F, T, F, E, E, T, F, F], [T, T, T, F, F, E, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_536 trivial)

theorem z_871 : le (tf [T, T, T, F, T, F, E, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, E, E, F, T, E, F, F] [([T, T, T, F, E, F, T, E, F, T, E, F, F], [T, T, T, F, F, E, T, E, F, T, E, F, F]), ([T, T, T, F, T, F, E, E, F, E, T, F, F], [T, T, T, F, T, F, E, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_750 (And.intro z_870 trivial))

theorem z_872 : le (tf [F, E, T, T, T, F, T, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, T, E, F, E, F, F] [([F, E, T, T, T, F, T, E, T, F, E, F, F], [F, E, T, T, T, F, T, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_552 trivial)

theorem z_873 : le (tf [T, F, E, T, T, F, T, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, T, E, F, E, F, F] [([E, F, T, T, T, F, T, T, E, F, E, F, F], [F, E, T, T, T, F, T, T, E, F, E, F, F]), ([T, F, E, T, T, F, T, E, T, F, E, F, F], [T, F, E, T, T, F, T, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_872 (And.intro z_556 trivial))

theorem z_874 : le (tf [T, T, F, E, T, F, T, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, T, T, E, F, E, F, F] [([T, E, F, T, T, F, T, T, E, F, E, F, F], [T, F, E, T, T, F, T, T, E, F, E, F, F]), ([T, T, F, E, T, F, T, E, T, F, E, F, F], [T, T, F, E, T, F, T, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_873 (And.intro z_595 trivial))

theorem z_875 : le (tf [T, T, T, F, E, F, T, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, T, E, F, E, F, F] [([T, T, E, F, T, F, T, T, E, F, E, F, F], [T, T, F, E, T, F, T, T, E, F, E, F, F]), ([T, T, T, F, E, F, T, E, T, F, E, F, F], [T, T, T, F, F, E, T, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_874 (And.intro z_105 trivial))

theorem z_876 : le (tf [F, E, T, T, T, F, T, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, T, E, F, E, F] [([F, E, T, T, T, F, T, F, E, T, F, E, F], [F, E, T, T, T, F, T, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_150 trivial)

theorem z_877 : le (tf [T, F, E, T, T, F, T, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, T, E, F, E, F] [([E, F, T, T, T, F, T, F, T, E, F, E, F], [F, E, T, T, T, F, T, F, T, E, F, E, F]), ([T, F, E, T, T, F, T, F, E, T, F, E, F], [T, F, E, T, T, F, T, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_876 (And.intro z_153 trivial))

theorem z_878 : le (tf [T, F, T, E, T, F, T, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, T, F, T, E, E, F, F] [([T, F, E, T, T, F, T, F, T, E, E, F, F], [T, F, E, T, T, F, T, F, T, E, F, E, F]), ([T, F, T, E, T, F, T, F, E, T, E, F, F], [T, F, T, E, T, F, T, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_877 (And.intro z_185 trivial))

theorem z_879 : le (tf [T, F, T, E, T, F, T, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, T, T, E, F, E, F, F] [([T, F, E, T, T, F, T, T, E, F, E, F, F], [T, F, E, T, T, F, T, T, F, E, E, F, F]), ([T, F, T, E, T, F, T, E, T, F, E, F, F], [T, F, T, E, T, F, T, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_832 (And.intro z_878 trivial))

theorem z_880 : le (tf [T, T, E, F, T, F, T, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, F, T, T, E, F, E, F, F] [([T, E, T, F, T, F, T, T, E, F, E, F, F], [T, F, T, E, T, F, T, T, E, F, E, F, F]), ([T, T, E, F, T, F, T, E, T, F, E, F, F], [T, T, E, F, T, F, T, E, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_879 (And.intro z_191 trivial))

theorem z_881 : le (tf [T, T, T, F, E, F, T, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, T, E, E, F, F, F] [([T, T, E, F, T, F, T, T, E, E, F, F, F], [T, T, E, F, T, F, T, T, E, F, E, F, F]), ([T, T, T, F, E, F, T, E, T, E, F, F, F], [T, T, T, F, E, F, T, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_880 (And.intro z_598 trivial))

theorem z_882 : le (tf [T, T, T, F, F, T, F, T, F, F, E, E, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, T, F, F, E, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_883 : le (tf [T, T, T, F, F, E, F, T, F, T, F, E, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, F, T, F, E, E] [([T, T, T, F, F, E, F, T, F, E, F, T, E], [T, T, T, F, F, F, E, T, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_53 trivial)

theorem z_884 : le (tf [T, T, T, F, F, T, F, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, F, T, E, F, E] [([T, T, T, F, F, E, F, T, F, T, E, F, E], [T, T, T, F, F, E, F, T, F, T, F, E, E]), ([T, T, T, F, F, T, F, E, F, E, T, F, E], [T, T, T, F, F, T, F, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_883 (And.intro z_201 trivial))

theorem z_885 : le (tf [T, T, T, F, F, T, F, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, F, E, E, T, E, F] [([T, T, T, F, F, T, F, F, E, E, E, T, F], [T, T, T, F, F, T, F, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_199 trivial)

theorem z_886 : le (tf [T, T, T, F, F, T, F, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, F, T, E, E, F] [([T, T, T, F, F, E, F, T, F, T, E, E, F], [T, T, T, F, F, F, E, T, F, T, E, E, F]), ([T, T, T, F, F, T, F, E, F, E, T, E, F], [T, T, T, F, F, T, F, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 (And.intro z_885 trivial))

theorem z_887 : le (tf [F, E, T, T, T, T, F, T, F, F, F, E, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, T, F, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_888 : le (tf [T, F, E, T, T, T, F, T, F, F, F, E, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, T, F, F, F, E, E] [([E, F, T, T, T, T, F, T, F, F, F, E, E], [F, E, T, T, T, T, F, T, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_887 trivial)

theorem z_889 : le (tf [T, T, F, E, T, T, F, T, F, F, F, E, E]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, T, F, F, F, E, E] [([T, E, F, T, T, T, F, T, F, F, F, E, E], [T, F, E, T, T, T, F, T, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_888 trivial)

theorem z_890 : le (tf [E, F, T, T, T, T, F, T, F, F, F, E, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, T, F, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_891 : le (tf [F, T, E, T, T, T, F, T, F, F, E, F, E]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, T, F, F, E, F, E] [([F, E, T, T, T, T, F, T, F, F, E, F, E], [F, E, T, T, T, T, F, T, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_887 trivial)

theorem z_892 : le (tf [T, E, F, T, T, T, F, T, F, F, E, F, E]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, T, F, F, E, F, E] [([E, T, F, T, T, T, F, T, F, F, E, F, E], [F, T, E, T, T, T, F, T, F, F, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_891 trivial)

theorem z_893 : le (tf [F, E, T, T, T, T, F, T, F, F, E, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, T, F, F, E, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_894 : le (tf [F, T, E, T, T, T, F, T, F, F, E, E, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, T, F, F, E, E, F] [([F, E, T, T, T, T, F, T, F, F, E, E, F], [F, E, T, T, T, T, F, T, F, F, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_893 trivial)

theorem z_895 : le (tf [T, E, F, T, T, T, F, T, F, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, T, F, F, E, E, F] [([E, T, F, T, T, T, F, T, F, F, E, E, F], [F, T, E, T, T, T, F, T, F, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_894 trivial)

theorem z_896 : le (tf [F, E, T, T, T, T, F, T, F, F, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, T, F, F, E, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_897 : le (tf [F, T, E, T, T, T, F, T, F, E, F, E, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, T, F, E, F, E, F] [([F, E, T, T, T, T, F, T, F, E, F, E, F], [F, E, T, T, T, T, F, T, F, F, E, E, F]), ([F, T, E, T, T, T, F, E, F, T, F, E, F], [F, T, E, T, T, T, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_896 (And.intro z_258 trivial))

theorem z_898 : le (tf [F, E, F, E, T, T, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, F, T, F, E, F] [([F, E, F, E, T, T, T, T, F, E, F, T, F], [F, E, F, E, T, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_368 trivial)

theorem z_899 : le (tf [F, E, T, F, E, T, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, F, T, F, E, F] [([F, E, E, F, T, T, T, T, F, T, F, E, F], [F, E, F, E, T, T, T, T, F, T, F, E, F]), ([F, E, T, F, E, T, T, T, F, E, F, T, F], [F, E, T, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_898 (And.intro z_369 trivial))

theorem z_900 : le (tf [F, E, T, T, F, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, T, F, E, F] [([F, E, T, E, F, T, T, T, F, T, F, E, F], [F, E, T, F, E, T, T, T, F, T, F, E, F]), ([F, E, T, T, F, E, T, T, F, E, F, T, F], [F, E, T, T, F, E, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_899 (And.intro z_371 trivial))

theorem z_901 : le (tf [F, E, T, T, T, F, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, E, E, F, T, F] [([F, E, T, T, T, F, F, E, T, E, F, T, F], [F, E, T, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_445 trivial)

theorem z_902 : le (tf [F, E, T, T, T, F, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, T, F, T, F, E, F] [([F, E, T, T, E, F, T, T, F, T, F, E, F], [F, E, T, T, F, E, T, T, F, T, F, E, F]), ([F, E, T, T, T, F, E, T, F, E, F, T, F], [F, E, T, T, T, F, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_900 (And.intro z_901 trivial))

theorem z_903 : le (tf [F, E, T, T, T, T, F, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, E, E, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_904 : le (tf [F, E, T, T, T, T, F, E, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, E, F, T, F, E, F] [([F, E, T, T, T, E, F, T, F, T, F, E, F], [F, E, T, T, T, F, E, T, F, T, F, E, F]), ([F, E, T, T, T, T, F, E, F, E, F, T, F], [F, E, T, T, T, T, F, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_902 (And.intro z_903 trivial))

theorem z_905 : le (tf [T, F, E, F, E, T, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, F, T, F, E, F] [([E, F, T, F, E, T, T, T, F, T, F, E, F], [F, E, T, F, E, T, T, T, F, T, F, E, F]), ([T, F, E, F, E, T, T, T, F, E, F, T, F], [T, F, E, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_899 (And.intro z_373 trivial))

theorem z_906 : le (tf [T, F, E, T, F, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, T, F, E, F] [([E, F, T, T, F, E, T, T, F, T, F, E, F], [F, E, T, T, F, E, T, T, F, T, F, E, F]), ([T, F, E, E, F, T, T, T, F, T, F, E, F], [T, F, E, F, E, T, T, T, F, T, F, E, F]), ([T, F, E, T, F, E, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_900 (And.intro z_905 (And.intro z_375 trivial)))

theorem z_907 : le (tf [T, F, E, T, T, F, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, E, E, F, T, F] [([E, F, T, T, T, F, F, T, E, E, F, T, F], [F, E, T, T, T, F, F, T, E, E, F, T, F]), ([T, F, E, T, T, F, F, E, T, E, F, T, F], [T, F, E, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_901 (And.intro z_449 trivial))

theorem z_908 : le (tf [T, F, E, T, T, F, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, T, F, T, F, E, F] [([E, F, T, T, T, F, E, T, F, T, F, E, F], [F, E, T, T, T, F, E, T, F, T, F, E, F]), ([T, F, E, T, E, F, T, T, F, T, F, E, F], [T, F, E, T, F, E, T, T, F, T, F, E, F]), ([T, F, E, T, T, F, E, T, F, E, F, T, F], [T, F, E, T, T, F, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_902 (And.intro z_906 (And.intro z_907 trivial)))

theorem z_909 : le (tf [T, F, E, T, T, T, F, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, E, E, F, T, F] [([E, F, T, T, T, T, F, F, E, E, F, T, F], [F, E, T, T, T, T, F, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_903 trivial)

theorem z_910 : le (tf [T, F, E, T, T, T, F, E, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, E, F, T, F, E, F] [([E, F, T, T, T, T, F, E, F, T, F, E, F], [F, E, T, T, T, T, F, E, F, T, F, E, F]), ([T, F, E, T, T, E, F, T, F, T, F, E, F], [T, F, E, T, T, F, E, T, F, T, F, E, F]), ([T, F, E, T, T, T, F, E, F, E, F, T, F], [T, F, E, T, T, T, F, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_904 (And.intro z_908 (And.intro z_909 trivial)))

theorem z_911 : le (tf [T, E, F, T, T, T, F, T, F, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, T, F, E, F, E, F] [([E, T, F, T, T, T, F, T, F, E, F, E, F], [F, T, E, T, T, T, F, T, F, E, F, E, F]), ([T, E, F, T, T, T, F, E, F, T, F, E, F], [T, F, E, T, T, T, F, E, F, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_897 (And.intro z_910 trivial))

theorem z_912 : le (tf [T, T, F, F, E, E, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, E, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_913 : le (tf [T, T, F, F, E, E, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, F, E, T, F, T, F] [([T, T, F, F, E, E, E, F, T, T, F, T, F], [T, T, F, F, E, E, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_912 trivial)

theorem z_914 : le (tf [T, T, F, F, E, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, E, F, T, F] [([T, T, F, F, E, E, T, E, F, T, F, T, F], [T, T, F, F, E, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_913 trivial)

theorem z_915 : le (tf [T, T, F, E, F, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, T, F, T, F, E, F] [([T, E, F, T, F, E, T, T, F, T, F, E, F], [T, F, E, T, F, E, T, T, F, T, F, E, F]), ([T, T, F, E, F, E, T, T, F, E, F, T, F], [T, T, F, F, E, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_906 (And.intro z_914 trivial))

theorem z_916 : le (tf [T, T, F, F, E, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, T, E, E, F, T, F] [([T, T, F, F, E, T, F, E, T, E, F, T, F], [T, T, F, F, E, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 trivial)

theorem z_917 : le (tf [T, T, F, F, F, E, E, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, E, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_918 : le (tf [T, T, F, F, E, F, E, T, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, E, T, F, T, F] [([T, T, F, F, E, F, E, E, T, T, F, T, F], [T, T, F, F, F, E, E, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_917 trivial)

theorem z_919 : le (tf [T, T, F, F, E, T, F, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, E, T, F, T, F] [([T, T, F, F, E, E, F, T, E, T, F, T, F], [T, T, F, F, E, F, E, T, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_918 trivial)

theorem z_920 : le (tf [T, T, F, F, T, E, E, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, F, E, T, F, T, F] [([T, T, F, F, E, T, E, F, E, T, F, T, F], [T, T, F, F, E, T, F, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_919 trivial)

theorem z_921 : le (tf [T, T, F, F, T, E, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, T, F, E, F, T, F] [([T, T, F, F, E, T, E, T, F, E, F, T, F], [T, T, F, F, E, T, F, T, E, E, F, T, F]), ([T, T, F, F, T, E, E, E, F, T, F, T, F], [T, T, F, F, T, E, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_916 (And.intro z_920 trivial))

theorem z_922 : le (tf [T, T, F, E, T, F, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, T, F, T, F, E, F] [([T, E, F, T, T, F, E, T, F, T, F, E, F], [T, F, E, T, T, F, E, T, F, T, F, E, F]), ([T, T, F, E, E, F, T, T, F, T, F, E, F], [T, T, F, E, F, E, T, T, F, T, F, E, F]), ([T, T, F, E, T, F, E, T, F, E, F, T, F], [T, T, F, F, T, E, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_908 (And.intro z_915 (And.intro z_921 trivial)))

theorem z_923 : le (tf [T, T, F, E, T, T, F, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, E, E, F, T, F] [([T, E, F, T, T, T, F, F, E, E, F, T, F], [T, F, E, T, T, T, F, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_909 trivial)

theorem z_924 : le (tf [T, T, F, E, T, T, F, E, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, E, F, T, F, E, F] [([T, E, F, T, T, T, F, E, F, T, F, E, F], [T, F, E, T, T, T, F, E, F, T, F, E, F]), ([T, T, F, E, T, E, F, T, F, T, F, E, F], [T, T, F, E, T, F, E, T, F, T, F, E, F]), ([T, T, F, E, T, T, F, E, F, E, F, T, F], [T, T, F, E, T, T, F, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_910 (And.intro z_922 (And.intro z_923 trivial)))

theorem z_925 : le (tf [F, E, T, T, T, T, F, T, F, E, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, T, F, E, F, E, F] [([F, E, T, T, T, T, F, E, F, T, F, E, F], [F, E, T, T, T, T, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 trivial)

theorem z_926 : le (tf [F, T, E, T, T, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, E, T, E, F, F] [([F, E, T, T, T, T, F, F, E, T, E, F, F], [F, E, T, T, T, T, F, F, E, T, F, E, F]), ([F, T, E, T, T, T, F, F, E, E, T, F, F], [F, T, E, T, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 (And.intro z_246 trivial))

theorem z_927 : le (tf [F, T, E, T, T, T, F, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, T, F, E, E, F, F] [([F, E, T, T, T, T, F, T, F, E, E, F, F], [F, E, T, T, T, T, F, T, F, E, F, E, F]), ([F, T, E, T, T, T, F, E, F, T, E, F, F], [F, T, E, T, T, T, F, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_925 (And.intro z_926 trivial))

theorem z_928 : le (tf [F, E, F, E, T, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, F, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_929 : le (tf [F, E, T, F, E, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, F, T, F, F, E] [([F, E, E, F, T, T, T, T, F, T, F, F, E], [F, E, F, E, T, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_928 trivial)

theorem z_930 : le (tf [F, E, T, T, F, E, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, T, F, F, E] [([F, E, T, E, F, T, T, T, F, T, F, F, E], [F, E, T, F, E, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_929 trivial)

theorem z_931 : le (tf [F, E, T, T, F, F, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, T, F, E, T, F] [([F, E, T, T, F, F, E, T, E, F, T, T, F], [F, E, T, T, F, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_788 trivial)

theorem z_932 : le (tf [F, E, T, T, F, T, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, E, F, E, T, T, F] [([F, E, T, T, F, E, F, T, F, E, T, T, F], [F, E, T, T, F, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_788 trivial)

theorem z_933 : le (tf [F, E, T, T, F, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, E, T, F, E, T, F] [([F, E, T, T, F, E, F, T, T, F, E, T, F], [F, E, T, T, F, F, E, T, T, F, E, T, F]), ([F, E, T, T, F, T, F, E, E, F, T, T, F], [F, E, T, T, F, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_931 (And.intro z_932 trivial))

theorem z_934 : le (tf [F, E, T, T, F, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, T, E, E, F, T, F] [([F, E, T, T, F, T, F, E, T, E, F, T, F], [F, E, T, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_933 trivial)

theorem z_935 : le (tf [F, E, T, T, F, T, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, E, T, F, T, F, E, F] [([F, E, T, T, F, E, T, T, F, T, F, E, F], [F, E, T, T, F, E, T, T, F, T, F, F, E]), ([F, E, T, T, F, T, E, T, F, E, F, T, F], [F, E, T, T, F, T, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_930 (And.intro z_934 trivial))

theorem z_936 : le (tf [F, F, E, F, E, E, T, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, E, T, T, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_937 : le (tf [F, F, E, E, F, T, E, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, F, T, E, T, T, T, F, T, F] [([F, F, E, E, F, E, T, T, T, T, F, T, F], [F, F, E, F, E, E, T, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_936 trivial)

theorem z_938 : le (tf [F, F, E, E, T, E, F, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, F, T, T, T, F, T, F] [([F, F, E, E, E, T, F, T, T, T, F, T, F], [F, F, E, E, F, T, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_937 trivial)

theorem z_939 : le (tf [F, E, F, E, T, T, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, F, E, T, T, F, T, F] [([F, E, F, E, T, E, F, T, T, T, F, T, F], [F, F, E, E, T, E, F, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_938 trivial)

theorem z_940 : le (tf [F, E, F, E, T, T, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, E, T, F, T, F] [([F, E, F, E, T, T, E, F, T, T, F, T, F], [F, E, F, E, T, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_939 trivial)

theorem z_941 : le (tf [F, E, F, E, T, T, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, T, F, E, F, T, F] [([F, E, F, E, T, T, T, E, F, T, F, T, F], [F, E, F, E, T, T, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_940 trivial)

theorem z_942 : le (tf [F, F, E, E, E, F, T, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, T, T, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_943 : le (tf [F, E, F, E, T, F, E, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, F, E, T, T, T, F, T, F] [([F, E, F, E, E, F, T, T, T, T, F, T, F], [F, F, E, E, E, F, T, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_942 trivial)

theorem z_944 : le (tf [F, E, T, F, E, F, E, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, F, E, T, T, T, F, T, F] [([F, E, E, F, T, F, E, T, T, T, F, T, F], [F, E, F, E, T, F, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_943 trivial)

theorem z_945 : le (tf [F, E, T, F, E, T, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, F, E, T, T, F, T, F] [([F, E, E, F, T, T, F, E, T, T, F, T, F], [F, E, F, E, T, T, F, E, T, T, F, T, F]), ([F, E, T, F, E, E, F, T, T, T, F, T, F], [F, E, T, F, E, F, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_939 (And.intro z_944 trivial))

theorem z_946 : le (tf [F, E, T, F, E, T, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, E, T, F, T, F] [([F, E, E, F, T, T, T, F, E, T, F, T, F], [F, E, F, E, T, T, T, F, E, T, F, T, F]), ([F, E, T, F, E, T, E, F, T, T, F, T, F], [F, E, T, F, E, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_940 (And.intro z_945 trivial))

theorem z_947 : le (tf [F, E, T, F, E, T, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, T, F, E, F, T, F] [([F, E, E, F, T, T, T, T, F, E, F, T, F], [F, E, F, E, T, T, T, T, F, E, F, T, F]), ([F, E, T, F, E, T, T, E, F, T, F, T, F], [F, E, T, F, E, T, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_941 (And.intro z_946 trivial))

theorem z_948 : le (tf [F, E, T, T, F, E, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, F, E, T, T, F, T, F] [([F, E, T, E, F, T, F, E, T, T, F, T, F], [F, E, T, F, E, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_945 trivial)

theorem z_949 : le (tf [F, E, T, T, F, E, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, E, T, F, T, F] [([F, E, T, E, F, T, T, F, E, T, F, T, F], [F, E, T, F, E, T, T, F, E, T, F, T, F]), ([F, E, T, T, F, E, E, F, T, T, F, T, F], [F, E, T, T, F, E, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_946 (And.intro z_948 trivial))

theorem z_950 : le (tf [F, E, T, T, F, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, T, F, E, F, T, F] [([F, E, T, E, F, T, T, T, F, E, F, T, F], [F, E, T, F, E, T, T, T, F, E, F, T, F]), ([F, E, T, T, F, E, T, E, F, T, F, T, F], [F, E, T, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_947 (And.intro z_949 trivial))

theorem z_951 : le (tf [F, E, T, T, T, F, E, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, F, E, T, F, T, F] [([F, E, T, T, E, F, T, F, E, T, F, T, F], [F, E, T, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_949 trivial)

theorem z_952 : le (tf [F, E, T, T, T, F, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, T, F, E, F, T, F] [([F, E, T, T, E, F, T, T, F, E, F, T, F], [F, E, T, T, F, E, T, T, F, E, F, T, F]), ([F, E, T, T, T, F, E, E, F, T, F, T, F], [F, E, T, T, T, F, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_950 (And.intro z_951 trivial))

theorem z_953 : le (tf [F, E, T, T, T, E, F, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, E, F, T, F, T, F, E, F] [([F, E, T, T, E, T, F, T, F, T, F, E, F], [F, E, T, T, F, T, E, T, F, T, F, E, F]), ([F, E, T, T, T, E, F, T, F, E, F, T, F], [F, E, T, T, T, F, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_935 (And.intro z_952 trivial))

theorem z_954 : le (tf [F, E, T, T, T, T, F, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, F, E, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_955 : le (tf [F, E, T, T, T, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, E, F, T, E, F, F] [([F, E, T, T, T, E, F, T, F, T, E, F, F], [F, E, T, T, T, E, F, T, F, T, F, E, F]), ([F, E, T, T, T, T, F, E, F, E, T, F, F], [F, E, T, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_953 (And.intro z_954 trivial))

theorem z_956 : le (tf [T, F, E, F, E, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, F, T, F, F, E] [([E, F, T, F, E, T, T, T, F, T, F, F, E], [F, E, T, F, E, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_929 trivial)

theorem z_957 : le (tf [T, F, E, T, F, E, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, T, F, F, E] [([E, F, T, T, F, E, T, T, F, T, F, F, E], [F, E, T, T, F, E, T, T, F, T, F, F, E]), ([T, F, E, E, F, T, T, T, F, T, F, F, E], [T, F, E, F, E, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_930 (And.intro z_956 trivial))

theorem z_958 : le (tf [T, F, F, T, E, F, E, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, F, E, E, F, T, T, T, F] [([T, F, F, E, T, F, E, E, F, T, T, T, F], [T, F, F, E, T, F, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_162 trivial)

theorem z_959 : le (tf [T, F, F, T, E, E, F, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, T, F, E, T, T, F] [([T, F, F, E, T, E, F, T, F, E, T, T, F], [T, F, F, E, T, F, E, T, F, E, T, T, F]), ([T, F, F, T, E, E, F, E, F, T, T, T, F], [T, F, F, T, E, F, E, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_163 (And.intro z_958 trivial))

theorem z_960 : le (tf [T, F, F, T, E, E, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, T, T, F, E, T, F] [([T, F, F, E, T, E, F, T, T, F, E, T, F], [T, F, F, E, T, F, E, T, T, F, E, T, F]), ([T, F, F, T, E, E, F, T, E, F, T, T, F], [T, F, F, T, E, E, F, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_164 (And.intro z_959 trivial))

theorem z_961 : le (tf [T, F, F, T, E, T, F, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, T, F, E, E, F, T, T, F] [([T, F, F, E, T, T, F, E, E, F, T, T, F], [T, F, F, E, T, T, F, E, F, E, T, T, F]), ([T, F, F, T, E, E, F, T, E, F, T, T, F], [T, F, F, T, E, E, F, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_166 (And.intro z_959 trivial))

theorem z_962 : le (tf [T, F, E, T, F, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, E, T, F, E, T, F] [([E, F, T, T, F, T, F, E, T, F, E, T, F], [F, E, T, T, F, T, F, E, T, F, E, T, F]), ([T, F, E, T, F, E, F, T, T, F, E, T, F], [T, F, F, T, E, E, F, T, T, F, E, T, F]), ([T, F, E, T, F, T, F, E, E, F, T, T, F], [T, F, F, T, E, T, F, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_933 (And.intro z_960 (And.intro z_961 trivial)))

theorem z_963 : le (tf [T, F, E, T, F, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, T, E, E, F, T, F] [([E, F, T, T, F, T, F, T, E, E, F, T, F], [F, E, T, T, F, T, F, T, E, E, F, T, F]), ([T, F, E, T, F, T, F, E, T, E, F, T, F], [T, F, E, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_934 (And.intro z_962 trivial))

theorem z_964 : le (tf [T, F, E, T, F, T, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, E, T, F, T, F, E, F] [([E, F, T, T, F, T, E, T, F, T, F, E, F], [F, E, T, T, F, T, E, T, F, T, F, E, F]), ([T, F, E, T, F, E, T, T, F, T, F, E, F], [T, F, E, T, F, E, T, T, F, T, F, F, E]), ([T, F, E, T, F, T, E, T, F, E, F, T, F], [T, F, E, T, F, T, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_935 (And.intro z_957 (And.intro z_963 trivial)))

theorem z_965 : le (tf [T, F, F, E, F, E, E, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, E, T, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_966 : le (tf [T, F, F, E, E, F, T, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, F, T, E, T, T, F, T, F] [([T, F, F, E, E, F, E, T, T, T, F, T, F], [T, F, F, E, F, E, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_965 trivial)

theorem z_967 : le (tf [T, F, F, E, E, T, E, F, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, E, F, T, T, F, T, F] [([T, F, F, E, E, E, T, F, T, T, F, T, F], [T, F, F, E, E, F, T, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_966 trivial)

theorem z_968 : le (tf [T, F, E, F, E, T, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, E, T, F, T, F] [([E, F, T, F, E, T, T, F, E, T, F, T, F], [F, E, T, F, E, T, T, F, E, T, F, T, F]), ([T, F, E, F, E, T, E, F, T, T, F, T, F], [T, F, F, E, E, T, E, F, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_946 (And.intro z_967 trivial))

theorem z_969 : le (tf [T, F, E, F, E, T, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, T, F, E, F, T, F] [([E, F, T, F, E, T, T, T, F, E, F, T, F], [F, E, T, F, E, T, T, T, F, E, F, T, F]), ([T, F, E, F, E, T, T, E, F, T, F, T, F], [T, F, E, F, E, T, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_947 (And.intro z_968 trivial))

theorem z_970 : le (tf [T, F, F, E, E, E, F, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, E, F, T, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_971 : le (tf [T, F, E, F, E, T, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, F, E, T, T, F, T, F] [([E, F, T, F, E, T, F, E, T, T, F, T, F], [F, E, T, F, E, T, F, E, T, T, F, T, F]), ([T, F, E, F, E, E, F, T, T, T, F, T, F], [T, F, F, E, E, E, F, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_945 (And.intro z_970 trivial))

theorem z_972 : le (tf [T, F, E, T, F, E, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, F, E, T, T, F, T, F] [([E, F, T, T, F, E, F, E, T, T, F, T, F], [F, E, T, T, F, E, F, E, T, T, F, T, F]), ([T, F, E, E, F, T, F, E, T, T, F, T, F], [T, F, E, F, E, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_948 (And.intro z_971 trivial))

theorem z_973 : le (tf [T, F, E, T, F, E, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, E, T, F, T, F] [([E, F, T, T, F, E, T, F, E, T, F, T, F], [F, E, T, T, F, E, T, F, E, T, F, T, F]), ([T, F, E, E, F, T, T, F, E, T, F, T, F], [T, F, E, F, E, T, T, F, E, T, F, T, F]), ([T, F, E, T, F, E, E, F, T, T, F, T, F], [T, F, E, T, F, E, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_949 (And.intro z_968 (And.intro z_972 trivial)))

theorem z_974 : le (tf [T, F, E, T, F, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, T, F, E, F, T, F] [([E, F, T, T, F, E, T, T, F, E, F, T, F], [F, E, T, T, F, E, T, T, F, E, F, T, F]), ([T, F, E, E, F, T, T, T, F, E, F, T, F], [T, F, E, F, E, T, T, T, F, E, F, T, F]), ([T, F, E, T, F, E, T, E, F, T, F, T, F], [T, F, E, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_950 (And.intro z_969 (And.intro z_973 trivial)))

theorem z_975 : le (tf [T, F, E, T, T, F, E, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, F, E, T, F, T, F] [([E, F, T, T, T, F, E, F, E, T, F, T, F], [F, E, T, T, T, F, E, F, E, T, F, T, F]), ([T, F, E, T, E, F, T, F, E, T, F, T, F], [T, F, E, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_951 (And.intro z_973 trivial))

theorem z_976 : le (tf [T, F, E, T, T, F, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, T, F, E, F, T, F] [([E, F, T, T, T, F, E, T, F, E, F, T, F], [F, E, T, T, T, F, E, T, F, E, F, T, F]), ([T, F, E, T, E, F, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, E, F, T, F]), ([T, F, E, T, T, F, E, E, F, T, F, T, F], [T, F, E, T, T, F, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_952 (And.intro z_974 (And.intro z_975 trivial)))

theorem z_977 : le (tf [T, F, E, T, T, E, F, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, E, F, T, F, T, F, E, F] [([E, F, T, T, T, E, F, T, F, T, F, E, F], [F, E, T, T, T, E, F, T, F, T, F, E, F]), ([T, F, E, T, E, T, F, T, F, T, F, E, F], [T, F, E, T, F, T, E, T, F, T, F, E, F]), ([T, F, E, T, T, E, F, T, F, E, F, T, F], [T, F, E, T, T, F, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_953 (And.intro z_964 (And.intro z_976 trivial)))

theorem z_978 : le (tf [T, F, E, T, T, T, F, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, E, E, T, F, F] [([E, F, T, T, T, T, F, F, E, E, T, F, F], [F, E, T, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_954 trivial)

theorem z_979 : le (tf [T, F, E, T, T, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, E, F, T, E, F, F] [([E, F, T, T, T, T, F, E, F, T, E, F, F], [F, E, T, T, T, T, F, E, F, T, E, F, F]), ([T, F, E, T, T, E, F, T, F, T, E, F, F], [T, F, E, T, T, E, F, T, F, T, F, E, F]), ([T, F, E, T, T, T, F, E, F, E, T, F, F], [T, F, E, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_955 (And.intro z_977 (And.intro z_978 trivial)))

theorem z_980 : le (tf [T, E, F, T, T, T, F, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, T, F, E, E, F, F] [([E, T, F, T, T, T, F, T, F, E, E, F, F], [F, T, E, T, T, T, F, T, F, E, E, F, F]), ([T, E, F, T, T, T, F, E, F, T, E, F, F], [T, F, E, T, T, T, F, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_927 (And.intro z_979 trivial))

theorem z_981 : le (tf [T, T, F, F, E, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, T, F, E, F] [([T, T, F, F, E, E, T, T, F, E, F, T, F], [T, T, F, F, E, E, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_466 trivial)

theorem z_982 : le (tf [T, T, F, F, E, T, E, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, F, E, T, F, T, F] [([T, T, F, F, E, E, T, F, E, T, F, T, F], [T, T, F, F, E, F, T, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_834 trivial)

theorem z_983 : le (tf [T, T, F, F, E, T, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, T, F, E, F, T, F] [([T, T, F, F, E, E, T, T, F, E, F, T, F], [T, T, F, F, E, E, T, T, F, F, E, T, F]), ([T, T, F, F, E, T, E, E, F, T, F, T, F], [T, T, F, F, E, T, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_466 (And.intro z_982 trivial))

theorem z_984 : le (tf [T, T, F, E, F, T, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, T, E, T, F, T, F, E, F] [([T, E, F, T, F, T, E, T, F, T, F, E, F], [T, F, E, T, F, T, E, T, F, T, F, E, F]), ([T, T, F, E, F, E, T, T, F, T, F, E, F], [T, T, F, F, E, E, T, T, F, T, F, E, F]), ([T, T, F, E, F, T, E, T, F, E, F, T, F], [T, T, F, F, E, T, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_964 (And.intro z_981 (And.intro z_983 trivial)))

theorem z_985 : le (tf [T, T, F, F, E, F, E, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, E, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_986 : le (tf [T, T, F, F, E, E, F, T, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, T, E, T, F, T, F] [([T, T, F, F, E, E, F, E, T, T, F, T, F], [T, T, F, F, E, F, E, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_985 trivial)

theorem z_987 : le (tf [T, T, F, F, E, E, T, E, F, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, E, F, T, F, T, F] [([T, T, F, F, E, E, E, T, F, T, F, T, F], [T, T, F, F, E, E, F, T, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_986 trivial)

theorem z_988 : le (tf [T, T, F, E, F, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, T, F, E, F, T, F] [([T, E, F, T, F, E, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, E, F, T, F]), ([T, T, F, E, F, E, T, E, F, T, F, T, F], [T, T, F, F, E, E, T, E, F, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_974 (And.intro z_987 trivial))

theorem z_989 : le (tf [T, T, F, F, T, E, E, E, F, T, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, E, F, T, F, T, F] [([T, T, F, F, E, T, E, E, F, T, F, T, F], [T, T, F, F, E, T, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_982 trivial)

theorem z_990 : le (tf [T, T, F, E, T, F, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, T, F, E, F, T, F] [([T, E, F, T, T, F, E, T, F, E, F, T, F], [T, F, E, T, T, F, E, T, F, E, F, T, F]), ([T, T, F, E, E, F, T, T, F, E, F, T, F], [T, T, F, E, F, E, T, T, F, E, F, T, F]), ([T, T, F, E, T, F, E, E, F, T, F, T, F], [T, T, F, F, T, E, E, E, F, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_976 (And.intro z_988 (And.intro z_989 trivial)))

theorem z_991 : le (tf [T, T, F, E, T, E, F, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, E, F, T, F, T, F, E, F] [([T, E, F, T, T, E, F, T, F, T, F, E, F], [T, F, E, T, T, E, F, T, F, T, F, E, F]), ([T, T, F, E, E, T, F, T, F, T, F, E, F], [T, T, F, E, F, T, E, T, F, T, F, E, F]), ([T, T, F, E, T, E, F, T, F, E, F, T, F], [T, T, F, E, T, F, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_977 (And.intro z_984 (And.intro z_990 trivial)))

theorem z_992 : le (tf [T, T, F, E, T, T, F, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, E, E, T, F, F] [([T, E, F, T, T, T, F, F, E, E, T, F, F], [T, F, E, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_978 trivial)

theorem z_993 : le (tf [T, T, F, E, T, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, E, F, T, E, F, F] [([T, E, F, T, T, T, F, E, F, T, E, F, F], [T, F, E, T, T, T, F, E, F, T, E, F, F]), ([T, T, F, E, T, E, F, T, F, T, E, F, F], [T, T, F, E, T, E, F, T, F, T, F, E, F]), ([T, T, F, E, T, T, F, E, F, E, T, F, F], [T, T, F, E, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_979 (And.intro z_991 (And.intro z_992 trivial)))

theorem z_994 : le (tf [F, E, T, T, T, T, F, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, F, T, F, E, E, F, F] [([F, E, T, T, T, T, F, E, F, T, E, F, F], [F, E, T, T, T, T, F, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 trivial)

theorem z_995 : le (tf [F, T, E, T, T, T, F, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, T, E, F, E, F, F] [([F, E, T, T, T, T, F, T, E, F, E, F, F], [F, E, T, T, T, T, F, T, F, E, E, F, F]), ([F, T, E, T, T, T, F, E, T, F, E, F, F], [F, T, E, T, T, T, F, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_994 (And.intro z_259 trivial))

theorem z_996 : le (tf [T, E, F, T, T, T, F, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, T, E, F, E, F, F] [([E, T, F, T, T, T, F, T, E, F, E, F, F], [F, T, E, T, T, T, F, T, E, F, E, F, F]), ([T, E, F, T, T, T, F, E, T, F, E, F, F], [T, F, E, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_995 (And.intro z_758 trivial))

theorem z_997 : le (tf [E, F, T, T, T, T, F, T, F, F, E, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, T, F, F, E, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_998 : le (tf [E, F, T, T, T, T, F, T, F, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, T, F, F, E, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_999 : le (tf [E, F, T, T, T, T, F, T, F, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, T, F, E, F, E, F] [([E, F, T, T, T, T, F, E, F, T, F, E, F], [F, E, T, T, T, T, F, E, F, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_904 trivial)

theorem z_1000 : le (tf [E, F, T, T, T, T, F, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, T, F, E, E, F, F] [([E, F, T, T, T, T, F, E, F, T, E, F, F], [F, E, T, T, T, T, F, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_955 trivial)

theorem z_1001 : le (tf [E, F, T, T, T, T, F, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, T, E, F, E, F, F] [([E, F, T, T, T, T, F, E, T, F, E, F, F], [F, E, T, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_754 trivial)

theorem z_1002 : le (tf [E, F, T, T, T, T, F, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, T, E, E, F, F, F] [([E, F, T, T, T, T, F, E, T, E, F, F, F], [E, F, T, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_297 trivial)

theorem z_1003 : le (tf [T, T, T, F, T, F, F, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, F, E, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1004 : le (tf [T, T, T, F, T, F, F, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, F, E, T, E, F] [([T, T, T, F, T, F, F, E, F, E, E, T, F], [T, T, T, F, T, F, F, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1003 trivial)

theorem z_1005 : le (tf [T, T, T, F, T, F, F, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, T, F, F, E, E, E, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1006 : le (tf [T, T, T, F, F, E, E, F, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, F, T, T, E, F, F] [([T, T, T, F, F, E, E, F, T, E, T, F, F], [T, T, T, F, F, E, F, E, T, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_531 trivial)

theorem z_1007 : le (tf [T, T, T, F, E, F, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, F, E, T, E, F, F] [([T, T, E, F, T, F, T, F, E, T, E, F, F], [T, T, F, E, T, F, T, F, E, T, E, F, F]), ([T, T, T, F, E, F, E, F, T, T, E, F, F], [T, T, T, F, F, E, E, F, T, T, E, F, F]), ([T, T, T, F, E, F, T, F, E, E, T, F, F], [T, T, T, F, F, E, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_867 (And.intro z_1006 (And.intro z_536 trivial)))

theorem z_1008 : le (tf [F, E, T, T, T, F, E, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, E, T, F, T, F, F, E] [([F, E, T, T, E, F, T, T, F, T, F, F, E], [F, E, T, T, F, E, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_930 trivial)

theorem z_1009 : le (tf [T, F, E, T, T, F, E, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, T, F, T, F, F, E] [([E, F, T, T, T, F, E, T, F, T, F, F, E], [F, E, T, T, T, F, E, T, F, T, F, F, E]), ([T, F, E, T, E, F, T, T, F, T, F, F, E], [T, F, E, T, F, E, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1008 (And.intro z_957 trivial))

theorem z_1010 : le (tf [T, F, T, E, E, F, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, T, E, E, F, T, T, F, T, F, F, E] [([T, F, E, T, E, F, T, T, F, T, F, F, E], [T, F, E, T, F, E, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_957 trivial)

theorem z_1011 : le (tf [T, F, F, E, T, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, T, E, E, F, T, F] [([T, F, F, E, T, T, F, E, T, E, F, T, F], [T, F, F, E, T, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_167 trivial)

theorem z_1012 : le (tf [T, F, T, F, E, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, F, T, E, E, F, T, F] [([T, F, E, F, T, T, F, T, E, E, F, T, F], [T, F, F, E, T, T, F, T, E, E, F, T, F]), ([T, F, T, F, E, T, F, E, T, E, F, T, F], [T, F, T, F, E, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1011 (And.intro z_177 trivial))

theorem z_1013 : le (tf [T, F, F, F, E, E, T, T, F, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, T, F, F, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1014 : le (tf [T, F, F, F, E, E, T, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, T, F, T, F, E, T] [([T, F, F, F, E, E, T, T, F, E, F, T, T], [T, F, F, F, E, E, T, T, F, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1013 trivial)

theorem z_1015 : le (tf [T, F, F, F, F, E, E, F, E, T, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, F, E, T, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1016 : le (tf [T, F, F, F, F, E, E, T, F, E, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, T, F, E, T, T, T] [([T, F, F, F, F, E, E, E, F, T, T, T, T], [T, F, F, F, F, E, E, F, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1015 trivial)

theorem z_1017 : le (tf [T, F, F, F, E, F, E, T, F, T, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, T, F, T, E, T, T] [([T, F, F, F, E, F, E, T, F, E, T, T, T], [T, F, F, F, F, E, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1016 trivial)

theorem z_1018 : le (tf [T, F, F, F, E, F, T, E, E, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, T, E, E, T, F, T, T] [([T, F, F, F, E, F, E, T, E, T, F, T, T], [T, F, F, F, E, F, E, T, F, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1017 trivial)

theorem z_1019 : le (tf [T, F, F, F, E, T, E, F, E, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, E, F, E, T, F, T, T] [([T, F, F, F, E, E, T, F, E, T, F, T, T], [T, F, F, F, E, F, T, E, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1018 trivial)

theorem z_1020 : le (tf [T, F, F, F, E, T, E, T, F, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, E, T, F, E, F, T, T] [([T, F, F, F, E, E, T, T, F, E, F, T, T], [T, F, F, F, E, E, T, T, F, F, E, T, T]), ([T, F, F, F, E, T, E, E, F, T, F, T, T], [T, F, F, F, E, T, E, F, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1013 (And.intro z_1019 trivial))

theorem z_1021 : le (tf [T, F, F, E, F, T, E, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, E, T, F, T, F, E, T] [([T, F, F, E, F, E, T, T, F, T, F, E, T], [T, F, F, F, E, E, T, T, F, T, F, E, T]), ([T, F, F, E, F, T, E, T, F, E, F, T, T], [T, F, F, F, E, T, E, T, F, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1014 (And.intro z_1020 trivial))

theorem z_1022 : le (tf [T, F, F, E, E, T, F, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, F, T, F, T, F, T, E] [([T, F, F, E, E, T, F, T, F, T, F, E, T], [T, F, F, E, F, T, E, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1021 trivial)

theorem z_1023 : le (tf [T, F, F, E, T, E, F, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, E, F, T, F, T, E, T, F] [([T, F, F, E, E, T, F, T, F, T, E, T, F], [T, F, F, E, E, T, F, T, F, T, F, T, E]), ([T, F, F, E, T, E, F, T, F, E, T, T, F], [T, F, F, E, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1022 (And.intro z_163 trivial))

theorem z_1024 : le (tf [T, F, F, E, T, T, F, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, E, E, T, F, T, F] [([T, F, F, E, T, E, F, T, E, T, F, T, F], [T, F, F, E, T, E, F, T, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1023 trivial)

theorem z_1025 : le (tf [F, F, F, E, E, F, E, T, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, E, T, T, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1026 : le (tf [F, F, F, E, E, T, F, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, F, E, T, T, F, T, T] [([F, F, F, E, E, E, F, T, T, T, F, T, T], [F, F, F, E, E, F, E, T, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1025 trivial)

theorem z_1027 : le (tf [F, F, F, E, E, T, T, F, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, F, E, T, F, T, T] [([F, F, F, E, E, T, E, F, T, T, F, T, T], [F, F, F, E, E, T, F, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1026 trivial)

theorem z_1028 : le (tf [F, F, F, E, E, T, T, T, F, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, T, F, E, F, T, T] [([F, F, F, E, E, T, T, E, F, T, F, T, T], [F, F, F, E, E, T, T, F, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1027 trivial)

theorem z_1029 : le (tf [F, F, F, F, E, E, F, E, T, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, F, E, T, T, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1030 : le (tf [F, F, F, F, E, E, T, F, E, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, T, F, E, T, T, T, T] [([F, F, F, F, E, E, E, F, T, T, T, T, T], [F, F, F, F, E, E, F, E, T, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1029 trivial)

theorem z_1031 : le (tf [F, F, F, F, E, E, T, T, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, T, T, F, E, T, T, T] [([F, F, F, F, E, E, T, E, F, T, T, T, T], [F, F, F, F, E, E, T, F, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1030 trivial)

theorem z_1032 : le (tf [F, F, F, F, E, T, E, E, F, T, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, T, E, E, F, T, T, T, T] [([F, F, F, F, E, E, T, E, F, T, T, T, T], [F, F, F, F, E, E, T, F, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1030 trivial)

theorem z_1033 : le (tf [F, F, F, E, F, T, E, T, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, T, E, T, F, E, T, T, T] [([F, F, F, E, F, E, T, T, F, E, T, T, T], [F, F, F, F, E, E, T, T, F, E, T, T, T]), ([F, F, F, E, F, T, E, E, F, T, T, T, T], [F, F, F, F, E, T, E, E, F, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1031 (And.intro z_1032 trivial))

theorem z_1034 : le (tf [F, F, F, E, E, T, F, T, F, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, F, T, F, T, E, T, T] [([F, F, F, E, E, T, F, T, F, E, T, T, T], [F, F, F, E, F, T, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1033 trivial)

theorem z_1035 : le (tf [F, F, F, F, E, E, E, T, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, F, E, E, E, T, T, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1036 : le (tf [F, F, F, E, F, E, T, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, T, E, T, T, F, T, T] [([F, F, F, E, F, E, E, T, T, T, F, T, T], [F, F, F, F, E, E, E, T, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1035 trivial)

theorem z_1037 : le (tf [F, F, F, E, T, F, E, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, F, E, E, T, T, F, T, T] [([F, F, F, E, E, F, T, E, T, T, F, T, T], [F, F, F, E, F, E, T, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1036 trivial)

theorem z_1038 : le (tf [F, F, F, E, T, E, F, T, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, E, F, T, E, T, F, T, T] [([F, F, F, E, E, T, F, T, E, T, F, T, T], [F, F, F, E, E, T, F, T, F, T, E, T, T]), ([F, F, F, E, T, E, F, E, T, T, F, T, T], [F, F, F, E, T, F, E, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1034 (And.intro z_1037 trivial))

theorem z_1039 : le (tf [F, F, F, E, T, E, T, E, F, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, E, T, E, F, T, F, T, T] [([F, F, F, E, E, T, T, E, F, T, F, T, T], [F, F, F, E, E, T, T, F, E, T, F, T, T]), ([F, F, F, E, T, E, E, T, F, T, F, T, T], [F, F, F, E, T, E, F, T, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1027 (And.intro z_1038 trivial))

theorem z_1040 : le (tf [F, F, E, F, T, E, T, T, F, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, T, E, T, T, F, E, F, T, T] [([F, F, E, F, E, T, T, T, F, E, F, T, T], [F, F, F, E, E, T, T, T, F, E, F, T, T]), ([F, F, E, F, T, E, T, E, F, T, F, T, T], [F, F, F, E, T, E, T, E, F, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1028 (And.intro z_1039 trivial))

theorem z_1041 : le (tf [F, F, E, E, T, F, T, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, T, F, T, F, E, T] [([F, F, E, E, T, F, T, T, F, E, F, T, T], [F, F, E, F, T, E, T, T, F, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1040 trivial)

theorem z_1042 : le (tf [F, E, F, E, T, F, T, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, T, F, T, T, F, T, F, T, E] [([F, E, F, E, T, F, T, T, F, T, F, E, T], [F, F, E, E, T, F, T, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1041 trivial)

theorem z_1043 : le (tf [F, F, E, F, E, T, T, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, F, T, F, E, T] [([F, F, E, F, E, T, T, T, F, E, F, T, T], [F, F, F, E, E, T, T, T, F, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1028 trivial)

theorem z_1044 : le (tf [F, F, E, F, E, T, T, T, F, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, F, F, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1045 : le (tf [F, F, E, T, F, E, T, T, F, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, F, F, E, T, T] [([F, F, E, E, F, T, T, T, F, F, E, T, T], [F, F, E, F, E, T, T, T, F, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1044 trivial)

theorem z_1046 : le (tf [F, F, E, T, F, E, T, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, F, T, F, E, T] [([F, F, E, E, F, T, T, T, F, T, F, E, T], [F, F, E, F, E, T, T, T, F, T, F, E, T]), ([F, F, E, T, F, E, T, T, F, E, F, T, T], [F, F, E, T, F, E, T, T, F, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1043 (And.intro z_1045 trivial))

theorem z_1047 : le (tf [F, F, T, F, E, F, E, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, E, F, E, E, T, T, F, T, T] [([F, F, E, F, T, F, E, E, T, T, F, T, T], [F, F, F, E, T, F, E, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1037 trivial)

theorem z_1048 : le (tf [F, F, T, F, E, E, F, T, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, E, E, F, T, E, T, F, T, T] [([F, F, E, F, T, E, F, T, E, T, F, T, T], [F, F, F, E, T, E, F, T, E, T, F, T, T]), ([F, F, T, F, E, E, F, E, T, T, F, T, T], [F, F, T, F, E, F, E, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1038 (And.intro z_1047 trivial))

theorem z_1049 : le (tf [F, F, T, F, E, E, T, E, F, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, F, E, E, T, E, F, T, F, T, T] [([F, F, E, F, T, E, T, E, F, T, F, T, T], [F, F, F, E, T, E, T, E, F, T, F, T, T]), ([F, F, T, F, E, E, E, T, F, T, F, T, T], [F, F, T, F, E, E, F, T, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1039 (And.intro z_1048 trivial))

theorem z_1050 : le (tf [F, F, T, E, F, E, T, T, F, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, T, E, F, E, T, T, F, E, F, T, T] [([F, F, E, T, F, E, T, T, F, E, F, T, T], [F, F, E, T, F, E, T, T, F, F, E, T, T]), ([F, F, T, E, F, E, T, E, F, T, F, T, T], [F, F, T, F, E, E, T, E, F, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1045 (And.intro z_1049 trivial))

theorem z_1051 : le (tf [F, F, T, E, E, F, T, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, T, F, T, F, E, T] [([F, F, E, T, E, F, T, T, F, T, F, E, T], [F, F, E, T, F, E, T, T, F, T, F, E, T]), ([F, F, T, E, E, F, T, T, F, E, F, T, T], [F, F, T, E, F, E, T, T, F, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1046 (And.intro z_1050 trivial))

theorem z_1052 : le (tf [F, E, T, F, E, F, T, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, F, T, T, F, T, F, T, E] [([F, E, E, F, T, F, T, T, F, T, F, T, E], [F, E, F, E, T, F, T, T, F, T, F, T, E]), ([F, E, T, F, E, F, T, T, F, T, F, E, T], [F, F, T, E, E, F, T, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1042 (And.intro z_1051 trivial))

theorem z_1053 : le (tf [F, F, E, T, T, F, F, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, F, E, F, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1054 : le (tf [F, F, T, E, T, F, F, E, E, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, T, E, T, F, F, E, E, F, T, T, T] [([F, F, E, T, T, F, F, E, E, F, T, T, T], [F, F, E, T, T, F, F, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1053 trivial)

theorem z_1055 : le (tf [F, E, T, F, T, F, F, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, F, E, T, F, E, T, T] [([F, E, T, F, T, F, F, E, E, F, T, T, T], [F, F, T, E, T, F, F, E, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1054 trivial)

theorem z_1056 : le (tf [F, E, T, F, T, F, F, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, F, T, E, E, F, T, T] [([F, E, T, F, T, F, F, E, T, E, F, T, T], [F, E, T, F, T, F, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1055 trivial)

theorem z_1057 : le (tf [F, E, T, F, T, F, E, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, T, F, T, F, E, T] [([F, E, T, F, E, F, T, T, F, T, F, E, T], [F, F, T, E, E, F, T, T, F, T, F, E, T]), ([F, E, T, F, T, F, E, T, F, E, F, T, T], [F, E, T, F, T, F, F, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1051 (And.intro z_1056 trivial))

theorem z_1058 : le (tf [E, F, T, F, T, F, E, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, E, T, F, T, F, T, E] [([E, F, T, F, E, F, T, T, F, T, F, T, E], [F, E, T, F, E, F, T, T, F, T, F, T, E]), ([E, F, T, F, T, F, E, T, F, T, F, E, T], [F, E, T, F, T, F, E, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1052 (And.intro z_1057 trivial))

theorem z_1059 : le (tf [T, F, F, E, E, F, T, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, F, T, T, F, T, E, T, F] [([T, F, F, E, E, F, T, T, F, E, T, T, F], [T, F, F, E, F, E, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_157 trivial)

theorem z_1060 : le (tf [T, F, E, F, T, F, E, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, F, E, T, F, T, E, T, F] [([E, F, T, F, T, F, E, T, F, T, E, T, F], [E, F, T, F, T, F, E, T, F, T, F, T, E]), ([T, F, E, F, E, F, T, T, F, T, E, T, F], [T, F, F, E, E, F, T, T, F, T, E, T, F]), ([T, F, E, F, T, F, E, T, F, E, T, T, F], [T, F, F, E, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1058 (And.intro z_1059 (And.intro z_163 trivial)))

theorem z_1061 : le (tf [T, F, T, F, F, E, E, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, E, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1062 : le (tf [T, F, T, F, E, F, E, T, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, F, E, T, E, T, F, T, F] [([T, F, E, F, T, F, E, T, E, T, F, T, F], [T, F, E, F, T, F, E, T, F, T, E, T, F]), ([T, F, T, F, E, F, E, E, T, T, F, T, F], [T, F, T, F, F, E, E, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1060 (And.intro z_1061 trivial))

theorem z_1063 : le (tf [T, F, T, F, E, T, F, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, F, E, E, T, F, T, F] [([T, F, E, F, T, T, F, E, E, T, F, T, F], [T, F, F, E, T, T, F, E, E, T, F, T, F]), ([T, F, T, F, E, E, F, T, E, T, F, T, F], [T, F, T, F, E, F, E, T, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1024 (And.intro z_1062 trivial))

theorem z_1064 : le (tf [T, F, T, F, T, E, E, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, E, F, E, T, F, T, F] [([T, F, T, F, E, T, E, F, E, T, F, T, F], [T, F, T, F, E, T, F, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1063 trivial)

theorem z_1065 : le (tf [T, F, T, F, T, E, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, E, T, F, E, F, T, F] [([T, F, T, F, E, T, E, T, F, E, F, T, F], [T, F, T, F, E, T, F, T, E, E, F, T, F]), ([T, F, T, F, T, E, E, E, F, T, F, T, F], [T, F, T, F, T, E, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1012 (And.intro z_1064 trivial))

theorem z_1066 : le (tf [T, F, T, E, T, F, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, E, T, F, T, F, E, F] [([T, F, E, T, T, F, E, T, F, T, F, E, F], [T, F, E, T, T, F, E, T, F, T, F, F, E]), ([T, F, T, E, E, F, T, T, F, T, F, E, F], [T, F, T, E, E, F, T, T, F, T, F, F, E]), ([T, F, T, E, T, F, E, T, F, E, F, T, F], [T, F, T, F, T, E, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1009 (And.intro z_1010 (And.intro z_1065 trivial)))

theorem z_1067 : le (tf [F, E, T, F, T, F, F, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, F, E, T, T, F, E, T] [([F, E, T, F, T, F, F, E, T, E, F, T, T], [F, E, T, F, T, F, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1055 trivial)

theorem z_1068 : le (tf [E, F, T, F, T, F, F, E, T, T, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, F, E, T, T, F, T, E] [([E, F, T, F, T, F, F, E, T, T, F, E, T], [F, E, T, F, T, F, F, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1067 trivial)

theorem z_1069 : le (tf [F, E, T, F, T, F, T, F, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, T, F, E, F, E, T, T] [([F, E, T, F, T, F, E, F, T, F, E, T, T], [F, E, T, F, T, F, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1055 trivial)

theorem z_1070 : le (tf [F, E, T, F, T, F, T, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, T, F, E, T, F, E, T] [([F, E, T, F, T, F, E, F, T, T, F, E, T], [F, E, T, F, T, F, F, E, T, T, F, E, T]), ([F, E, T, F, T, F, T, F, E, E, F, T, T], [F, E, T, F, T, F, T, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1067 (And.intro z_1069 trivial))

theorem z_1071 : le (tf [E, F, T, F, T, F, T, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, T, F, E, T, F, T, E] [([E, F, T, F, T, F, E, F, T, T, F, T, E], [E, F, T, F, T, F, F, E, T, T, F, T, E]), ([E, F, T, F, T, F, T, F, E, T, F, E, T], [F, E, T, F, T, F, T, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1068 (And.intro z_1070 trivial))

theorem z_1072 : le (tf [E, F, T, F, T, F, T, F, T, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, T, F, T, E, E, T, F] [([E, F, T, F, T, F, T, F, E, T, E, T, F], [E, F, T, F, T, F, T, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1071 trivial)

theorem z_1073 : le (tf [T, F, E, F, T, F, T, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, F, T, E, T, F, E, T, F] [([E, F, T, F, T, F, T, E, T, F, E, T, F], [E, F, T, F, T, F, T, F, T, E, E, T, F]), ([T, F, E, F, T, F, E, T, T, F, E, T, F], [T, F, F, E, T, F, E, T, T, F, E, T, F]), ([T, F, E, F, T, F, T, E, E, F, T, T, F], [T, F, F, E, T, F, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1072 (And.intro z_164 (And.intro z_812 trivial)))

theorem z_1074 : le (tf [T, F, T, F, E, F, T, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, F, T, E, E, F, T, T, F] [([T, F, E, F, T, F, T, E, E, F, T, T, F], [T, F, F, E, T, F, T, E, E, F, T, T, F]), ([T, F, T, F, E, F, E, T, E, F, T, T, F], [T, F, T, F, F, E, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_812 (And.intro z_171 trivial))

theorem z_1075 : le (tf [T, F, T, F, E, E, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, E, T, F, T, F, E, T, F] [([T, F, E, F, T, E, T, F, T, F, E, T, F], [T, F, E, F, T, F, T, E, T, F, E, T, F]), ([T, F, T, F, E, E, T, F, E, F, T, T, F], [T, F, T, F, E, F, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1073 (And.intro z_1074 trivial))

theorem z_1076 : le (tf [T, F, T, E, F, E, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, F, E, T, F, T, F, T, E, F] [([T, F, E, T, F, E, T, F, T, F, T, E, F], [T, F, E, T, F, E, T, F, T, F, T, F, E]), ([T, F, T, E, F, E, T, F, T, F, E, T, F], [T, F, T, F, E, E, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_827 (And.intro z_1075 trivial))

theorem z_1077 : le (tf [T, F, T, E, T, F, E, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, E, F, T, F, T, E, F] [([T, F, E, T, T, F, E, F, T, F, T, E, F], [T, F, E, T, T, F, E, F, T, F, T, F, E]), ([T, F, T, E, E, F, T, F, T, F, T, E, F], [T, F, T, E, F, E, T, F, T, F, T, E, F]), ([T, F, T, E, T, F, E, F, T, F, E, T, F], [T, F, T, F, T, E, E, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_828 (And.intro z_1076 (And.intro z_180 trivial)))

theorem z_1078 : le (tf [T, F, T, E, T, F, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, T, F, E, E, T, F, F] [([T, F, E, T, T, F, T, F, E, E, T, F, F], [T, F, E, T, T, F, T, F, E, F, T, E, F]), ([T, F, T, E, T, F, E, F, T, E, T, F, F], [T, F, T, E, T, F, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_830 (And.intro z_1077 trivial))

theorem z_1079 : le (tf [T, F, T, E, T, F, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, T, E, F, T, E, F, F] [([T, F, E, T, T, F, T, E, F, T, E, F, F], [T, F, E, T, T, F, T, F, E, T, E, F, F]), ([T, F, T, E, T, F, E, T, F, T, E, F, F], [T, F, T, E, T, F, E, T, F, T, F, E, F]), ([T, F, T, E, T, F, T, E, F, E, T, F, F], [T, F, T, E, T, F, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_831 (And.intro z_1066 (And.intro z_1078 trivial)))

theorem z_1080 : le (tf [F, F, E, E, T, T, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, T, F, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1081 : le (tf [F, E, F, T, E, T, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, F, F, E, T, F] [([F, E, F, E, T, T, T, T, F, F, E, T, F], [F, F, E, E, T, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1080 trivial)

theorem z_1082 : le (tf [F, E, F, T, E, T, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, F, T, F, E, F] [([F, E, F, E, T, T, T, T, F, T, F, E, F], [F, E, F, E, T, T, T, T, F, T, F, F, E]), ([F, E, F, T, E, T, T, T, F, E, F, T, F], [F, E, F, T, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_928 (And.intro z_1081 trivial))

theorem z_1083 : le (tf [F, E, T, E, F, T, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, F, T, F, E, F] [([F, E, E, T, F, T, T, T, F, T, F, E, F], [F, E, F, T, E, T, T, T, F, T, F, E, F]), ([F, E, T, E, F, T, T, T, F, E, F, T, F], [F, E, T, F, E, T, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1082 (And.intro z_947 trivial))

theorem z_1084 : le (tf [E, F, T, T, F, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, F, T, F, E, F] [([E, F, T, E, F, T, T, T, F, T, F, E, F], [F, E, T, E, F, T, T, T, F, T, F, E, F]), ([E, F, T, T, F, E, T, T, F, E, F, T, F], [F, E, T, T, F, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1083 (And.intro z_950 trivial))

theorem z_1085 : le (tf [E, F, T, F, T, E, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, F, T, F, T, E, T, T, F, T, F, F, E] [([E, F, T, F, E, T, T, T, F, T, F, F, E], [F, E, T, F, E, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_929 trivial)

theorem z_1086 : le (tf [T, F, E, E, T, F, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, E, T, F, T, T, F, T, F, F, E] [([E, F, T, E, T, F, T, T, F, T, F, F, E], [E, F, T, F, T, E, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1085 trivial)

theorem z_1087 : le (tf [T, F, E, T, E, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, E, F, T, T, F, T, F, E, F] [([E, F, T, T, E, F, T, T, F, T, F, E, F], [E, F, T, T, F, E, T, T, F, T, F, E, F]), ([T, F, E, E, T, F, T, T, F, T, F, E, F], [T, F, E, E, T, F, T, T, F, T, F, F, E]), ([T, F, E, T, E, F, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1084 (And.intro z_1086 (And.intro z_974 trivial)))

theorem z_1088 : le (tf [T, T, F, E, E, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, E, F, T, T, F, T, F, E, F] [([T, E, F, T, E, F, T, T, F, T, F, E, F], [T, F, E, T, E, F, T, T, F, T, F, E, F]), ([T, T, F, E, E, F, T, T, F, E, F, T, F], [T, T, F, E, F, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1087 (And.intro z_988 trivial))

theorem z_1089 : le (tf [T, T, E, F, T, F, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, F, E, T, F, T, F, E, F] [([T, E, T, F, T, F, E, T, F, T, F, E, F], [T, F, T, E, T, F, E, T, F, T, F, E, F]), ([T, T, E, F, E, F, T, T, F, T, F, E, F], [T, T, F, E, E, F, T, T, F, T, F, E, F]), ([T, T, E, F, T, F, E, T, F, E, F, T, F], [T, T, F, E, T, F, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1066 (And.intro z_1088 (And.intro z_990 trivial)))

theorem z_1090 : le (tf [E, F, T, T, T, F, F, E, T, E, T, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, E, T, E, T, F, F] [([E, F, T, T, T, F, F, E, E, T, T, F, F], [F, E, T, T, T, F, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_450 trivial)

theorem z_1091 : le (tf [E, F, T, T, F, E, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, F, T, F, T, E, F] [([E, F, T, E, F, T, T, F, T, F, T, E, F], [E, F, T, F, E, T, T, F, T, F, T, E, F]), ([E, F, T, T, F, E, T, F, T, F, E, T, F], [F, E, T, T, F, E, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_335 (And.intro z_790 trivial))

theorem z_1092 : le (tf [F, F, F, E, F, E, E, T, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, E, T, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1093 : le (tf [F, F, F, E, E, F, T, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, T, E, T, T, T, F, T] [([F, F, F, E, E, F, E, T, T, T, T, F, T], [F, F, F, E, F, E, E, T, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1092 trivial)

theorem z_1094 : le (tf [F, F, F, E, E, T, E, F, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, E, F, T, T, T, F, T] [([F, F, F, E, E, E, T, F, T, T, T, F, T], [F, F, F, E, E, F, T, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1093 trivial)

theorem z_1095 : le (tf [F, F, E, F, T, E, E, F, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, F, T, E, E, F, T, T, T, F, T] [([F, F, E, F, E, T, E, F, T, T, T, F, T], [F, F, F, E, E, T, E, F, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1094 trivial)

theorem z_1096 : le (tf [F, F, E, E, T, F, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, F, E, T, T, F, T] [([F, F, E, E, T, F, E, F, T, T, T, F, T], [F, F, E, F, T, E, E, F, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1095 trivial)

theorem z_1097 : le (tf [F, F, E, E, T, F, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, T, F, E, T, F, T] [([F, F, E, E, T, F, T, E, F, T, T, F, T], [F, F, E, E, T, F, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1096 trivial)

theorem z_1098 : le (tf [F, F, E, E, T, F, T, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, T, T, F, E, F, T] [([F, F, E, E, T, F, T, T, E, F, T, F, T], [F, F, E, E, T, F, T, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1097 trivial)

theorem z_1099 : le (tf [F, E, F, E, T, F, T, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, T, F, T, T, T, F, T, F, E] [([F, E, F, E, T, F, T, T, T, F, E, F, T], [F, F, E, E, T, F, T, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1098 trivial)

theorem z_1100 : le (tf [F, F, E, F, E, T, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, F, E, T, T, F, T] [([F, F, E, F, E, T, E, F, T, T, T, F, T], [F, F, F, E, E, T, E, F, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1094 trivial)

theorem z_1101 : le (tf [F, F, E, F, E, T, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, F, E, T, F, T] [([F, F, E, F, E, T, T, E, F, T, T, F, T], [F, F, E, F, E, T, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1100 trivial)

theorem z_1102 : le (tf [F, F, E, F, E, T, T, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, T, F, E, F, T] [([F, F, E, F, E, T, T, T, E, F, T, F, T], [F, F, E, F, E, T, T, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1101 trivial)

theorem z_1103 : le (tf [F, F, F, E, E, E, F, T, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, F, T, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1104 : le (tf [F, F, E, F, E, T, F, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, F, E, T, T, T, F, T] [([F, F, E, F, E, E, F, T, T, T, T, F, T], [F, F, F, E, E, E, F, T, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1103 trivial)

theorem z_1105 : le (tf [F, F, E, T, F, E, F, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, F, E, T, T, T, F, T] [([F, F, E, E, F, T, F, E, T, T, T, F, T], [F, F, E, F, E, T, F, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1104 trivial)

theorem z_1106 : le (tf [F, F, E, T, F, E, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, F, E, T, T, F, T] [([F, F, E, E, F, T, T, F, E, T, T, F, T], [F, F, E, F, E, T, T, F, E, T, T, F, T]), ([F, F, E, T, F, E, E, F, T, T, T, F, T], [F, F, E, T, F, E, F, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1100 (And.intro z_1105 trivial))

theorem z_1107 : le (tf [F, F, E, T, F, E, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, F, E, T, F, T] [([F, F, E, E, F, T, T, T, F, E, T, F, T], [F, F, E, F, E, T, T, T, F, E, T, F, T]), ([F, F, E, T, F, E, T, E, F, T, T, F, T], [F, F, E, T, F, E, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1101 (And.intro z_1106 trivial))

theorem z_1108 : le (tf [F, F, E, T, F, E, T, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, T, F, E, F, T] [([F, F, E, E, F, T, T, T, T, F, E, F, T], [F, F, E, F, E, T, T, T, T, F, E, F, T]), ([F, F, E, T, F, E, T, T, E, F, T, F, T], [F, F, E, T, F, E, T, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1102 (And.intro z_1107 trivial))

theorem z_1109 : le (tf [F, F, T, E, F, E, E, F, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, T, E, F, E, E, F, T, T, T, F, T] [([F, F, E, T, F, E, E, F, T, T, T, F, T], [F, F, E, T, F, E, F, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1105 trivial)

theorem z_1110 : le (tf [F, F, T, E, E, F, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, F, E, T, T, F, T] [([F, F, E, T, E, F, T, F, E, T, T, F, T], [F, F, E, T, F, E, T, F, E, T, T, F, T]), ([F, F, T, E, E, F, E, F, T, T, T, F, T], [F, F, T, E, F, E, E, F, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1106 (And.intro z_1109 trivial))

theorem z_1111 : le (tf [F, F, T, E, E, F, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, T, F, E, T, F, T] [([F, F, E, T, E, F, T, T, F, E, T, F, T], [F, F, E, T, F, E, T, T, F, E, T, F, T]), ([F, F, T, E, E, F, T, E, F, T, T, F, T], [F, F, T, E, E, F, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1107 (And.intro z_1110 trivial))

theorem z_1112 : le (tf [F, F, T, E, E, F, T, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, T, T, F, E, F, T] [([F, F, E, T, E, F, T, T, T, F, E, F, T], [F, F, E, T, F, E, T, T, T, F, E, F, T]), ([F, F, T, E, E, F, T, T, E, F, T, F, T], [F, F, T, E, E, F, T, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1108 (And.intro z_1111 trivial))

theorem z_1113 : le (tf [F, E, T, F, E, F, T, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, F, T, T, T, F, T, F, E] [([F, E, E, F, T, F, T, T, T, F, T, F, E], [F, E, F, E, T, F, T, T, T, F, T, F, E]), ([F, E, T, F, E, F, T, T, T, F, E, F, T], [F, F, T, E, E, F, T, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1099 (And.intro z_1112 trivial))

theorem z_1114 : le (tf [F, F, E, T, T, F, E, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, E, F, E, T, T, F, T] [([F, F, E, T, E, F, T, F, E, T, T, F, T], [F, F, E, T, F, E, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1106 trivial)

theorem z_1115 : le (tf [F, F, T, E, T, F, E, E, F, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, T, E, T, F, E, E, F, T, T, F, T] [([F, F, E, T, T, F, E, E, F, T, T, F, T], [F, F, E, T, T, F, E, F, E, T, T, F, T]), ([F, F, T, E, E, F, T, E, F, T, T, F, T], [F, F, T, E, E, F, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1114 (And.intro z_1110 trivial))

theorem z_1116 : le (tf [F, E, T, F, T, F, E, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, T, F, E, T, F, T] [([F, E, T, F, E, F, T, T, F, E, T, F, T], [F, F, T, E, E, F, T, T, F, E, T, F, T]), ([F, E, T, F, T, F, E, E, F, T, T, F, T], [F, F, T, E, T, F, E, E, F, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1111 (And.intro z_1115 trivial))

theorem z_1117 : le (tf [F, E, T, F, T, F, E, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, T, T, F, E, F, T] [([F, E, T, F, E, F, T, T, T, F, E, F, T], [F, F, T, E, E, F, T, T, T, F, E, F, T]), ([F, E, T, F, T, F, E, T, E, F, T, F, T], [F, E, T, F, T, F, E, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1112 (And.intro z_1116 trivial))

theorem z_1118 : le (tf [E, F, T, F, T, F, E, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, E, T, T, F, T, F, E] [([E, F, T, F, E, F, T, T, T, F, T, F, E], [F, E, T, F, E, F, T, T, T, F, T, F, E]), ([E, F, T, F, T, F, E, T, T, F, E, F, T], [F, E, T, F, T, F, E, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1113 (And.intro z_1117 trivial))

theorem z_1119 : le (tf [E, F, T, F, T, F, T, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, T, E, T, F, T, E, F] [([E, F, T, F, T, F, E, T, T, F, T, E, F], [E, F, T, F, T, F, E, T, T, F, T, F, E]), ([E, F, T, F, T, F, T, E, T, F, E, T, F], [E, F, T, F, T, F, T, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1118 (And.intro z_1072 trivial))

theorem z_1120 : le (tf [T, F, E, F, T, E, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, E, T, F, T, F, T, E, F] [([E, F, T, F, T, E, T, F, T, F, T, E, F], [E, F, T, F, T, F, T, E, T, F, T, E, F]), ([T, F, E, F, E, T, T, F, T, F, T, E, F], [T, F, E, F, E, T, T, F, T, F, T, F, E]), ([T, F, E, F, T, E, T, F, T, F, E, T, F], [T, F, E, F, T, F, T, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1119 (And.intro z_824 (And.intro z_1073 trivial)))

theorem z_1121 : le (tf [T, F, E, T, E, F, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, E, F, T, F, T, F, T, E, F] [([E, F, T, T, E, F, T, F, T, F, T, E, F], [E, F, T, T, F, E, T, F, T, F, T, E, F]), ([T, F, E, E, T, F, T, F, T, F, T, E, F], [T, F, E, F, T, E, T, F, T, F, T, E, F]), ([T, F, E, T, E, F, T, F, T, F, E, T, F], [T, F, E, T, F, E, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1091 (And.intro z_1120 (And.intro z_818 trivial)))

theorem z_1122 : le (tf [T, F, E, T, T, F, E, F, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, E, F, T, E, T, F, F] [([E, F, T, T, T, F, E, F, T, E, T, F, F], [E, F, T, T, T, F, F, E, T, E, T, F, F]), ([T, F, E, T, E, F, T, F, T, E, T, F, F], [T, F, E, T, E, F, T, F, T, F, T, E, F]), ([T, F, E, T, T, F, E, F, E, T, T, F, F], [T, F, E, T, T, F, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1090 (And.intro z_1121 (And.intro z_451 trivial)))

theorem z_1123 : le (tf [F, E, F, T, E, T, T, F, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, F, F, E, T, F, T] [([F, E, F, E, T, T, T, F, F, E, T, F, T], [F, F, E, E, T, T, T, F, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_794 trivial)

theorem z_1124 : le (tf [F, F, E, E, F, T, T, F, T, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, T, T, F, T, E, T, F, T] [([F, F, E, E, F, T, T, F, E, T, T, F, T], [F, F, E, F, E, T, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1100 trivial)

theorem z_1125 : le (tf [F, E, F, T, F, E, T, F, T, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, T, F, E, T, F, T, E, T, F, T] [([F, E, F, E, F, T, T, F, T, E, T, F, T], [F, F, E, E, F, T, T, F, T, E, T, F, T]), ([F, E, F, T, F, E, T, F, E, T, T, F, T], [F, F, E, T, F, E, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1124 (And.intro z_1106 trivial))

theorem z_1126 : le (tf [F, E, F, T, F, T, E, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, T, F, T, E, E, T, F, T, F, T] [([F, E, F, T, F, E, T, E, T, F, T, F, T], [F, E, F, T, F, E, T, F, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1125 trivial)

theorem z_1127 : le (tf [F, F, E, F, E, E, T, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, E, T, T, T, F, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1128 : le (tf [F, F, E, E, F, T, E, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, T, E, T, T, F, T, F, T] [([F, F, E, E, F, E, T, T, T, F, T, F, T], [F, F, E, F, E, E, T, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1127 trivial)

theorem z_1129 : le (tf [F, E, F, T, F, E, E, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, T, F, E, E, T, T, F, T, F, T] [([F, E, F, E, F, T, E, T, T, F, T, F, T], [F, F, E, E, F, T, E, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1128 trivial)

theorem z_1130 : le (tf [F, T, F, E, E, F, E, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, F, E, T, T, F, T, F, T] [([F, E, F, T, E, F, E, T, T, F, T, F, T], [F, E, F, T, F, E, E, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1129 trivial)

theorem z_1131 : le (tf [F, T, F, E, E, T, F, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, T, F, E, T, F, T, F, T] [([F, E, F, T, E, T, F, E, T, F, T, F, T], [F, E, F, T, F, T, E, E, T, F, T, F, T]), ([F, T, F, E, E, E, F, T, T, F, T, F, T], [F, T, F, E, E, F, E, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1126 (And.intro z_1130 trivial))

theorem z_1132 : le (tf [F, T, F, E, E, T, T, F, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, T, T, F, E, F, T, F, T] [([F, E, F, T, E, T, T, F, E, F, T, F, T], [F, E, F, T, E, T, T, F, F, E, T, F, T]), ([F, T, F, E, E, T, E, F, T, F, T, F, T], [F, T, F, E, E, T, F, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1123 (And.intro z_1131 trivial))

theorem z_1133 : le (tf [F, T, E, F, E, T, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, F, E, T, T, F, T, F, E, F, T] [([F, E, T, F, E, T, T, F, T, F, E, F, T], [F, E, T, F, E, T, T, F, T, F, F, E, T]), ([F, T, E, F, E, T, T, F, E, F, T, F, T], [F, T, F, E, E, T, T, F, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_798 (And.intro z_1132 trivial))

theorem z_1134 : le (tf [F, T, E, E, F, T, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, F, T, F, T, F, E] [([F, E, T, E, F, T, T, F, T, F, T, F, E], [F, E, T, F, E, T, T, F, T, F, T, F, E]), ([F, T, E, E, F, T, T, F, T, F, E, F, T], [F, T, E, F, E, T, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_799 (And.intro z_1133 trivial))

theorem z_1135 : le (tf [F, F, E, T, T, F, E, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, E, T, F, E, T, F, T] [([F, F, E, T, E, F, T, T, F, E, T, F, T], [F, F, E, T, F, E, T, T, F, E, T, F, T]), ([F, F, E, T, T, F, E, E, F, T, T, F, T], [F, F, E, T, T, F, E, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1107 (And.intro z_1114 trivial))

theorem z_1136 : le (tf [F, F, E, T, T, F, T, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, T, E, E, F, T, F, T] [([F, F, E, T, T, F, E, T, E, F, T, F, T], [F, F, E, T, T, F, E, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1135 trivial)

theorem z_1137 : le (tf [F, T, F, F, E, F, E, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, F, E, F, E, E, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1138 : le (tf [F, T, F, F, E, E, F, T, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, F, E, E, F, T, E, T, T, F, T] [([F, T, F, F, E, E, F, E, T, T, T, F, T], [F, T, F, F, E, F, E, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1137 trivial)

theorem z_1139 : le (tf [F, T, F, F, E, E, T, E, F, T, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, F, E, E, T, E, F, T, T, F, T] [([F, T, F, F, E, E, E, T, F, T, T, F, T], [F, T, F, F, E, E, F, T, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1138 trivial)

theorem z_1140 : le (tf [F, T, F, E, F, E, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, F, E, T, T, F, E, T, F, T] [([F, E, F, T, F, E, T, T, F, E, T, F, T], [F, F, E, T, F, E, T, T, F, E, T, F, T]), ([F, T, F, E, F, E, T, E, F, T, T, F, T], [F, T, F, F, E, E, T, E, F, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1107 (And.intro z_1139 trivial))

theorem z_1141 : le (tf [F, T, F, F, E, E, E, F, T, T, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, F, E, E, E, F, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1142 : le (tf [F, T, F, E, F, E, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, F, E, T, F, E, T, T, F, T] [([F, E, F, T, F, E, T, F, E, T, T, F, T], [F, F, E, T, F, E, T, F, E, T, T, F, T]), ([F, T, F, E, F, E, E, F, T, T, T, F, T], [F, T, F, F, E, E, E, F, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1106 (And.intro z_1141 trivial))

theorem z_1143 : le (tf [F, T, F, E, T, F, E, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, T, F, E, F, E, T, T, F, T] [([F, E, F, T, T, F, E, F, E, T, T, F, T], [F, F, E, T, T, F, E, F, E, T, T, F, T]), ([F, T, F, E, E, F, T, F, E, T, T, F, T], [F, T, F, E, F, E, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1114 (And.intro z_1142 trivial))

theorem z_1144 : le (tf [F, T, F, E, T, F, E, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, T, F, E, T, F, E, T, F, T] [([F, E, F, T, T, F, E, T, F, E, T, F, T], [F, F, E, T, T, F, E, T, F, E, T, F, T]), ([F, T, F, E, E, F, T, T, F, E, T, F, T], [F, T, F, E, F, E, T, T, F, E, T, F, T]), ([F, T, F, E, T, F, E, E, F, T, T, F, T], [F, T, F, E, T, F, E, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1135 (And.intro z_1140 (And.intro z_1143 trivial)))

theorem z_1145 : le (tf [F, T, F, E, T, F, T, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, T, F, T, E, E, F, T, F, T] [([F, E, F, T, T, F, T, E, E, F, T, F, T], [F, F, E, T, T, F, T, E, E, F, T, F, T]), ([F, T, F, E, T, F, E, T, E, F, T, F, T], [F, T, F, E, T, F, E, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1136 (And.intro z_1144 trivial))

theorem z_1146 : le (tf [F, F, F, E, E, T, T, F, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, F, F, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1147 : le (tf [F, F, F, E, E, T, T, F, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, F, T, F, E, T, T] [([F, F, F, E, E, T, T, F, E, F, T, T, T], [F, F, F, E, E, T, T, F, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1146 trivial)

theorem z_1148 : le (tf [F, F, F, E, F, E, T, F, T, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, T, F, T, E, T, T, T] [([F, F, F, E, F, E, T, F, E, T, T, T, T], [F, F, F, F, E, E, T, F, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1030 trivial)

theorem z_1149 : le (tf [F, F, F, E, F, T, E, E, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, F, T, E, E, T, F, T, T, T] [([F, F, F, E, F, E, T, E, T, F, T, T, T], [F, F, F, E, F, E, T, F, T, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1148 trivial)

theorem z_1150 : le (tf [F, F, F, E, T, E, F, E, T, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, E, F, E, T, F, T, T, T] [([F, F, F, E, E, T, F, E, T, F, T, T, T], [F, F, F, E, F, T, E, E, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1149 trivial)

theorem z_1151 : le (tf [F, F, F, E, T, E, T, F, E, F, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, T, E, T, F, E, F, T, T, T] [([F, F, F, E, E, T, T, F, E, F, T, T, T], [F, F, F, E, E, T, T, F, F, E, T, T, T]), ([F, F, F, E, T, E, E, F, T, F, T, T, T], [F, F, F, E, T, E, F, E, T, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1146 (And.intro z_1150 trivial))

theorem z_1152 : le (tf [F, F, E, F, T, E, T, F, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, T, E, T, F, T, F, E, T, T] [([F, F, E, F, E, T, T, F, T, F, E, T, T], [F, F, F, E, E, T, T, F, T, F, E, T, T]), ([F, F, E, F, T, E, T, F, E, F, T, T, T], [F, F, F, E, T, E, T, F, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1147 (And.intro z_1151 trivial))

theorem z_1153 : le (tf [F, F, E, E, T, F, T, F, T, F, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, F, T, F, T, E, T] [([F, F, E, E, T, F, T, F, T, F, E, T, T], [F, F, E, F, T, E, T, F, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1152 trivial)

theorem z_1154 : le (tf [F, F, E, T, E, F, T, F, T, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, E, F, T, F, T, E, T, F, T] [([F, F, E, E, T, F, T, F, T, E, T, F, T], [F, F, E, E, T, F, T, F, T, F, T, E, T]), ([F, F, E, T, E, F, T, F, E, T, T, F, T], [F, F, E, T, F, E, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1153 (And.intro z_1106 trivial))

theorem z_1155 : le (tf [F, F, E, T, T, F, E, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, E, E, T, F, T, F, T] [([F, F, E, T, E, F, T, E, T, F, T, F, T], [F, F, E, T, E, F, T, F, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1154 trivial)

theorem z_1156 : le (tf [F, T, F, F, E, E, E, T, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, F, E, E, E, T, T, F, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1157 : le (tf [F, T, F, E, F, E, T, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, F, E, T, E, T, F, T, F, T] [([F, E, F, T, F, E, T, E, T, F, T, F, T], [F, E, F, T, F, E, T, F, T, E, T, F, T]), ([F, T, F, E, F, E, E, T, T, F, T, F, T], [F, T, F, F, E, E, E, T, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1125 (And.intro z_1156 trivial))

theorem z_1158 : le (tf [F, T, F, E, T, F, E, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, E, T, F, E, E, T, F, T, F, T] [([F, E, F, T, T, F, E, E, T, F, T, F, T], [F, F, E, T, T, F, E, E, T, F, T, F, T]), ([F, T, F, E, E, F, T, E, T, F, T, F, T], [F, T, F, E, F, E, T, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1155 (And.intro z_1157 trivial))

theorem z_1159 : le (tf [F, T, F, T, E, E, F, E, T, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, T, E, E, F, E, T, F, T, F, T] [([F, T, F, E, T, E, F, E, T, F, T, F, T], [F, T, F, E, T, F, E, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1158 trivial)

theorem z_1160 : le (tf [F, T, F, T, E, E, T, F, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, F, T, E, E, T, F, E, F, T, F, T] [([F, T, F, E, T, E, T, F, E, F, T, F, T], [F, T, F, E, T, F, T, E, E, F, T, F, T]), ([F, T, F, T, E, E, E, F, T, F, T, F, T], [F, T, F, T, E, E, F, E, T, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1145 (And.intro z_1159 trivial))

theorem z_1161 : le (tf [F, T, E, T, F, E, T, F, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, F, E, T, F, T, F, E, F, T] [([F, E, T, T, F, E, T, F, T, F, E, F, T], [F, E, T, T, F, E, T, F, T, F, F, E, T]), ([F, T, E, E, F, T, T, F, T, F, E, F, T], [F, T, E, F, E, T, T, F, T, F, E, F, T]), ([F, T, E, T, F, E, T, F, E, F, T, F, T], [F, T, F, T, E, E, T, F, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_800 (And.intro z_1133 (And.intro z_1160 trivial)))

theorem z_1162 : le (tf [E, T, F, T, F, E, T, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, F, T, F, T, F, E] [([E, T, F, E, F, T, T, F, T, F, T, F, E], [F, T, E, E, F, T, T, F, T, F, T, F, E]), ([E, T, F, T, F, E, T, F, T, F, E, F, T], [F, T, E, T, F, E, T, F, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1134 (And.intro z_1161 trivial))

theorem z_1163 : le (tf [T, F, E, E, F, T, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, F, T, F, T, E, F] [([E, F, T, E, F, T, T, F, T, F, T, E, F], [E, F, T, F, E, T, T, F, T, F, T, E, F]), ([T, F, E, E, F, T, T, F, T, F, E, T, F], [T, F, E, F, E, T, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_335 (And.intro z_810 trivial))

theorem z_1164 : le (tf [T, E, F, T, F, E, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, F, E, T, F, T, F, T, E, F] [([E, T, F, T, F, E, T, F, T, F, T, E, F], [E, T, F, T, F, E, T, F, T, F, T, F, E]), ([T, E, F, E, F, T, T, F, T, F, T, E, F], [T, F, E, E, F, T, T, F, T, F, T, E, F]), ([T, E, F, T, F, E, T, F, T, F, E, T, F], [T, F, E, T, F, E, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1162 (And.intro z_1163 (And.intro z_818 trivial)))

theorem z_1165 : le (tf [T, T, F, E, F, E, T, F, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, F, T, E, T, F, F] [([T, E, F, T, F, E, T, F, T, E, T, F, F], [T, E, F, T, F, E, T, F, T, F, T, E, F]), ([T, T, F, E, F, E, T, F, E, T, T, F, F], [T, T, F, F, E, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1164 (And.intro z_512 trivial))

theorem z_1166 : le (tf [T, T, F, F, F, E, E, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, E, T, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1167 : le (tf [T, T, F, F, E, F, E, T, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, E, T, T, F, F] [([T, T, F, F, E, F, E, E, T, T, T, F, F], [T, T, F, F, F, E, E, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1166 trivial)

theorem z_1168 : le (tf [T, T, F, F, E, T, F, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, E, T, T, F, F] [([T, T, F, F, E, E, F, T, E, T, T, F, F], [T, T, F, F, E, F, E, T, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1167 trivial)

theorem z_1169 : le (tf [T, T, F, F, T, E, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, F, E, T, T, F, F] [([T, T, F, F, E, T, E, F, E, T, T, F, F], [T, T, F, F, E, T, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1168 trivial)

theorem z_1170 : le (tf [T, T, F, E, T, F, E, F, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, F, E, F, T, E, T, F, F] [([T, E, F, T, T, F, E, F, T, E, T, F, F], [T, F, E, T, T, F, E, F, T, E, T, F, F]), ([T, T, F, E, E, F, T, F, T, E, T, F, F], [T, T, F, E, F, E, T, F, T, E, T, F, F]), ([T, T, F, E, T, F, E, F, E, T, T, F, F], [T, T, F, F, T, E, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1122 (And.intro z_1165 (And.intro z_1169 trivial)))

theorem z_1171 : le (tf [T, T, E, F, T, F, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, F, T, F, E, E, T, F, F] [([T, E, T, F, T, F, T, F, E, E, T, F, F], [T, F, T, E, T, F, T, F, E, E, T, F, F]), ([T, T, E, F, T, F, E, F, T, E, T, F, F], [T, T, F, E, T, F, E, F, T, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1078 (And.intro z_1170 trivial))

theorem z_1172 : le (tf [T, T, E, F, T, F, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, F, T, E, F, T, E, F, F] [([T, E, T, F, T, F, T, E, F, T, E, F, F], [T, F, T, E, T, F, T, E, F, T, E, F, F]), ([T, T, E, F, T, F, E, T, F, T, E, F, F], [T, T, E, F, T, F, E, T, F, T, F, E, F]), ([T, T, E, F, T, F, T, E, F, E, T, F, F], [T, T, E, F, T, F, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1079 (And.intro z_1089 (And.intro z_1171 trivial)))

theorem z_1173 : le (tf [T, T, T, F, E, F, E, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, E, T, F, T, E, F, F] [([T, T, E, F, T, F, E, T, F, T, E, F, F], [T, T, E, F, T, F, E, T, F, T, F, E, F]), ([T, T, T, F, E, F, E, T, F, E, T, F, F], [T, T, T, F, F, E, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1089 (And.intro z_538 trivial))

theorem z_1174 : le (tf [T, T, T, F, E, F, T, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, F, T, E, E, T, F, F, F] [([T, T, E, F, T, F, T, E, E, T, F, F, F], [T, T, E, F, T, F, T, E, F, T, E, F, F]), ([T, T, T, F, E, F, E, T, E, T, F, F, F], [T, T, T, F, E, F, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1172 (And.intro z_1173 trivial))

theorem z_1175 : le (tf [T, T, T, F, F, E, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, F, T, E, E, F] [([T, T, T, F, F, E, F, T, F, E, T, E, F], [T, T, T, F, F, F, E, T, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_54 trivial)

theorem z_1176 : le (tf [T, T, T, F, F, F, E, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, E, T, E, E, F, T, F] [([T, T, T, F, F, F, E, E, T, E, F, T, F], [T, T, T, F, F, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 trivial)

theorem z_1177 : le (tf [T, T, T, F, F, E, F, T, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, F, T, E, T, F, E, F] [([T, T, T, F, F, E, F, E, T, T, F, E, F], [T, T, T, F, F, F, E, E, T, T, F, E, F]), ([T, T, T, F, F, E, F, T, E, E, F, T, F], [T, T, T, F, F, F, E, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_209 (And.intro z_1176 trivial))

theorem z_1178 : le (tf [T, T, T, F, F, T, F, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, T, F, E, E, E, F, T, F] [([T, T, T, F, F, E, F, T, E, E, F, T, F], [T, T, T, F, F, F, E, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1176 trivial)

theorem z_1179 : le (tf [T, F, E, T, T, T, F, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, F, F, F, T, E, E, F] [([E, F, T, T, T, T, F, F, F, T, E, E, F], [F, E, T, T, T, T, F, F, F, T, E, E, F]), ([T, F, E, T, T, T, F, F, F, E, T, E, F], [T, F, E, T, T, T, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_255 (And.intro z_454 trivial))

theorem z_1180 : le (tf [T, T, F, E, T, T, F, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, F, F, F, T, E, E, F] [([T, E, F, T, T, T, F, F, F, T, E, E, F], [T, F, E, T, T, T, F, F, F, T, E, E, F]), ([T, T, F, E, T, T, F, F, F, E, T, E, F], [T, T, F, E, T, T, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1179 (And.intro z_517 trivial))

theorem z_1181 : le (tf [E, F, T, T, T, T, F, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, F, T, E, E, F] [([E, F, T, T, T, T, F, F, F, E, T, E, F], [E, F, T, T, T, T, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_455 trivial)

theorem z_1182 : le (tf [T, E, F, T, T, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, F, E, T, F, E, F] [([E, T, F, T, T, T, F, F, E, T, F, E, F], [F, T, E, T, T, T, F, F, E, T, F, E, F]), ([T, E, F, T, T, T, F, F, E, E, F, T, F], [T, F, E, T, T, T, F, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_258 (And.intro z_909 trivial))

theorem z_1183 : le (tf [T, E, F, T, T, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, F, E, T, E, F, F] [([E, T, F, T, T, T, F, F, E, T, E, F, F], [F, T, E, T, T, T, F, F, E, T, E, F, F]), ([T, E, F, T, T, T, F, F, E, E, T, F, F], [T, F, E, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_926 (And.intro z_978 trivial))

theorem z_1184 : le (tf [F, T, E, T, T, T, F, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, F, F, E, E, T, F, F] [([F, E, T, T, T, T, F, F, E, E, T, F, F], [F, E, T, T, T, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_237 trivial)

theorem z_1185 : le (tf [E, T, F, T, T, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, F, E, T, E, F, F] [([E, T, F, T, T, T, F, F, E, E, T, F, F], [F, T, E, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1184 trivial)

theorem z_1186 : le (tf [F, T, E, T, T, F, F, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, E, F, T, T, F] [([F, E, T, T, T, F, F, E, E, F, T, T, F], [F, E, T, T, T, F, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_444 trivial)

theorem z_1187 : le (tf [E, T, F, T, T, F, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, T, F, E, T, F] [([E, T, F, T, T, F, F, E, E, F, T, T, F], [F, T, E, T, T, F, F, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1186 trivial)

theorem z_1188 : le (tf [E, T, F, T, T, F, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, T, T, F, E, F] [([E, T, F, T, T, F, F, E, T, E, F, T, F], [E, T, F, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1187 trivial)

theorem z_1189 : le (tf [F, E, T, T, T, F, F, F, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, F, E, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1190 : le (tf [F, T, E, T, T, F, F, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, F, E, T, F, T] [([F, E, T, T, T, F, F, E, F, E, T, F, T], [F, E, T, T, T, F, F, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1189 trivial)

theorem z_1191 : le (tf [F, T, E, T, T, F, F, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, T, F, E, F, T] [([F, E, T, T, T, F, F, E, T, F, E, F, T], [F, E, T, T, T, F, F, F, T, E, E, F, T]), ([F, T, E, T, T, F, F, E, E, F, T, F, T], [F, T, E, T, T, F, F, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_436 (And.intro z_1190 trivial))

theorem z_1192 : le (tf [E, T, F, T, T, F, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, T, F, T, F, E] [([E, T, F, T, T, F, F, E, T, F, E, F, T], [F, T, E, T, T, F, F, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1191 trivial)

theorem z_1193 : le (tf [F, T, E, T, T, F, F, F, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, F, E, E, F, T, T] [([F, E, T, T, T, F, F, F, E, E, F, T, T], [F, E, T, T, T, F, F, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 trivial)

theorem z_1194 : le (tf [F, T, E, T, T, F, F, E, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, F, T, F, E, T] [([F, E, T, T, T, F, F, E, F, T, F, E, T], [F, E, T, T, T, F, F, F, E, T, F, E, T]), ([F, T, E, T, T, F, F, E, F, E, F, T, T], [F, T, E, T, T, F, F, F, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_1193 trivial))

theorem z_1195 : le (tf [E, T, F, T, T, F, F, E, F, T, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, F, T, F, T, E] [([E, T, F, T, T, F, F, E, F, T, F, E, T], [F, T, E, T, T, F, F, E, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1194 trivial)

theorem z_1196 : le (tf [E, T, F, T, T, F, F, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, T, F, E, E, T, F] [([E, T, F, T, T, F, F, E, F, T, E, T, F], [E, T, F, T, T, F, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1195 trivial)

theorem z_1197 : le (tf [E, T, F, T, T, F, F, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, T, E, F, T, E, F] [([E, T, F, T, T, F, F, E, T, F, T, E, F], [E, T, F, T, T, F, F, E, T, F, T, F, E]), ([E, T, F, T, T, F, F, T, E, F, E, T, F], [E, T, F, T, T, F, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1192 (And.intro z_1196 trivial))

theorem z_1198 : le (tf [E, T, F, T, T, F, F, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, T, E, T, E, F, F] [([E, T, F, T, T, F, F, E, T, T, E, F, F], [E, T, F, T, T, F, F, E, T, T, F, E, F]), ([E, T, F, T, T, F, F, T, E, E, T, F, F], [E, T, F, T, T, F, F, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1188 (And.intro z_1197 trivial))

theorem z_1199 : le (tf [F, F, E, E, F, E, T, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, T, T, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1200 : le (tf [F, F, E, E, T, F, E, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, E, T, T, T, F, T, F] [([F, F, E, E, E, F, T, T, T, T, F, T, F], [F, F, E, E, F, E, T, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1199 trivial)

theorem z_1201 : le (tf [F, F, E, E, T, T, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, F, E, T, T, F, T, F] [([F, F, E, E, T, E, F, T, T, T, F, T, F], [F, F, E, E, T, F, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1200 trivial)

theorem z_1202 : le (tf [F, F, E, E, T, T, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, F, E, T, F, T, F] [([F, F, E, E, T, T, E, F, T, T, F, T, F], [F, F, E, E, T, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1201 trivial)

theorem z_1203 : le (tf [F, F, E, T, E, E, F, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, E, E, F, T, T, T, F, T, F] [([F, F, E, E, T, E, F, T, T, T, F, T, F], [F, F, E, E, T, F, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1200 trivial)

theorem z_1204 : le (tf [F, E, F, T, E, T, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, F, E, T, T, F, T, F] [([F, E, F, E, T, T, F, E, T, T, F, T, F], [F, F, E, E, T, T, F, E, T, T, F, T, F]), ([F, E, F, T, E, E, F, T, T, T, F, T, F], [F, F, E, T, E, E, F, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1201 (And.intro z_1203 trivial))

theorem z_1205 : le (tf [F, E, F, T, E, T, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, F, E, T, F, T, F] [([F, E, F, E, T, T, T, F, E, T, F, T, F], [F, F, E, E, T, T, T, F, E, T, F, T, F]), ([F, E, F, T, E, T, E, F, T, T, F, T, F], [F, E, F, T, E, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1202 (And.intro z_1204 trivial))

theorem z_1206 : le (tf [F, E, F, T, E, T, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, F, E, F, T, F] [([F, E, F, E, T, T, T, T, F, E, F, T, F], [F, E, F, E, T, T, T, T, F, F, E, T, F]), ([F, E, F, T, E, T, T, E, F, T, F, T, F], [F, E, F, T, E, T, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_368 (And.intro z_1205 trivial))

theorem z_1207 : le (tf [F, E, E, T, F, T, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, F, T, T, T, F, T, F, E, F] [([F, E, E, T, F, T, T, T, F, E, F, T, F], [F, E, F, T, E, T, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1206 trivial)

theorem z_1208 : le (tf [F, E, T, E, F, T, T, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, F, T, E, F, F] [([F, E, E, T, F, T, T, T, F, T, E, F, F], [F, E, E, T, F, T, T, T, F, T, F, E, F]), ([F, E, T, E, F, T, T, T, F, E, T, F, F], [F, E, T, E, F, T, T, T, F, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1207 (And.intro z_370 trivial))

theorem z_1209 : le (tf [E, F, T, T, F, E, T, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, F, T, E, F, F] [([E, F, T, E, F, T, T, T, F, T, E, F, F], [F, E, T, E, F, T, T, T, F, T, E, F, F]), ([E, F, T, T, F, E, T, T, F, E, T, F, F], [F, E, T, T, F, E, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1208 (And.intro z_600 trivial))

theorem z_1210 : le (tf [E, F, T, F, T, E, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, E, T, T, F, F, E, T, F] [([E, F, T, F, E, T, T, T, F, F, E, T, F], [F, E, T, F, E, T, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_369 trivial)

theorem z_1211 : le (tf [E, F, T, F, T, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, E, T, T, F, T, F, E, F] [([E, F, T, F, E, T, T, T, F, T, F, E, F], [F, E, T, F, E, T, T, T, F, T, F, E, F]), ([E, F, T, F, T, E, T, T, F, E, F, T, F], [E, F, T, F, T, E, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_899 (And.intro z_1210 trivial))

theorem z_1212 : le (tf [T, F, F, E, E, F, E, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, F, E, T, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1213 : le (tf [T, F, F, E, E, T, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, F, E, T, T, F, T, F] [([T, F, F, E, E, E, F, T, T, T, F, T, F], [T, F, F, E, E, F, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1212 trivial)

theorem z_1214 : le (tf [T, F, F, E, E, T, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, T, F, E, T, F, T, F] [([T, F, F, E, E, T, E, F, T, T, F, T, F], [T, F, F, E, E, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1213 trivial)

theorem z_1215 : le (tf [T, F, F, F, E, E, F, E, T, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, F, E, T, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1216 : le (tf [T, F, F, F, E, E, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, F, E, T, T, T, F] [([T, F, F, F, E, E, E, F, T, T, T, T, F], [T, F, F, F, E, E, F, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1215 trivial)

theorem z_1217 : le (tf [T, F, F, F, E, E, T, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, T, F, E, T, T, F] [([T, F, F, F, E, E, T, E, F, T, T, T, F], [T, F, F, F, E, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1216 trivial)

theorem z_1218 : le (tf [T, F, F, F, E, T, E, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, E, E, F, T, T, T, F] [([T, F, F, F, E, E, T, E, F, T, T, T, F], [T, F, F, F, E, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1216 trivial)

theorem z_1219 : le (tf [T, F, F, E, F, T, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, E, T, F, E, T, T, F] [([T, F, F, E, F, E, T, T, F, E, T, T, F], [T, F, F, F, E, E, T, T, F, E, T, T, F]), ([T, F, F, E, F, T, E, E, F, T, T, T, F], [T, F, F, F, E, T, E, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1217 (And.intro z_1218 trivial))

theorem z_1220 : le (tf [T, F, F, E, E, T, F, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, F, T, F, T, E, T, F] [([T, F, F, E, E, T, F, T, F, E, T, T, F], [T, F, F, E, F, T, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1219 trivial)

theorem z_1221 : le (tf [T, F, F, F, E, E, E, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, E, T, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1222 : le (tf [T, F, F, E, F, E, T, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, E, T, T, F, T, F] [([T, F, F, E, F, E, E, T, T, T, F, T, F], [T, F, F, F, E, E, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1221 trivial)

theorem z_1223 : le (tf [T, F, F, E, T, F, E, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, E, T, T, F, T, F] [([T, F, F, E, E, F, T, E, T, T, F, T, F], [T, F, F, E, F, E, T, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1222 trivial)

theorem z_1224 : le (tf [T, F, F, E, T, E, F, T, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, E, F, T, E, T, F, T, F] [([T, F, F, E, E, T, F, T, E, T, F, T, F], [T, F, F, E, E, T, F, T, F, T, E, T, F]), ([T, F, F, E, T, E, F, E, T, T, F, T, F], [T, F, F, E, T, F, E, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1220 (And.intro z_1223 trivial))

theorem z_1225 : le (tf [T, F, F, E, T, E, T, E, F, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, E, T, E, F, T, F, T, F] [([T, F, F, E, E, T, T, E, F, T, F, T, F], [T, F, F, E, E, T, T, F, E, T, F, T, F]), ([T, F, F, E, T, E, E, T, F, T, F, T, F], [T, F, F, E, T, E, F, T, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1214 (And.intro z_1224 trivial))

theorem z_1226 : le (tf [T, F, E, F, T, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, E, T, T, F, E, F, T, F] [([E, F, T, F, T, E, T, T, F, E, F, T, F], [E, F, T, F, T, E, T, T, F, F, E, T, F]), ([T, F, E, F, E, T, T, T, F, E, F, T, F], [T, F, E, F, E, T, T, T, F, F, E, T, F]), ([T, F, E, F, T, E, T, E, F, T, F, T, F], [T, F, F, E, T, E, T, E, F, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1210 (And.intro z_373 (And.intro z_1225 trivial)))

theorem z_1227 : le (tf [T, F, E, E, T, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, T, F, T, T, F, T, F, E, F] [([E, F, T, E, T, F, T, T, F, T, F, E, F], [E, F, T, F, T, E, T, T, F, T, F, E, F]), ([T, F, E, E, T, F, T, T, F, E, F, T, F], [T, F, E, F, T, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1211 (And.intro z_1226 trivial))

theorem z_1228 : le (tf [T, F, E, T, E, F, T, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, E, F, T, T, F, T, E, F, F] [([E, F, T, T, E, F, T, T, F, T, E, F, F], [E, F, T, T, F, E, T, T, F, T, E, F, F]), ([T, F, E, E, T, F, T, T, F, T, E, F, F], [T, F, E, E, T, F, T, T, F, T, F, E, F]), ([T, F, E, T, E, F, T, T, F, E, T, F, F], [T, F, E, T, F, E, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1209 (And.intro z_1227 (And.intro z_609 trivial)))

theorem z_1229 : le (tf [T, E, F, T, T, F, E, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, F, E, T, F, T, E, F, F] [([E, T, F, T, T, F, E, T, F, T, E, F, F], [E, T, F, T, T, F, F, T, E, T, E, F, F]), ([T, E, F, T, E, F, T, T, F, T, E, F, F], [T, F, E, T, E, F, T, T, F, T, E, F, F]), ([T, E, F, T, T, F, E, T, F, E, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1198 (And.intro z_1228 (And.intro z_611 trivial)))

theorem z_1230 : le (tf [T, E, F, T, T, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, F, E, F, T, E, F, F] [([E, T, F, T, T, T, F, E, F, T, E, F, F], [E, T, F, T, T, T, F, F, E, T, E, F, F]), ([T, E, F, T, T, E, F, T, F, T, E, F, F], [T, E, F, T, T, F, E, T, F, T, E, F, F]), ([T, E, F, T, T, T, F, E, F, E, T, F, F], [T, F, E, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1185 (And.intro z_1229 (And.intro z_757 trivial)))

theorem z_1231 : le (tf [T, T, F, F, F, E, T, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, T, F, E, T, F, E] [([T, T, F, F, F, E, T, E, F, T, T, F, E], [T, T, F, F, F, E, T, F, E, T, T, F, E]), ([T, T, F, F, F, E, T, T, F, E, E, F, T], [T, T, F, F, F, E, T, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_479 (And.intro z_581 trivial))

theorem z_1232 : le (tf [T, T, F, F, F, E, T, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, T, F, T, E, E, F] [([T, T, F, F, F, E, T, T, F, E, T, E, F], [T, T, F, F, F, E, T, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1231 trivial)

theorem z_1233 : le (tf [T, T, F, F, T, F, E, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, F, E, T, T, F, E] [([T, T, F, F, E, F, T, F, E, T, T, F, E], [T, T, F, F, F, E, T, F, E, T, T, F, E]), ([T, T, F, F, T, F, E, F, E, T, E, F, T], [T, T, F, F, T, F, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_479 (And.intro z_586 trivial))

theorem z_1234 : le (tf [T, T, F, F, T, F, F, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, F, E, E, E, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1235 : le (tf [T, T, F, F, T, F, E, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, F, E, T, F, E, T] [([T, T, F, F, E, F, T, F, E, T, F, E, T], [T, T, F, F, F, E, T, F, E, T, F, E, T]), ([T, T, F, F, T, F, E, F, E, E, F, T, T], [T, T, F, F, T, F, F, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 (And.intro z_1234 trivial))

theorem z_1236 : le (tf [T, T, F, F, T, F, E, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, T, F, E, F, E, T] [([T, T, F, F, E, F, T, T, F, E, F, E, T], [T, T, F, F, F, E, T, T, F, E, F, E, T]), ([T, T, F, F, T, F, E, E, F, T, F, E, T], [T, T, F, F, T, F, E, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_581 (And.intro z_1235 trivial))

theorem z_1237 : le (tf [T, T, F, F, T, F, E, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, T, F, E, T, F, E] [([T, T, F, F, E, F, T, T, F, E, T, F, E], [T, T, F, F, F, E, T, T, F, E, T, F, E]), ([T, T, F, F, T, F, E, E, F, T, T, F, E], [T, T, F, F, T, F, E, F, E, T, T, F, E]), ([T, T, F, F, T, F, E, T, F, E, E, F, T], [T, T, F, F, T, F, E, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1231 (And.intro z_1233 (And.intro z_1236 trivial)))

theorem z_1238 : le (tf [T, T, F, F, T, F, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, T, F, T, E, E, F] [([T, T, F, F, E, F, T, T, F, T, E, E, F], [T, T, F, F, F, E, T, T, F, T, E, E, F]), ([T, T, F, F, T, F, E, T, F, E, T, E, F], [T, T, F, F, T, F, E, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1232 (And.intro z_1237 trivial))

theorem z_1239 : le (tf [T, T, F, F, F, E, T, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, T, T, F, E, E, F, T] [([T, T, F, F, F, E, T, E, F, T, E, F, T], [T, T, F, F, F, E, T, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_492 trivial)

theorem z_1240 : le (tf [T, T, F, F, E, F, T, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, F, E, T, F, E] [([T, T, F, F, E, F, T, E, F, T, T, F, E], [T, T, F, F, E, F, T, F, E, T, T, F, E]), ([T, T, F, F, E, F, T, T, F, E, E, F, T], [T, T, F, F, F, E, T, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_493 (And.intro z_1239 trivial))

theorem z_1241 : le (tf [T, T, F, F, E, F, T, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, F, T, E, E, F] [([T, T, F, F, E, F, T, T, F, E, T, E, F], [T, T, F, F, E, F, T, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1240 trivial)

theorem z_1242 : le (tf [T, T, F, F, T, F, F, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, F, E, E, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1243 : le (tf [T, T, F, F, T, F, E, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, F, E, T, E, F, T] [([T, T, F, F, E, F, T, F, E, T, E, F, T], [T, T, F, F, F, E, T, F, E, T, E, F, T]), ([T, T, F, F, T, F, E, F, E, E, T, F, T], [T, T, F, F, T, F, F, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_492 (And.intro z_1242 trivial))

theorem z_1244 : le (tf [T, T, F, F, T, F, E, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, F, T, T, F, E] [([T, T, F, F, E, F, T, E, F, T, T, F, E], [T, T, F, F, E, F, T, F, E, T, T, F, E]), ([T, T, F, F, T, F, E, E, F, T, E, F, T], [T, T, F, F, T, F, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_493 (And.intro z_1243 trivial))

theorem z_1245 : le (tf [T, T, F, F, T, F, E, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, T, F, E, E, F, T] [([T, T, F, F, E, F, T, T, F, E, E, F, T], [T, T, F, F, F, E, T, T, F, E, E, F, T]), ([T, T, F, F, T, F, E, E, F, T, E, F, T], [T, T, F, F, T, F, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1239 (And.intro z_1243 trivial))

theorem z_1246 : le (tf [T, T, F, F, F, E, E, T, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1247 : le (tf [T, T, F, F, E, F, T, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, T, T, F, F, E] [([T, T, F, F, E, F, E, T, T, T, F, F, E], [T, T, F, F, F, E, E, T, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1246 trivial)

theorem z_1248 : le (tf [T, T, F, F, E, F, T, T, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, E, F, E, T, F] [([T, T, F, F, E, F, T, E, T, F, E, T, F], [T, T, F, F, E, F, T, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_499 trivial)

theorem z_1249 : le (tf [T, T, F, F, E, F, T, T, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, E, T, F, E, F] [([T, T, F, F, E, F, T, E, T, T, F, E, F], [T, T, F, F, E, F, T, E, T, T, F, F, E]), ([T, T, F, F, E, F, T, T, E, E, F, T, F], [T, T, F, F, E, F, T, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1247 (And.intro z_1248 trivial))

theorem z_1250 : le (tf [T, T, F, F, T, F, E, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, T, T, F, E, F] [([T, T, F, F, E, F, T, E, T, T, F, E, F], [T, T, F, F, E, F, T, E, T, T, F, F, E]), ([T, T, F, F, T, F, E, E, T, E, F, T, F], [T, T, F, F, T, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1247 (And.intro z_578 trivial))

theorem z_1251 : le (tf [T, T, F, F, T, F, E, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, T, E, E, F, T, F] [([T, T, F, F, E, F, T, T, E, E, F, T, F], [T, T, F, F, E, F, T, T, E, F, E, T, F]), ([T, T, F, F, T, F, E, E, T, E, F, T, F], [T, T, F, F, T, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1248 (And.intro z_578 trivial))

theorem z_1252 : le (tf [T, T, F, F, F, E, E, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, T, T, F, E, F] [([T, T, F, F, F, E, E, T, T, E, F, T, F], [T, T, F, F, F, E, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_502 trivial)

theorem z_1253 : le (tf [T, T, F, F, E, F, T, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, T, T, F, E, F] [([T, T, F, F, E, F, E, T, T, T, F, E, F], [T, T, F, F, F, E, E, T, T, T, F, E, F]), ([T, T, F, F, E, F, T, E, T, E, F, T, F], [T, T, F, F, E, F, T, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1252 (And.intro z_505 trivial))

theorem z_1254 : le (tf [T, T, F, F, F, E, E, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1255 : le (tf [T, T, F, F, F, E, E, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, T, F, T, F, E] [([T, T, F, F, F, E, E, T, T, F, E, F, T], [T, T, F, F, F, E, E, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1254 trivial)

theorem z_1256 : le (tf [T, T, F, F, E, F, T, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, T, F, T, F, E] [([T, T, F, F, E, F, E, T, T, F, T, F, E], [T, T, F, F, F, E, E, T, T, F, T, F, E]), ([T, T, F, F, E, F, T, E, T, F, E, F, T], [T, T, F, F, E, F, T, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1255 (And.intro z_494 trivial))

theorem z_1257 : le (tf [T, T, F, F, E, F, T, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, F, E, E, T, F] [([T, T, F, F, E, F, T, E, F, T, E, T, F], [T, T, F, F, F, E, T, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_845 trivial)

theorem z_1258 : le (tf [T, T, F, F, E, F, T, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, E, F, T, E, F] [([T, T, F, F, E, F, T, E, T, F, T, E, F], [T, T, F, F, E, F, T, E, T, F, T, F, E]), ([T, T, F, F, E, F, T, T, E, F, E, T, F], [T, T, F, F, E, F, T, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1256 (And.intro z_1257 trivial))

theorem z_1259 : le (tf [T, T, F, F, E, F, T, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, E, T, E, F, F] [([T, T, F, F, E, F, T, E, T, T, E, F, F], [T, T, F, F, E, F, T, E, T, T, F, E, F]), ([T, T, F, F, E, F, T, T, E, E, T, F, F], [T, T, F, F, E, F, T, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1253 (And.intro z_1258 trivial))

theorem z_1260 : le (tf [T, T, F, F, T, F, E, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, F, E, E, T, T, F] [([T, T, F, F, E, F, T, F, E, E, T, T, F], [T, T, F, F, F, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_844 trivial)

theorem z_1261 : le (tf [T, T, F, F, T, F, E, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, F, T, E, T, F] [([T, T, F, F, E, F, T, E, F, T, E, T, F], [T, T, F, F, F, E, T, E, F, T, E, T, F]), ([T, T, F, F, T, F, E, E, F, E, T, T, F], [T, T, F, F, T, F, E, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_845 (And.intro z_1260 trivial))

theorem z_1262 : le (tf [T, T, F, F, T, F, E, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, T, E, F, T, F] [([T, T, F, F, E, F, T, E, T, E, F, T, F], [T, T, F, F, E, F, T, E, T, F, E, T, F]), ([T, T, F, F, T, F, E, E, E, T, F, T, F], [T, T, F, F, T, F, E, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_505 (And.intro z_1261 trivial))

theorem z_1263 : le (tf [T, T, F, F, T, F, E, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, F, T, T, E, F] [([T, T, F, F, E, F, T, E, F, T, T, E, F], [T, T, F, F, E, F, T, F, E, T, T, E, F]), ([T, T, F, F, T, F, E, E, F, T, E, T, F], [T, T, F, F, T, F, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_498 (And.intro z_590 trivial))

theorem z_1264 : le (tf [T, T, F, F, T, F, E, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, F, E, T, F, T] [([T, T, F, F, E, F, T, E, F, E, T, F, T], [T, T, F, F, F, E, T, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_859 trivial)

theorem z_1265 : le (tf [T, T, F, F, T, F, E, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, T, F, E, F, T] [([T, T, F, F, E, F, T, E, T, F, E, F, T], [T, T, F, F, E, F, T, F, T, E, E, F, T]), ([T, T, F, F, T, F, E, E, E, F, T, F, T], [T, T, F, F, T, F, E, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_494 (And.intro z_1264 trivial))

theorem z_1266 : le (tf [T, T, F, F, F, T, E, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, F, T, T, F, E] [([T, T, F, F, F, E, T, E, F, T, T, F, E], [T, T, F, F, F, E, T, F, E, T, T, F, E]), ([T, T, F, F, F, T, E, E, F, T, E, F, T], [T, T, F, F, F, T, E, E, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_479 (And.intro z_730 trivial))

theorem z_1267 : le (tf [T, T, F, F, F, T, E, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, T, F, E, E, F, T] [([T, T, F, F, F, E, T, T, F, E, E, F, T], [T, T, F, F, F, E, T, T, F, E, F, E, T]), ([T, T, F, F, F, T, E, E, F, T, E, F, T], [T, T, F, F, F, T, E, E, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_581 (And.intro z_730 trivial))

theorem z_1268 : le (tf [T, T, F, F, E, T, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, T, F, E, T, F, E] [([T, T, F, F, E, T, F, E, F, T, T, F, E], [T, T, F, F, F, T, E, E, F, T, T, F, E]), ([T, T, F, F, E, T, F, T, F, E, E, F, T], [T, T, F, F, F, T, E, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1266 (And.intro z_1267 trivial))

theorem z_1269 : le (tf [T, T, F, F, E, T, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, T, F, T, E, E, F] [([T, T, F, F, E, T, F, T, F, E, T, E, F], [T, T, F, F, E, T, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1268 trivial)

theorem z_1270 : le (tf [T, T, F, F, F, E, E, T, F, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, E, E, T, F, T, E, F, T] [([T, T, F, F, F, E, E, T, F, E, T, F, T], [T, T, F, F, F, E, F, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_858 trivial)

theorem z_1271 : le (tf [T, T, F, F, E, F, E, T, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, F, T, T, F, E] [([T, T, F, F, E, F, E, T, F, T, E, F, T], [T, T, F, F, F, E, E, T, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1270 trivial)

theorem z_1272 : le (tf [T, T, F, F, F, T, E, F, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, F, E, E, T, F, T] [([T, T, F, F, F, E, T, F, E, E, T, F, T], [T, T, F, F, F, E, T, F, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_491 trivial)

theorem z_1273 : le (tf [T, T, F, F, F, T, E, E, F, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, F, T, E, F, T] [([T, T, F, F, F, E, T, E, F, T, E, F, T], [T, T, F, F, F, E, T, F, E, T, E, F, T]), ([T, T, F, F, F, T, E, E, F, E, T, F, T], [T, T, F, F, F, T, E, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_492 (And.intro z_1272 trivial))

theorem z_1274 : le (tf [T, T, F, F, E, T, F, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, F, T, T, F, E] [([T, T, F, F, E, E, F, T, F, T, T, F, E], [T, T, F, F, E, F, E, T, F, T, T, F, E]), ([T, T, F, F, E, T, F, E, F, T, E, F, T], [T, T, F, F, F, T, E, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1271 (And.intro z_1273 trivial))

theorem z_1275 : le (tf [T, T, F, F, E, T, F, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, T, F, E, E, F, T] [([T, T, F, F, E, T, F, E, F, T, E, F, T], [T, T, F, F, F, T, E, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1273 trivial)

theorem z_1276 : le (tf [T, T, F, F, E, F, E, T, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1277 : le (tf [T, T, F, F, E, T, F, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, T, T, F, F, E] [([T, T, F, F, E, E, F, T, T, T, F, F, E], [T, T, F, F, E, F, E, T, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1276 trivial)

theorem z_1278 : le (tf [T, T, F, F, E, E, F, T, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, T, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1279 : le (tf [T, T, F, F, E, E, F, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, T, T, T, F, E, F] [([T, T, F, F, E, E, F, T, T, E, F, T, F], [T, T, F, F, E, F, E, T, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_837 trivial)

theorem z_1280 : le (tf [T, T, F, F, E, F, E, T, F, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, E, T, F, T, T, E, F] [([T, T, F, F, E, F, E, T, F, T, E, T, F], [T, T, F, F, E, F, E, T, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_728 trivial)

theorem z_1281 : le (tf [T, T, F, F, E, T, F, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, F, T, T, E, F] [([T, T, F, F, E, E, F, T, F, T, T, E, F], [T, T, F, F, E, F, E, T, F, T, T, E, F]), ([T, T, F, F, E, T, F, E, F, T, E, T, F], [T, T, F, F, E, T, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1280 (And.intro z_731 trivial))

theorem z_1282 : le (tf [T, T, F, F, E, E, F, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, T, T, F, T, F, E] [([T, T, F, F, E, E, F, T, T, F, E, F, T], [T, T, F, F, E, F, E, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_857 trivial)

theorem z_1283 : le (tf [T, T, F, F, F, T, E, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, F, T, E, E, F, E, T, T, F] [([T, T, F, F, F, E, T, E, F, E, T, T, F], [T, T, F, F, F, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_844 trivial)

theorem z_1284 : le (tf [T, T, F, F, E, T, F, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, F, E, F, T, E, T, F] [([T, T, F, F, E, E, F, T, F, T, E, T, F], [T, T, F, F, E, F, E, T, F, T, E, T, F]), ([T, T, F, F, E, T, F, E, F, E, T, T, F], [T, T, F, F, F, T, E, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_833 (And.intro z_1283 trivial))

theorem z_1285 : le (tf [T, T, F, F, E, F, T, T, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, T, E, E, T, F, F] [([T, T, F, F, E, F, T, E, T, E, T, F, F], [T, T, F, F, E, F, T, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_735 trivial)

theorem z_1286 : le (tf [T, T, F, F, T, F, E, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, E, E, E, F, T, T, F] [([T, T, F, F, E, F, T, E, E, F, T, T, F], [T, T, F, F, F, E, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_504 trivial)

theorem z_1287 : le (tf [T, T, F, E, E, F, T, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, E, F, T, T, F, T, E, F, F] [([T, E, F, T, E, F, T, T, F, T, E, F, F], [T, F, E, T, E, F, T, T, F, T, E, F, F]), ([T, T, F, E, E, F, T, T, F, E, T, F, F], [T, T, F, E, F, E, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1228 (And.intro z_721 trivial))

theorem z_1288 : le (tf [E, F, T, T, T, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, E, T, F, E, F] [([E, F, T, T, T, T, F, F, E, E, F, T, F], [F, E, T, T, T, T, F, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_903 trivial)

theorem z_1289 : le (tf [E, F, T, T, T, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, F, E, T, E, F, F] [([E, F, T, T, T, T, F, F, E, E, T, F, F], [F, E, T, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_954 trivial)

theorem z_1290 : le (tf [E, F, T, T, T, F, E, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, E, T, F, T, E, F, F] [([E, F, T, T, E, F, T, T, F, T, E, F, F], [E, F, T, T, F, E, T, T, F, T, E, F, F]), ([E, F, T, T, T, F, E, T, F, E, T, F, F], [F, E, T, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1209 (And.intro z_602 trivial))

theorem z_1291 : le (tf [E, F, T, T, T, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, F, E, F, T, E, F, F] [([E, F, T, T, T, E, F, T, F, T, E, F, F], [E, F, T, T, T, F, E, T, F, T, E, F, F]), ([E, F, T, T, T, T, F, E, F, E, T, F, F], [F, E, T, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1290 (And.intro z_753 trivial))

theorem z_1292 : le (tf [F, E, T, T, T, F, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, T, F, T, E, E, F] [([F, E, T, T, T, F, F, T, F, E, T, E, F], [F, E, T, T, T, F, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_405 trivial)

theorem z_1293 : le (tf [T, F, E, T, T, F, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, T, F, T, E, E, F] [([E, F, T, T, T, F, F, T, F, T, E, E, F], [F, E, T, T, T, F, F, T, F, T, E, E, F]), ([T, F, E, T, T, F, F, T, F, E, T, E, F], [T, F, E, T, T, F, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1292 (And.intro z_410 trivial))

theorem z_1294 : le (tf [E, F, T, T, T, F, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, F, T, E, E, F] [([E, F, T, T, T, F, F, T, F, E, T, E, F], [E, F, T, T, T, F, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_416 trivial)

theorem z_1295 : le (tf [E, F, T, T, T, F, F, T, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, E, T, F, E, F] [([E, F, T, T, T, F, F, E, T, T, F, E, F], [F, E, T, T, T, F, F, E, T, T, F, E, F]), ([E, F, T, T, T, F, F, T, E, E, F, T, F], [F, E, T, T, T, F, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_549 (And.intro z_901 trivial))

theorem z_1296 : le (tf [E, F, T, T, T, F, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, E, T, T, F, E, F] [([E, F, T, T, T, F, F, E, T, E, F, T, F], [F, E, T, T, T, F, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_792 trivial)

theorem z_1297 : le (tf [E, F, T, T, T, F, F, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, T, E, T, E, F, F] [([E, F, T, T, T, F, F, E, T, T, E, F, F], [E, F, T, T, T, F, F, E, T, T, F, E, F]), ([E, F, T, T, T, F, F, T, E, E, T, F, F], [E, F, T, T, T, F, F, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1296 (And.intro z_435 trivial))

theorem z_1298 : le (tf [F, E, T, T, T, F, F, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, F, E, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1299 : le (tf [T, F, E, T, T, F, F, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, F, E, T, T, F, F, E] [([E, F, T, T, T, F, F, E, T, T, F, F, E], [F, E, T, T, T, F, F, E, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1298 trivial)

theorem z_1300 : le (tf [E, F, T, T, T, F, F, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, F, F, E, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1301 : le (tf [F, T, E, E, F, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, T, F, T, F, F, E] [([F, E, T, E, F, T, T, T, F, T, F, F, E], [F, E, T, F, E, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_929 trivial)

theorem z_1302 : le (tf [E, T, F, T, F, E, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, T, F, T, F, F, E] [([E, T, F, E, F, T, T, T, F, T, F, F, E], [F, T, E, E, F, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1301 trivial)

theorem z_1303 : le (tf [F, T, E, T, F, F, E, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, T, E, T, F, F, E, E, F, T, T, T, F] [([F, E, T, T, F, F, E, E, F, T, T, T, F], [F, E, T, T, F, F, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_787 trivial)

theorem z_1304 : le (tf [E, T, F, T, F, F, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, F, E, T, F, E, T, T, F] [([E, T, F, T, F, F, E, E, F, T, T, T, F], [F, T, E, T, F, F, E, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1303 trivial)

theorem z_1305 : le (tf [E, T, F, T, F, F, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, F, E, T, T, F, E, T, F] [([E, T, F, T, F, F, E, T, E, F, T, T, F], [E, T, F, T, F, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1304 trivial)

theorem z_1306 : le (tf [E, T, F, T, F, T, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, T, F, E, F, E, T, T, F] [([E, T, F, T, F, E, F, T, F, E, T, T, F], [E, T, F, T, F, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1304 trivial)

theorem z_1307 : le (tf [E, T, F, T, F, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, T, F, E, T, F, E, T, F] [([E, T, F, T, F, E, F, T, T, F, E, T, F], [E, T, F, T, F, F, E, T, T, F, E, T, F]), ([E, T, F, T, F, T, F, E, E, F, T, T, F], [E, T, F, T, F, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1305 (And.intro z_1306 trivial))

theorem z_1308 : le (tf [E, T, F, T, F, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, T, F, T, E, E, F, T, F] [([E, T, F, T, F, T, F, E, T, E, F, T, F], [E, T, F, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1307 trivial)

theorem z_1309 : le (tf [E, T, F, T, F, T, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, T, E, T, F, T, F, E, F] [([E, T, F, T, F, E, T, T, F, T, F, E, F], [E, T, F, T, F, E, T, T, F, T, F, F, E]), ([E, T, F, T, F, T, E, T, F, E, F, T, F], [E, T, F, T, F, T, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1302 (And.intro z_1308 trivial))

theorem z_1310 : le (tf [F, T, E, F, E, E, F, T, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, F, T, T, T, F, T, F] [([F, E, T, F, E, E, F, T, T, T, F, T, F], [F, E, T, F, E, F, E, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_944 trivial)

theorem z_1311 : le (tf [F, T, E, E, F, T, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, F, E, T, T, F, T, F] [([F, E, T, E, F, T, F, E, T, T, F, T, F], [F, E, T, F, E, T, F, E, T, T, F, T, F]), ([F, T, E, E, F, E, F, T, T, T, F, T, F], [F, T, E, F, E, E, F, T, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_945 (And.intro z_1310 trivial))

theorem z_1312 : le (tf [F, T, E, E, F, T, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, F, E, T, F, T, F] [([F, E, T, E, F, T, T, F, E, T, F, T, F], [F, E, T, F, E, T, T, F, E, T, F, T, F]), ([F, T, E, E, F, T, E, F, T, T, F, T, F], [F, T, E, E, F, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_946 (And.intro z_1311 trivial))

theorem z_1313 : le (tf [F, T, E, E, F, T, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, T, F, E, F, T, F] [([F, E, T, E, F, T, T, T, F, E, F, T, F], [F, E, T, F, E, T, T, T, F, E, F, T, F]), ([F, T, E, E, F, T, T, E, F, T, F, T, F], [F, T, E, E, F, T, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_947 (And.intro z_1312 trivial))

theorem z_1314 : le (tf [F, T, E, T, F, E, E, F, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, T, F, E, E, F, T, T, F, T, F] [([F, E, T, T, F, E, E, F, T, T, F, T, F], [F, E, T, T, F, E, F, E, T, T, F, T, F]), ([F, T, E, E, F, T, E, F, T, T, F, T, F], [F, T, E, E, F, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_948 (And.intro z_1311 trivial))

theorem z_1315 : le (tf [E, T, F, T, F, E, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, F, E, T, F, T, F] [([E, T, F, E, F, T, T, F, E, T, F, T, F], [F, T, E, E, F, T, T, F, E, T, F, T, F]), ([E, T, F, T, F, E, E, F, T, T, F, T, F], [F, T, E, T, F, E, E, F, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1312 (And.intro z_1314 trivial))

theorem z_1316 : le (tf [E, T, F, T, F, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, T, F, E, F, T, F] [([E, T, F, E, F, T, T, T, F, E, F, T, F], [F, T, E, E, F, T, T, T, F, E, F, T, F]), ([E, T, F, T, F, E, T, E, F, T, F, T, F], [E, T, F, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1313 (And.intro z_1315 trivial))

theorem z_1317 : le (tf [E, T, F, T, T, F, E, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, F, E, T, F, T, F] [([E, T, F, T, E, F, T, F, E, T, F, T, F], [E, T, F, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1315 trivial)

theorem z_1318 : le (tf [E, T, F, T, T, F, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, T, F, E, F, T, F] [([E, T, F, T, E, F, T, T, F, E, F, T, F], [E, T, F, T, F, E, T, T, F, E, F, T, F]), ([E, T, F, T, T, F, E, E, F, T, F, T, F], [E, T, F, T, T, F, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1316 (And.intro z_1317 trivial))

theorem z_1319 : le (tf [E, T, F, T, T, E, F, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, E, F, T, F, T, F, E, F] [([E, T, F, T, E, T, F, T, F, T, F, E, F], [E, T, F, T, F, T, E, T, F, T, F, E, F]), ([E, T, F, T, T, E, F, T, F, E, F, T, F], [E, T, F, T, T, F, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1309 (And.intro z_1318 trivial))

theorem z_1320 : le (tf [E, T, F, T, T, T, F, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, F, E, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1321 : le (tf [E, T, F, T, T, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, E, F, T, E, F, F] [([E, T, F, T, T, E, F, T, F, T, E, F, F], [E, T, F, T, T, E, F, T, F, T, F, E, F]), ([E, T, F, T, T, T, F, E, F, E, T, F, F], [E, T, F, T, T, T, F, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1319 (And.intro z_1320 trivial))

theorem z_1322 : le (tf [F, T, E, T, T, F, F, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, F, T, T, F, E] [([F, E, T, T, T, F, F, E, F, T, T, F, E], [F, E, T, T, T, F, F, F, E, T, T, F, E]), ([F, T, E, T, T, F, F, E, F, T, E, F, T], [F, T, E, T, T, F, F, E, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_1194 trivial))

theorem z_1323 : le (tf [F, T, E, T, T, F, F, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, T, F, E, E, F, T] [([F, E, T, T, T, F, F, T, F, E, E, F, T], [F, E, T, T, T, F, F, T, F, E, F, E, T]), ([F, T, E, T, T, F, F, E, F, T, E, F, T], [F, T, E, T, T, F, F, E, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_404 (And.intro z_1194 trivial))

theorem z_1324 : le (tf [E, T, F, T, T, F, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, T, F, E, T, F, E] [([E, T, F, T, T, F, F, E, F, T, T, F, E], [F, T, E, T, T, F, F, E, F, T, T, F, E]), ([E, T, F, T, T, F, F, T, F, E, E, F, T], [F, T, E, T, T, F, F, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1322 (And.intro z_1323 trivial))

theorem z_1325 : le (tf [E, T, F, T, T, F, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, T, F, T, E, E, F] [([E, T, F, T, T, F, F, T, F, E, T, E, F], [E, T, F, T, T, F, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1324 trivial)

theorem z_1326 : le (tf [F, T, E, T, T, F, F, F, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, F, E, E, T, F, T] [([F, E, T, T, T, F, F, F, E, E, T, F, T], [F, E, T, T, T, F, F, F, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_412 trivial)

theorem z_1327 : le (tf [F, T, E, T, T, F, F, E, F, T, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, F, T, E, F, T] [([F, E, T, T, T, F, F, E, F, T, E, F, T], [F, E, T, T, T, F, F, F, E, T, E, F, T]), ([F, T, E, T, T, F, F, E, F, E, T, F, T], [F, T, E, T, T, F, F, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 (And.intro z_1326 trivial))

theorem z_1328 : le (tf [E, T, F, T, T, F, F, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, F, T, T, F, E] [([E, T, F, T, T, F, F, E, F, T, E, F, T], [F, T, E, T, T, F, F, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1327 trivial)

theorem z_1329 : le (tf [E, T, F, T, T, F, F, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, T, F, E, E, F, T] [([E, T, F, T, T, F, F, E, F, T, E, F, T], [F, T, E, T, T, F, F, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1327 trivial)

theorem z_1330 : le (tf [E, T, F, T, T, F, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, T, E, E, F, T, F] [([E, T, F, T, T, F, F, E, T, E, F, T, F], [E, T, F, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1187 trivial)

theorem z_1331 : le (tf [E, T, F, T, T, F, F, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1332 : le (tf [F, T, E, T, T, F, F, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, E, T, F, T, F] [([F, E, T, T, T, F, F, E, E, T, F, T, F], [F, E, T, T, T, F, F, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 trivial)

theorem z_1333 : le (tf [E, T, F, T, T, F, F, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, T, E, F, T, F] [([E, T, F, T, T, F, F, E, E, T, F, T, F], [F, T, E, T, T, F, F, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1332 trivial)

theorem z_1334 : le (tf [E, T, F, T, T, F, F, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, F, T, T, E, F] [([E, T, F, T, T, F, F, E, F, T, E, T, F], [E, T, F, T, T, F, F, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1195 trivial)

theorem z_1335 : le (tf [F, T, E, T, T, F, F, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, E, F, T, F, T] [([F, E, T, T, T, F, F, E, E, F, T, F, T], [F, E, T, T, T, F, F, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 trivial)

theorem z_1336 : le (tf [E, T, F, T, T, F, F, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, T, F, E, F, T] [([E, T, F, T, T, F, F, E, E, F, T, F, T], [F, T, E, T, T, F, F, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1335 trivial)

theorem z_1337 : le (tf [F, T, E, T, T, F, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, F, E, F, E, T, T, F] [([F, E, T, T, T, F, F, E, F, E, T, T, F], [F, E, T, T, T, F, F, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 trivial)

theorem z_1338 : le (tf [E, T, F, T, T, F, F, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, F, E, F, T, E, T, F] [([E, T, F, T, T, F, F, E, F, E, T, T, F], [F, T, E, T, T, F, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1337 trivial)

theorem z_1339 : le (tf [F, F, E, E, T, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, T, T, F, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1340 : le (tf [F, E, F, T, E, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, F, T, E, T, T, T, F, T, F, F, E] [([F, E, F, E, T, T, T, T, F, T, F, F, E], [F, F, E, E, T, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1339 trivial)

theorem z_1341 : le (tf [F, E, T, E, F, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, F, T, T, T, F, T, F, F, E] [([F, E, E, T, F, T, T, T, F, T, F, F, E], [F, E, F, T, E, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1340 trivial)

theorem z_1342 : le (tf [E, F, T, T, F, E, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, F, E, T, T, F, T, F, F, E] [([E, F, T, E, F, T, T, T, F, T, F, F, E], [F, E, T, E, F, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1341 trivial)

theorem z_1343 : le (tf [T, F, E, E, F, T, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, F, T, F, F, E] [([E, F, T, E, F, T, T, T, F, T, F, F, E], [F, E, T, E, F, T, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1341 trivial)

theorem z_1344 : le (tf [T, F, E, E, F, T, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, F, T, F, E, F] [([E, F, T, E, F, T, T, T, F, T, F, E, F], [F, E, T, E, F, T, T, T, F, T, F, E, F]), ([T, F, E, E, F, T, T, T, F, E, F, T, F], [T, F, E, F, E, T, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1083 (And.intro z_969 trivial))

theorem z_1345 : le (tf [T, F, E, E, F, T, T, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, E, F, T, T, T, F, T, E, F, F] [([E, F, T, E, F, T, T, T, F, T, E, F, F], [F, E, T, E, F, T, T, T, F, T, E, F, F]), ([T, F, E, E, F, T, T, T, F, E, T, F, F], [T, F, E, E, F, T, T, T, F, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1208 (And.intro z_374 trivial))

theorem z_1346 : le (tf [F, E, E, T, T, F, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, T, F, T, T, F, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1347 : le (tf [F, E, E, T, T, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, T, F, T, T, F, T, F, E, F] [([F, E, E, T, T, F, T, T, F, E, F, T, F], [F, E, E, T, T, F, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1346 trivial)

theorem z_1348 : le (tf [F, E, T, F, T, E, E, F, T, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, E, E, F, T, T, F, T, F] [([F, E, T, F, E, T, E, F, T, T, F, T, F], [F, E, T, F, E, T, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_945 trivial)

theorem z_1349 : le (tf [E, F, T, F, T, E, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, E, T, F, E, T, F, T, F] [([E, F, T, F, E, T, T, F, E, T, F, T, F], [F, E, T, F, E, T, T, F, E, T, F, T, F]), ([E, F, T, F, T, E, E, F, T, T, F, T, F], [F, E, T, F, T, E, E, F, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_946 (And.intro z_1348 trivial))

theorem z_1350 : le (tf [E, F, T, F, T, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, E, T, T, F, E, F, T, F] [([E, F, T, F, E, T, T, T, F, E, F, T, F], [F, E, T, F, E, T, T, T, F, E, F, T, F]), ([E, F, T, F, T, E, T, E, F, T, F, T, F], [E, F, T, F, T, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_947 (And.intro z_1349 trivial))

theorem z_1351 : le (tf [E, F, T, E, T, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, T, F, T, T, F, T, F, E, F] [([E, F, E, T, T, F, T, T, F, T, F, E, F], [F, E, E, T, T, F, T, T, F, T, F, E, F]), ([E, F, T, E, T, F, T, T, F, E, F, T, F], [E, F, T, F, T, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1347 (And.intro z_1350 trivial))

theorem z_1352 : le (tf [E, F, T, T, E, F, T, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, E, F, T, T, F, T, E, F, F] [([E, F, T, E, T, F, T, T, F, T, E, F, F], [E, F, T, E, T, F, T, T, F, T, F, E, F]), ([E, F, T, T, E, F, T, T, F, E, T, F, F], [E, F, T, T, F, E, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1351 (And.intro z_291 trivial))

theorem z_1353 : le (tf [F, E, E, T, T, F, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, T, F, T, T, F, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1354 : le (tf [E, F, T, E, T, F, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, F, T, E, T, F, T, T, F, T, F, F, E] [([E, F, E, T, T, F, T, T, F, T, F, F, E], [F, E, E, T, T, F, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1353 trivial)

theorem z_1355 : le (tf [T, F, E, F, T, E, E, F, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, E, E, F, T, T, F, T, F] [([E, F, T, F, T, E, E, F, T, T, F, T, F], [F, E, T, F, T, E, E, F, T, T, F, T, F]), ([T, F, E, F, E, T, E, F, T, T, F, T, F], [T, F, F, E, E, T, E, F, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1348 (And.intro z_967 trivial))

theorem z_1356 : le (tf [T, F, E, E, T, F, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, T, F, T, F, E, T, F, T, F] [([E, F, T, E, T, F, T, F, E, T, F, T, F], [E, F, T, F, T, E, T, F, E, T, F, T, F]), ([T, F, E, E, T, F, E, F, T, T, F, T, F], [T, F, E, F, T, E, E, F, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1349 (And.intro z_1355 trivial))

theorem z_1357 : le (tf [T, F, E, E, T, F, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, T, F, T, T, F, E, F, T, F] [([E, F, T, E, T, F, T, T, F, E, F, T, F], [E, F, T, F, T, E, T, T, F, E, F, T, F]), ([T, F, E, E, T, F, T, E, F, T, F, T, F], [T, F, E, E, T, F, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1350 (And.intro z_1356 trivial))

theorem z_1358 : le (tf [T, T, F, F, E, E, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1359 : le (tf [T, T, F, F, E, E, F, T, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, F, T, T, F, T, E, F] [([T, T, F, F, E, E, F, T, T, F, E, T, F], [T, T, F, F, E, F, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_557 trivial)

theorem z_1360 : le (tf [F, E, T, T, F, T, F, F, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, F, E, F, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1361 : le (tf [F, E, T, T, F, T, F, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, F, E, T, F, E, T] [([F, E, T, T, F, T, F, F, E, E, F, T, T], [F, E, T, T, F, T, F, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1360 trivial)

theorem z_1362 : le (tf [F, E, T, T, F, T, F, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, F, E, T, T, F, E] [([F, E, T, T, F, T, F, F, E, T, E, F, T], [F, E, T, T, F, T, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1361 trivial)

theorem z_1363 : le (tf [F, E, T, T, F, T, F, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, T, F, E, F, E, T] [([F, E, T, T, F, T, F, E, F, T, F, E, T], [F, E, T, T, F, T, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1361 trivial)

theorem z_1364 : le (tf [F, E, T, T, F, T, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, T, F, E, T, F, E] [([F, E, T, T, F, T, F, E, F, T, T, F, E], [F, E, T, T, F, T, F, F, E, T, T, F, E]), ([F, E, T, T, F, T, F, T, F, E, E, F, T], [F, E, T, T, F, T, F, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1362 (And.intro z_1363 trivial))

theorem z_1365 : le (tf [F, E, T, T, F, T, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, T, F, T, E, E, F] [([F, E, T, T, F, T, F, T, F, E, T, E, F], [F, E, T, T, F, T, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1364 trivial)

theorem z_1366 : le (tf [T, F, F, E, T, T, F, F, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, F, E, F, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1367 : le (tf [T, F, F, T, E, T, F, F, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, T, E, T, F, F, E, E, F, T, T] [([T, F, F, E, T, T, F, F, E, E, F, T, T], [T, F, F, E, T, T, F, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1366 trivial)

theorem z_1368 : le (tf [T, F, E, T, F, T, F, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, F, E, T, F, E, T] [([E, F, T, T, F, T, F, F, E, T, F, E, T], [F, E, T, T, F, T, F, F, E, T, F, E, T]), ([T, F, E, T, F, T, F, F, E, E, F, T, T], [T, F, F, T, E, T, F, F, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1361 (And.intro z_1367 trivial))

theorem z_1369 : le (tf [T, F, E, T, F, T, F, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, F, E, T, T, F, E] [([E, F, T, T, F, T, F, F, E, T, T, F, E], [F, E, T, T, F, T, F, F, E, T, T, F, E]), ([T, F, E, T, F, T, F, F, E, T, E, F, T], [T, F, E, T, F, T, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1362 (And.intro z_1368 trivial))

theorem z_1370 : le (tf [T, F, E, T, F, T, F, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, T, F, E, F, E, T] [([E, F, T, T, F, T, F, T, F, E, F, E, T], [F, E, T, T, F, T, F, T, F, E, F, E, T]), ([T, F, E, T, F, T, F, E, F, T, F, E, T], [T, F, E, T, F, T, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1363 (And.intro z_1368 trivial))

theorem z_1371 : le (tf [T, F, E, T, F, T, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, T, F, E, T, F, E] [([E, F, T, T, F, T, F, T, F, E, T, F, E], [F, E, T, T, F, T, F, T, F, E, T, F, E]), ([T, F, E, T, F, T, F, E, F, T, T, F, E], [T, F, E, T, F, T, F, F, E, T, T, F, E]), ([T, F, E, T, F, T, F, T, F, E, E, F, T], [T, F, E, T, F, T, F, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1364 (And.intro z_1369 (And.intro z_1370 trivial)))

theorem z_1372 : le (tf [T, F, E, T, F, T, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, T, F, T, E, E, F] [([E, F, T, T, F, T, F, T, F, T, E, E, F], [F, E, T, T, F, T, F, T, F, T, E, E, F]), ([T, F, E, T, F, T, F, T, F, E, T, E, F], [T, F, E, T, F, T, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1365 (And.intro z_1371 trivial))

theorem z_1373 : le (tf [F, E, T, T, F, F, F, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, F, E, F, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1374 : le (tf [F, E, T, T, F, F, F, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, F, E, T, F, E, T, T] [([F, E, T, T, F, F, F, E, E, F, T, T, T], [F, E, T, T, F, F, F, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1373 trivial)

theorem z_1375 : le (tf [F, E, T, T, F, F, F, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, F, T, E, E, F, T, T] [([F, E, T, T, F, F, F, E, T, E, F, T, T], [F, E, T, T, F, F, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1374 trivial)

theorem z_1376 : le (tf [F, E, T, T, F, F, E, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, F, T, F, E, T] [([F, E, T, T, F, F, E, T, F, E, F, T, T], [F, E, T, T, F, F, F, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1375 trivial)

theorem z_1377 : le (tf [F, E, T, T, F, F, E, T, F, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, F, T, T, F, E] [([F, E, T, T, F, F, E, T, F, T, E, F, T], [F, E, T, T, F, F, E, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1376 trivial)

theorem z_1378 : le (tf [F, E, T, T, F, T, F, F, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, F, F, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1379 : le (tf [F, E, T, T, F, T, F, F, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, F, E, F, T, E, T] [([F, E, T, T, F, T, F, F, E, F, E, T, T], [F, E, T, T, F, T, F, F, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1378 trivial)

theorem z_1380 : le (tf [F, E, T, T, F, T, F, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, F, E, T, E, F, T] [([F, E, T, T, F, T, F, F, E, E, T, F, T], [F, E, T, T, F, T, F, F, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1379 trivial)

theorem z_1381 : le (tf [F, E, T, T, F, T, F, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, E, F, T, T, F, E] [([F, E, T, T, F, E, F, T, F, T, T, F, E], [F, E, T, T, F, F, E, T, F, T, T, F, E]), ([F, E, T, T, F, T, F, E, F, T, E, F, T], [F, E, T, T, F, T, F, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1377 (And.intro z_1380 trivial))

theorem z_1382 : le (tf [F, E, T, T, F, T, F, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, T, F, E, E, F, T] [([F, E, T, T, F, T, F, E, F, T, E, F, T], [F, E, T, T, F, T, F, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1380 trivial)

theorem z_1383 : le (tf [E, F, T, T, F, T, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, F, T, F, T, F, E, T, F, E] [([E, F, T, T, F, T, F, E, F, T, T, F, E], [F, E, T, T, F, T, F, E, F, T, T, F, E]), ([E, F, T, T, F, T, F, T, F, E, E, F, T], [F, E, T, T, F, T, F, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1381 (And.intro z_1382 trivial))

theorem z_1384 : le (tf [E, F, T, T, F, T, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, T, F, T, F, T, E, E, F] [([E, F, T, T, F, T, F, T, F, E, T, E, F], [E, F, T, T, F, T, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1383 trivial)

theorem z_1385 : le (tf [T, F, F, F, E, E, F, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, F, E, T, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1386 : le (tf [T, F, F, F, E, E, T, F, E, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, F, E, T, F, T, T] [([T, F, F, F, E, E, E, F, T, T, F, T, T], [T, F, F, F, E, E, F, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1385 trivial)

theorem z_1387 : le (tf [T, F, F, F, E, E, T, T, F, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, T, F, E, F, T, T] [([T, F, F, F, E, E, T, E, F, T, F, T, T], [T, F, F, F, E, E, T, F, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1386 trivial)

theorem z_1388 : le (tf [T, F, F, E, F, E, T, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, F, T, F, E, T] [([T, F, F, E, F, E, T, T, F, E, F, T, T], [T, F, F, F, E, E, T, T, F, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1387 trivial)

theorem z_1389 : le (tf [T, F, F, E, F, E, T, T, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, F, T, T, F, E] [([T, F, F, E, F, E, T, T, F, T, E, F, T], [T, F, F, E, F, E, T, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1388 trivial)

theorem z_1390 : le (tf [T, F, F, F, F, E, F, E, E, T, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, F, E, E, T, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1391 : le (tf [T, F, F, F, F, E, E, F, T, E, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, F, T, E, T, T, T] [([T, F, F, F, F, E, E, F, E, T, T, T, T], [T, F, F, F, F, E, F, E, E, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1390 trivial)

theorem z_1392 : le (tf [T, F, F, F, F, E, E, T, E, F, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, T, E, F, T, T, T] [([T, F, F, F, F, E, E, E, T, F, T, T, T], [T, F, F, F, F, E, E, F, T, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1391 trivial)

theorem z_1393 : le (tf [T, F, F, F, E, F, E, T, T, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, T, T, F, E, T, T] [([T, F, F, F, E, F, E, T, E, F, T, T, T], [T, F, F, F, F, E, E, T, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1392 trivial)

theorem z_1394 : le (tf [T, F, F, F, F, E, E, E, F, T, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, E, F, T, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1395 : le (tf [T, F, F, F, E, F, E, T, F, E, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, T, F, E, T, T, T] [([T, F, F, F, E, F, E, E, F, T, T, T, T], [T, F, F, F, F, E, E, E, F, T, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1394 trivial)

theorem z_1396 : le (tf [T, F, F, F, E, T, F, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, F, E, F, E, T, T, T] [([T, F, F, F, E, E, F, T, F, E, T, T, T], [T, F, F, F, E, F, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1395 trivial)

theorem z_1397 : le (tf [T, F, F, F, E, T, F, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, F, E, T, F, E, T, T] [([T, F, F, F, E, E, F, T, T, F, E, T, T], [T, F, F, F, E, F, E, T, T, F, E, T, T]), ([T, F, F, F, E, T, F, E, E, F, T, T, T], [T, F, F, F, E, T, F, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1393 (And.intro z_1396 trivial))

theorem z_1398 : le (tf [T, F, F, F, E, T, F, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, F, T, E, E, F, T, T] [([T, F, F, F, E, T, F, E, T, E, F, T, T], [T, F, F, F, E, T, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1397 trivial)

theorem z_1399 : le (tf [T, F, F, F, F, E, E, E, T, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, E, T, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1400 : le (tf [T, F, F, F, E, F, E, T, E, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, T, E, T, F, T, T] [([T, F, F, F, E, F, E, E, T, T, F, T, T], [T, F, F, F, F, E, E, E, T, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1399 trivial)

theorem z_1401 : le (tf [T, F, F, F, E, T, F, E, E, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, F, E, E, T, F, T, T] [([T, F, F, F, E, E, F, T, E, T, F, T, T], [T, F, F, F, E, F, E, T, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1400 trivial)

theorem z_1402 : le (tf [T, F, F, F, T, E, E, F, E, T, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, T, E, E, F, E, T, F, T, T] [([T, F, F, F, E, T, E, F, E, T, F, T, T], [T, F, F, F, E, T, F, E, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1401 trivial)

theorem z_1403 : le (tf [T, F, F, F, T, E, E, T, F, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, T, E, E, T, F, E, F, T, T] [([T, F, F, F, E, T, E, T, F, E, F, T, T], [T, F, F, F, E, T, F, T, E, E, F, T, T]), ([T, F, F, F, T, E, E, E, F, T, F, T, T], [T, F, F, F, T, E, E, F, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1398 (And.intro z_1402 trivial))

theorem z_1404 : le (tf [T, F, F, E, T, F, E, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, F, T, F, E, T] [([T, F, F, E, E, F, T, T, F, T, F, E, T], [T, F, F, E, F, E, T, T, F, T, F, E, T]), ([T, F, F, E, T, F, E, T, F, E, F, T, T], [T, F, F, F, T, E, E, T, F, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1388 (And.intro z_1403 trivial))

theorem z_1405 : le (tf [T, F, F, E, T, F, E, T, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, F, T, T, F, E] [([T, F, F, E, E, F, T, T, F, T, T, F, E], [T, F, F, E, F, E, T, T, F, T, T, F, E]), ([T, F, F, E, T, F, E, T, F, T, E, F, T], [T, F, F, E, T, F, E, T, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1389 (And.intro z_1404 trivial))

theorem z_1406 : le (tf [T, F, F, F, E, E, F, T, T, F, T, E, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, F, T, T, F, T, E, T] [([T, F, F, F, E, E, F, T, T, F, E, T, T], [T, F, F, F, E, F, E, T, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1393 trivial)

theorem z_1407 : le (tf [T, F, F, E, F, T, F, E, T, F, T, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, F, E, T, F, T, E, T] [([T, F, F, E, F, E, F, T, T, F, T, E, T], [T, F, F, F, E, E, F, T, T, F, T, E, T]), ([T, F, F, E, F, T, F, E, T, F, E, T, T], [T, F, F, F, E, T, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1406 (And.intro z_1397 trivial))

theorem z_1408 : le (tf [T, F, F, E, F, T, F, T, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, F, T, E, E, T, F, T] [([T, F, F, E, F, T, F, E, T, E, T, F, T], [T, F, F, E, F, T, F, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1407 trivial)

theorem z_1409 : le (tf [T, F, F, E, F, T, F, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, F, E, E, T, T, F, T] [([T, F, F, E, F, E, F, T, E, T, T, F, T], [T, F, F, F, E, E, F, T, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_696 trivial)

theorem z_1410 : le (tf [T, F, F, T, F, E, E, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, E, E, F, E, T, T, F, T] [([T, F, F, E, F, T, E, F, E, T, T, F, T], [T, F, F, E, F, T, F, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1409 trivial)

theorem z_1411 : le (tf [T, F, F, T, F, E, E, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, E, E, T, F, E, T, F, T] [([T, F, F, E, F, T, E, T, F, E, T, F, T], [T, F, F, E, F, T, F, T, E, E, T, F, T]), ([T, F, F, T, F, E, E, E, F, T, T, F, T], [T, F, F, T, F, E, E, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1408 (And.intro z_1410 trivial))

theorem z_1412 : le (tf [T, F, F, T, E, F, E, T, F, T, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, E, F, E, T, F, T, E, F, T] [([T, F, F, E, T, F, E, T, F, T, E, F, T], [T, F, F, E, T, F, E, T, F, T, F, E, T]), ([T, F, F, T, E, F, E, T, F, E, T, F, T], [T, F, F, T, F, E, E, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1404 (And.intro z_1411 trivial))

theorem z_1413 : le (tf [T, F, F, T, E, E, F, T, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, T, F, T, T, F, E] [([T, F, F, E, T, E, F, T, F, T, T, F, E], [T, F, F, E, T, F, E, T, F, T, T, F, E]), ([T, F, F, T, E, E, F, T, F, T, E, F, T], [T, F, F, T, E, F, E, T, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1405 (And.intro z_1412 trivial))

theorem z_1414 : le (tf [T, F, F, E, T, T, F, F, F, E, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, F, F, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1415 : le (tf [T, F, F, E, T, T, F, F, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, F, E, F, T, E, T] [([T, F, F, E, T, T, F, F, E, F, E, T, T], [T, F, F, E, T, T, F, F, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1414 trivial)

theorem z_1416 : le (tf [T, F, F, E, T, T, F, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, F, E, T, E, F, T] [([T, F, F, E, T, T, F, F, E, E, T, F, T], [T, F, F, E, T, T, F, F, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1415 trivial)

theorem z_1417 : le (tf [T, F, F, F, E, T, T, F, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, T, F, E, F, E, T, T] [([T, F, F, F, E, T, E, F, T, F, E, T, T], [T, F, F, F, E, T, F, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1397 trivial)

theorem z_1418 : le (tf [T, F, F, E, F, T, T, F, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, T, F, E, F, T, E, T] [([T, F, F, E, F, T, E, F, T, F, T, E, T], [T, F, F, E, F, T, F, E, T, F, T, E, T]), ([T, F, F, E, F, T, T, F, E, F, E, T, T], [T, F, F, F, E, T, T, F, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1407 (And.intro z_1417 trivial))

theorem z_1419 : le (tf [T, F, F, T, F, F, E, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, F, E, E, E, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1420 : le (tf [T, F, F, T, F, E, F, E, T, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, E, F, E, T, E, T, F, T] [([T, F, F, E, F, T, F, E, T, E, T, F, T], [T, F, F, E, F, T, F, E, T, F, T, E, T]), ([T, F, F, T, F, E, F, E, E, T, T, F, T], [T, F, F, T, F, F, E, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1407 (And.intro z_1419 trivial))

theorem z_1421 : le (tf [T, F, F, T, F, E, T, F, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, E, T, F, E, E, T, F, T] [([T, F, F, E, F, T, T, F, E, E, T, F, T], [T, F, F, E, F, T, T, F, E, F, T, E, T]), ([T, F, F, T, F, E, E, F, T, E, T, F, T], [T, F, F, T, F, E, F, E, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1418 (And.intro z_1420 trivial))

theorem z_1422 : le (tf [T, F, F, T, F, T, E, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, T, E, E, F, E, T, F, T] [([T, F, F, T, F, E, T, E, F, E, T, F, T], [T, F, F, T, F, E, T, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1421 trivial)

theorem z_1423 : le (tf [T, F, F, T, E, T, F, E, F, T, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, E, T, F, E, F, T, E, F, T] [([T, F, F, E, T, T, F, E, F, T, E, F, T], [T, F, F, E, T, T, F, F, E, T, E, F, T]), ([T, F, F, T, E, E, F, T, F, T, E, F, T], [T, F, F, T, E, F, E, T, F, T, E, F, T]), ([T, F, F, T, E, T, F, E, F, E, T, F, T], [T, F, F, T, F, T, E, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1416 (And.intro z_1412 (And.intro z_1422 trivial)))

theorem z_1424 : le (tf [T, F, E, T, F, T, F, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, E, F, T, T, F, E] [([E, F, T, T, F, T, F, E, F, T, T, F, E], [F, E, T, T, F, T, F, E, F, T, T, F, E]), ([T, F, E, T, F, E, F, T, F, T, T, F, E], [T, F, F, T, E, E, F, T, F, T, T, F, E]), ([T, F, E, T, F, T, F, E, F, T, E, F, T], [T, F, F, T, E, T, F, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1381 (And.intro z_1413 (And.intro z_1423 trivial)))

theorem z_1425 : le (tf [T, F, E, T, F, T, F, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, T, F, E, E, F, T] [([E, F, T, T, F, T, F, T, F, E, E, F, T], [F, E, T, T, F, T, F, T, F, E, E, F, T]), ([T, F, E, T, F, T, F, E, F, T, E, F, T], [T, F, F, T, E, T, F, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1382 (And.intro z_1423 trivial))

theorem z_1426 : le (tf [F, E, T, T, F, F, E, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, T, T, F, E, F] [([F, E, T, T, F, F, E, T, T, E, F, T, F], [F, E, T, T, F, F, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_931 trivial)

theorem z_1427 : le (tf [F, E, T, T, F, T, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, E, T, T, F, E, F] [([F, E, T, T, F, E, F, T, T, T, F, E, F], [F, E, T, T, F, F, E, T, T, T, F, E, F]), ([F, E, T, T, F, T, F, E, T, E, F, T, F], [F, E, T, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1426 (And.intro z_933 trivial))

theorem z_1428 : le (tf [E, F, T, T, F, T, F, T, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, T, F, T, E, T, F, E, F] [([E, F, T, T, F, T, F, E, T, T, F, E, F], [F, E, T, T, F, T, F, E, T, T, F, E, F]), ([E, F, T, T, F, T, F, T, E, E, F, T, F], [F, E, T, T, F, T, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1427 (And.intro z_934 trivial))

theorem z_1429 : le (tf [T, F, F, T, E, E, F, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, T, T, T, F, E, F] [([T, F, F, E, T, E, F, T, T, T, F, E, F], [T, F, F, E, T, F, E, T, T, T, F, E, F]), ([T, F, F, T, E, E, F, T, T, E, F, T, F], [T, F, F, T, E, E, F, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_165 (And.intro z_960 trivial))

theorem z_1430 : le (tf [T, F, E, T, F, T, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, E, T, T, F, E, F] [([E, F, T, T, F, T, F, E, T, T, F, E, F], [F, E, T, T, F, T, F, E, T, T, F, E, F]), ([T, F, E, T, F, E, F, T, T, T, F, E, F], [T, F, F, T, E, E, F, T, T, T, F, E, F]), ([T, F, E, T, F, T, F, E, T, E, F, T, F], [T, F, E, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1427 (And.intro z_1429 (And.intro z_962 trivial)))

theorem z_1431 : le (tf [F, F, E, E, F, E, T, T, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, T, T, F, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1432 : le (tf [F, F, E, E, T, F, E, T, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, E, T, F, T, T, T, F] [([F, F, E, E, E, F, T, T, F, T, T, T, F], [F, F, E, E, F, E, T, T, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1431 trivial)

theorem z_1433 : le (tf [F, F, E, E, T, T, F, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, T, F, E, F, T, T, T, F] [([F, F, E, E, T, E, F, T, F, T, T, T, F], [F, F, E, E, T, F, E, T, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1432 trivial)

theorem z_1434 : le (tf [F, E, F, E, T, T, F, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, F, T, F, E, T, T, F] [([F, E, F, E, T, T, F, E, F, T, T, T, F], [F, F, E, E, T, T, F, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1433 trivial)

theorem z_1435 : le (tf [F, E, F, E, T, T, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, F, T, T, F, E, T, F] [([F, E, F, E, T, T, F, T, E, F, T, T, F], [F, E, F, E, T, T, F, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1434 trivial)

theorem z_1436 : le (tf [F, F, F, E, F, E, E, T, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, F, E, E, T, T, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1437 : le (tf [F, F, F, E, E, F, T, E, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, T, E, T, T, T, T, F] [([F, F, F, E, E, F, E, T, T, T, T, T, F], [F, F, F, E, F, E, E, T, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1436 trivial)

theorem z_1438 : le (tf [F, F, F, E, E, T, E, F, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, E, F, T, T, T, T, F] [([F, F, F, E, E, E, T, F, T, T, T, T, F], [F, F, F, E, E, F, T, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1437 trivial)

theorem z_1439 : le (tf [F, F, E, F, E, T, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, F, E, T, T, T, F] [([F, F, E, F, E, T, E, F, T, T, T, T, F], [F, F, F, E, E, T, E, F, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1438 trivial)

theorem z_1440 : le (tf [F, F, F, E, E, E, F, T, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, F, T, T, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1441 : le (tf [F, F, E, F, E, T, F, E, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, F, E, T, T, T, T, F] [([F, F, E, F, E, E, F, T, T, T, T, T, F], [F, F, F, E, E, E, F, T, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1440 trivial)

theorem z_1442 : le (tf [F, F, E, T, F, E, F, E, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, F, E, T, T, T, T, F] [([F, F, E, E, F, T, F, E, T, T, T, T, F], [F, F, E, F, E, T, F, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1441 trivial)

theorem z_1443 : le (tf [F, F, E, T, F, E, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, F, E, T, T, T, F] [([F, F, E, E, F, T, T, F, E, T, T, T, F], [F, F, E, F, E, T, T, F, E, T, T, T, F]), ([F, F, E, T, F, E, E, F, T, T, T, T, F], [F, F, E, T, F, E, F, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1439 (And.intro z_1442 trivial))

theorem z_1444 : le (tf [F, F, E, T, F, T, E, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, T, E, E, F, T, T, T, F] [([F, F, E, T, F, E, T, E, F, T, T, T, F], [F, F, E, T, F, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1443 trivial)

theorem z_1445 : le (tf [F, F, F, E, E, E, T, T, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, T, T, F, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1446 : le (tf [F, F, E, F, E, T, E, T, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, E, T, F, T, T, T, F] [([F, F, E, F, E, E, T, T, F, T, T, T, F], [F, F, F, E, E, E, T, T, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1445 trivial)

theorem z_1447 : le (tf [F, F, E, T, F, E, E, T, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, E, T, F, T, T, T, F] [([F, F, E, E, F, T, E, T, F, T, T, T, F], [F, F, E, F, E, T, E, T, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1446 trivial)

theorem z_1448 : le (tf [F, F, T, E, E, F, E, T, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, E, T, F, T, T, T, F] [([F, F, E, T, E, F, E, T, F, T, T, T, F], [F, F, E, T, F, E, E, T, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1447 trivial)

theorem z_1449 : le (tf [F, F, T, E, E, T, F, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, T, E, E, T, F, E, F, T, T, T, F] [([F, F, E, T, E, T, F, E, F, T, T, T, F], [F, F, E, T, F, T, E, E, F, T, T, T, F]), ([F, F, T, E, E, E, F, T, F, T, T, T, F], [F, F, T, E, E, F, E, T, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1444 (And.intro z_1448 trivial))

theorem z_1450 : le (tf [F, E, T, F, E, T, F, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, F, T, F, E, T, T, F] [([F, E, E, F, T, T, F, T, F, E, T, T, F], [F, E, F, E, T, T, F, T, F, E, T, T, F]), ([F, E, T, F, E, T, F, E, F, T, T, T, F], [F, F, T, E, E, T, F, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1434 (And.intro z_1449 trivial))

theorem z_1451 : le (tf [F, E, T, F, E, T, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, F, T, T, F, E, T, F] [([F, E, E, F, T, T, F, T, T, F, E, T, F], [F, E, F, E, T, T, F, T, T, F, E, T, F]), ([F, E, T, F, E, T, F, T, E, F, T, T, F], [F, E, T, F, E, T, F, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1435 (And.intro z_1450 trivial))

theorem z_1452 : le (tf [F, E, T, T, F, F, F, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, F, E, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1453 : le (tf [F, E, T, T, F, F, E, F, T, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, F, T, E, T, T, F] [([F, E, T, T, F, F, E, F, E, T, T, T, F], [F, E, T, T, F, F, F, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1452 trivial)

theorem z_1454 : le (tf [F, E, T, T, F, F, E, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, E, F, T, T, F] [([F, E, T, T, F, F, E, E, T, F, T, T, F], [F, E, T, T, F, F, E, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1453 trivial)

theorem z_1455 : le (tf [F, E, T, T, F, E, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, F, T, T, F, E, T, F] [([F, E, T, E, F, T, F, T, T, F, E, T, F], [F, E, T, F, E, T, F, T, T, F, E, T, F]), ([F, E, T, T, F, E, F, T, E, F, T, T, F], [F, E, T, T, F, F, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1451 (And.intro z_1454 trivial))

theorem z_1456 : le (tf [F, E, T, T, F, T, F, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, E, E, F, T, T, F] [([F, E, T, T, F, E, F, T, E, F, T, T, F], [F, E, T, T, F, F, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1454 trivial)

theorem z_1457 : le (tf [E, F, T, T, F, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, T, F, E, T, F, E, T, F] [([E, F, T, T, F, E, F, T, T, F, E, T, F], [F, E, T, T, F, E, F, T, T, F, E, T, F]), ([E, F, T, T, F, T, F, E, E, F, T, T, F], [F, E, T, T, F, T, F, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1455 (And.intro z_1456 trivial))

theorem z_1458 : le (tf [E, F, T, T, F, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, T, F, T, E, E, F, T, F] [([E, F, T, T, F, T, F, E, T, E, F, T, F], [E, F, T, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1457 trivial)

theorem z_1459 : le (tf [E, F, T, T, F, T, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, F, T, E, T, F, T, F, E, F] [([E, F, T, T, F, E, T, T, F, T, F, E, F], [F, E, T, T, F, E, T, T, F, T, F, E, F]), ([E, F, T, T, F, T, E, T, F, E, F, T, F], [E, F, T, T, F, T, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_900 (And.intro z_1458 trivial))

theorem z_1460 : le (tf [T, F, F, E, F, E, T, F, T, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, F, T, E, T, T, F] [([T, F, F, E, F, E, T, F, E, T, T, T, F], [T, F, F, F, E, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1216 trivial)

theorem z_1461 : le (tf [T, F, F, E, F, T, E, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, E, E, T, F, T, T, F] [([T, F, F, E, F, E, T, E, T, F, T, T, F], [T, F, F, E, F, E, T, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1460 trivial)

theorem z_1462 : le (tf [T, F, F, E, E, T, F, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, E, T, F, T, E, F, T, T, F] [([T, F, F, E, E, T, F, E, T, F, T, T, F], [T, F, F, E, F, T, E, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1461 trivial)

theorem z_1463 : le (tf [T, F, E, F, E, T, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, F, T, T, F, E, T, F] [([E, F, T, F, E, T, F, T, T, F, E, T, F], [F, E, T, F, E, T, F, T, T, F, E, T, F]), ([T, F, E, F, E, T, F, T, E, F, T, T, F], [T, F, F, E, E, T, F, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1451 (And.intro z_1462 trivial))

theorem z_1464 : le (tf [T, F, F, E, F, E, T, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, E, F, T, T, F] [([T, F, F, E, F, E, T, E, T, F, T, T, F], [T, F, F, E, F, E, T, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1460 trivial)

theorem z_1465 : le (tf [T, F, F, F, F, E, E, E, T, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, E, T, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1466 : le (tf [T, F, F, F, E, F, E, T, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, T, E, T, T, T, F] [([T, F, F, F, E, F, E, E, T, T, T, T, F], [T, F, F, F, F, E, E, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1465 trivial)

theorem z_1467 : le (tf [T, F, F, F, E, T, F, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, F, E, E, T, T, T, F] [([T, F, F, F, E, E, F, T, E, T, T, T, F], [T, F, F, F, E, F, E, T, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1466 trivial)

theorem z_1468 : le (tf [T, F, F, F, T, E, E, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, T, E, E, F, E, T, T, T, F] [([T, F, F, F, E, T, E, F, E, T, T, T, F], [T, F, F, F, E, T, F, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1467 trivial)

theorem z_1469 : le (tf [T, F, F, E, T, F, E, F, T, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, F, T, E, T, T, F] [([T, F, F, E, E, F, T, F, T, E, T, T, F], [T, F, F, E, F, E, T, F, T, E, T, T, F]), ([T, F, F, E, T, F, E, F, E, T, T, T, F], [T, F, F, F, T, E, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1460 (And.intro z_1468 trivial))

theorem z_1470 : le (tf [T, F, F, E, T, F, E, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, E, F, T, T, F] [([T, F, F, E, E, F, T, T, E, F, T, T, F], [T, F, F, E, F, E, T, T, E, F, T, T, F]), ([T, F, F, E, T, F, E, E, T, F, T, T, F], [T, F, F, E, T, F, E, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1464 (And.intro z_1469 trivial))

theorem z_1471 : le (tf [T, F, F, T, E, F, E, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, F, E, E, T, F, T, T, F] [([T, F, F, E, T, F, E, E, T, F, T, T, F], [T, F, F, E, T, F, E, F, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1469 trivial)

theorem z_1472 : le (tf [T, F, F, T, E, E, F, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, T, E, F, T, T, F] [([T, F, F, E, T, E, F, T, E, F, T, T, F], [T, F, F, E, T, F, E, T, E, F, T, T, F]), ([T, F, F, T, E, E, F, E, T, F, T, T, F], [T, F, F, T, E, F, E, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1470 (And.intro z_1471 trivial))

theorem z_1473 : le (tf [T, F, E, T, F, E, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, F, T, T, F, E, T, F] [([E, F, T, T, F, E, F, T, T, F, E, T, F], [F, E, T, T, F, E, F, T, T, F, E, T, F]), ([T, F, E, E, F, T, F, T, T, F, E, T, F], [T, F, E, F, E, T, F, T, T, F, E, T, F]), ([T, F, E, T, F, E, F, T, E, F, T, T, F], [T, F, F, T, E, E, F, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1455 (And.intro z_1463 (And.intro z_1472 trivial)))

theorem z_1474 : le (tf [T, F, E, T, F, T, F, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, E, E, F, T, T, F] [([E, F, T, T, F, T, F, E, E, F, T, T, F], [F, E, T, T, F, T, F, E, E, F, T, T, F]), ([T, F, E, T, F, E, F, T, E, F, T, T, F], [T, F, F, T, E, E, F, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1456 (And.intro z_1472 trivial))

theorem z_1475 : le (tf [F, E, T, T, F, T, E, E, F, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, E, E, F, T, F, T, F] [([F, E, T, T, F, E, T, E, F, T, F, T, F], [F, E, T, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_949 trivial)

theorem z_1476 : le (tf [T, F, E, T, F, T, E, E, F, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, E, E, F, T, F, T, F] [([E, F, T, T, F, T, E, E, F, T, F, T, F], [F, E, T, T, F, T, E, E, F, T, F, T, F]), ([T, F, E, T, F, E, T, E, F, T, F, T, F], [T, F, E, T, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1475 (And.intro z_973 trivial))

theorem z_1477 : le (tf [T, E, F, T, F, T, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, F, T, F, T, E, T, F, E, F, T, F] [([E, T, F, T, F, T, E, T, F, E, F, T, F], [E, T, F, T, F, T, F, T, E, E, F, T, F]), ([T, E, F, T, F, E, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, E, F, T, F]), ([T, E, F, T, F, T, E, E, F, T, F, T, F], [T, F, E, T, F, T, E, E, F, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1308 (And.intro z_974 (And.intro z_1476 trivial)))

theorem z_1478 : le (tf [T, E, F, T, F, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, F, E, T, T, F, T, F, E, F] [([E, T, F, T, F, E, T, T, F, T, F, E, F], [E, T, F, T, F, E, T, T, F, T, F, F, E]), ([T, E, F, E, F, T, T, T, F, T, F, E, F], [T, F, E, E, F, T, T, T, F, T, F, E, F]), ([T, E, F, T, F, E, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1302 (And.intro z_1344 (And.intro z_974 trivial)))

theorem z_1479 : le (tf [T, T, F, F, E, E, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, T, F, E, T, F, F] [([T, T, F, F, E, E, T, E, F, T, T, F, F], [T, T, F, F, E, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_512 trivial)

theorem z_1480 : le (tf [T, T, F, E, F, E, T, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, E, T, T, F, T, E, F, F] [([T, E, F, T, F, E, T, T, F, T, E, F, F], [T, E, F, T, F, E, T, T, F, T, F, E, F]), ([T, T, F, E, F, E, T, T, F, E, T, F, F], [T, T, F, F, E, E, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1478 (And.intro z_1479 trivial))

theorem z_1481 : le (tf [E, T, T, F, F, E, T, T, F, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, T, T, F, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1482 : le (tf [E, T, T, F, F, E, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, T, T, F, T, F, E, F] [([E, T, T, F, F, E, T, T, F, E, F, T, F], [E, T, T, F, F, E, T, T, F, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1481 trivial)

theorem z_1483 : le (tf [E, T, T, F, T, F, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, F, E, F, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1484 : le (tf [E, T, T, F, T, F, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, F, E, T, F, E, T, F] [([E, T, T, F, T, F, F, E, E, F, T, T, F], [E, T, T, F, T, F, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1483 trivial)

theorem z_1485 : le (tf [E, T, T, F, T, F, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, F, T, E, E, F, T, F] [([E, T, T, F, T, F, F, E, T, E, F, T, F], [E, T, T, F, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1484 trivial)

theorem z_1486 : le (tf [E, T, T, F, T, F, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, E, T, F, T, F, E, F] [([E, T, T, F, E, F, T, T, F, T, F, E, F], [E, T, T, F, F, E, T, T, F, T, F, E, F]), ([E, T, T, F, T, F, E, T, F, E, F, T, F], [E, T, T, F, T, F, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1482 (And.intro z_1485 trivial))

theorem z_1487 : le (tf [E, F, E, T, T, F, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, T, F, T, T, F, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1488 : le (tf [E, T, F, E, T, F, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, T, F, T, T, F, T, F, F, E] [([E, E, F, T, T, F, T, T, F, T, F, F, E], [E, F, E, T, T, F, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1487 trivial)

theorem z_1489 : le (tf [T, E, F, E, T, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, T, F, T, T, F, T, F, E, F] [([E, T, F, E, T, F, T, T, F, T, F, E, F], [E, T, F, E, T, F, T, T, F, T, F, F, E]), ([T, E, F, E, T, F, T, T, F, E, F, T, F], [T, F, E, E, T, F, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1488 (And.intro z_1357 trivial))

theorem z_1490 : le (tf [T, F, T, E, F, E, E, F, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, E, F, E, E, F, T, T, F, T, F] [([T, F, E, T, F, E, E, F, T, T, F, T, F], [T, F, E, T, F, E, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_972 trivial)

theorem z_1491 : le (tf [T, F, T, E, E, F, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, E, E, F, T, F, E, T, F, T, F] [([T, F, E, T, E, F, T, F, E, T, F, T, F], [T, F, E, T, F, E, T, F, E, T, F, T, F]), ([T, F, T, E, E, F, E, F, T, T, F, T, F], [T, F, T, E, F, E, E, F, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_973 (And.intro z_1490 trivial))

theorem z_1492 : le (tf [T, F, T, E, E, F, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, E, E, F, T, T, F, E, F, T, F] [([T, F, E, T, E, F, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, E, F, T, F]), ([T, F, T, E, E, F, T, E, F, T, F, T, F], [T, F, T, E, E, F, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_974 (And.intro z_1491 trivial))

theorem z_1493 : le (tf [T, E, T, F, E, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, F, T, T, F, T, F, E, F] [([E, T, T, F, E, F, T, T, F, T, F, E, F], [E, T, T, F, F, E, T, T, F, T, F, E, F]), ([T, E, E, F, T, F, T, T, F, T, F, E, F], [T, E, F, E, T, F, T, T, F, T, F, E, F]), ([T, E, T, F, E, F, T, T, F, E, F, T, F], [T, F, T, E, E, F, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1482 (And.intro z_1489 (And.intro z_1492 trivial)))

theorem z_1494 : le (tf [T, F, T, E, T, F, E, E, F, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, E, E, F, T, F, T, F] [([T, F, E, T, T, F, E, E, F, T, F, T, F], [T, F, E, T, T, F, E, F, E, T, F, T, F]), ([T, F, T, E, E, F, T, E, F, T, F, T, F], [T, F, T, E, E, F, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_975 (And.intro z_1491 trivial))

theorem z_1495 : le (tf [T, E, T, F, T, F, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, F, E, T, F, E, F, T, F] [([E, T, T, F, T, F, E, T, F, E, F, T, F], [E, T, T, F, T, F, F, T, E, E, F, T, F]), ([T, E, T, F, E, F, T, T, F, E, F, T, F], [T, F, T, E, E, F, T, T, F, E, F, T, F]), ([T, E, T, F, T, F, E, E, F, T, F, T, F], [T, F, T, E, T, F, E, E, F, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1485 (And.intro z_1492 (And.intro z_1494 trivial)))

theorem z_1496 : le (tf [T, T, T, T, F, F, T, F, F, F, E, E, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, T, F, F, F, E, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1497 : le (tf [T, T, T, T, F, F, F, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1498 : le (tf [T, T, T, T, F, F, F, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, E, F, T, E, F] [([T, T, T, T, F, F, F, E, E, F, E, T, F], [T, T, T, T, F, F, F, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1497 trivial)

theorem z_1499 : le (tf [T, T, T, T, F, F, E, F, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, F, T, F, E, E, F] [([T, T, T, T, F, F, E, F, E, F, T, E, F], [T, T, T, T, F, F, F, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1498 trivial)

theorem z_1500 : le (tf [T, T, T, T, F, F, F, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, E, F, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1501 : le (tf [T, T, T, T, F, F, F, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, E, T, F, E, F] [([T, T, T, T, F, F, F, E, E, E, F, T, F], [T, T, T, T, F, F, F, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1500 trivial)

theorem z_1502 : le (tf [T, T, T, T, F, F, E, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, F, T, E, F, E, F] [([T, T, T, T, F, F, E, F, E, T, F, E, F], [T, T, T, T, F, F, F, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1501 trivial)

theorem z_1503 : le (tf [T, T, T, T, F, F, F, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, E, T, E, F, F] [([T, T, T, T, F, F, F, E, E, E, T, F, F], [T, T, T, T, F, F, F, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1498 trivial)

theorem z_1504 : le (tf [T, T, T, T, F, F, E, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, F, T, E, E, F, F] [([T, T, T, T, F, F, E, F, E, T, E, F, F], [T, T, T, T, F, F, F, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1503 trivial)

theorem z_1505 : le (tf [T, T, T, T, F, F, F, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, E, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1506 : le (tf [T, T, T, T, F, F, E, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, F, E, T, E, F, F] [([T, T, T, T, F, F, E, F, E, E, T, F, F], [T, T, T, T, F, F, F, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1505 trivial)

theorem z_1507 : le (tf [T, T, T, T, F, F, E, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, T, F, E, E, F, F] [([T, T, T, T, F, F, E, E, F, T, E, F, F], [T, T, T, T, F, F, E, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1506 trivial)

theorem z_1508 : le (tf [T, T, T, T, F, F, E, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, T, E, F, E, F, F] [([T, T, T, T, F, F, E, E, T, F, E, F, F], [T, T, T, T, F, F, E, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1504 trivial)

theorem z_1509 : le (tf [T, T, T, T, F, F, E, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, E, F, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1510 : le (tf [T, T, T, T, F, F, E, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, E, T, F, E, F, F] [([T, T, T, T, F, F, E, E, E, F, T, F, F], [T, T, T, T, F, F, E, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1509 trivial)

theorem z_1511 : le (tf [T, T, T, T, F, F, E, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, T, E, E, F, F, F] [([T, T, T, T, F, F, E, E, T, E, F, F, F], [T, T, T, T, F, F, E, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1510 trivial)

theorem z_1512 : le (tf [F, E, T, T, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, T, F, E, F, E, F, F] [([F, E, T, T, T, T, E, F, T, F, E, F, F], [F, E, T, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_754 trivial)

theorem z_1513 : le (tf [T, F, E, T, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, T, F, E, F, E, F, F] [([E, F, T, T, T, T, T, F, E, F, E, F, F], [F, E, T, T, T, T, T, F, E, F, E, F, F]), ([T, F, E, T, T, T, E, F, T, F, E, F, F], [T, F, E, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1512 (And.intro z_758 trivial))

theorem z_1514 : le (tf [T, T, F, E, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, T, F, E, F, E, F, F] [([T, E, F, T, T, T, T, F, E, F, E, F, F], [T, F, E, T, T, T, T, F, E, F, E, F, F]), ([T, T, F, E, T, T, E, F, T, F, E, F, F], [T, T, F, E, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1513 (And.intro z_762 trivial))

theorem z_1515 : le (tf [T, T, F, T, F, F, E, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, E, F, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1516 : le (tf [T, T, F, T, F, E, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, F, E, T, F, E, T, F] [([T, T, F, E, F, T, F, E, T, F, E, T, F], [T, T, F, F, E, T, F, E, T, F, E, T, F]), ([T, T, F, T, F, E, F, E, E, F, T, T, F], [T, T, F, T, F, F, E, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 (And.intro z_1515 trivial))

theorem z_1517 : le (tf [T, T, F, T, E, F, F, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, F, F, E, T, F, T, E, F] [([T, T, F, E, T, F, F, E, T, F, T, E, F], [T, T, F, F, T, E, F, E, T, F, T, E, F]), ([T, T, F, T, E, F, F, E, T, F, E, T, F], [T, T, F, T, F, E, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_579 (And.intro z_1516 trivial))

theorem z_1518 : le (tf [T, T, F, T, E, F, F, T, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, F, F, T, E, E, T, F, F] [([T, T, F, E, T, F, F, T, E, E, T, F, F], [T, T, F, F, T, E, F, T, E, E, T, F, F]), ([T, T, F, T, E, F, F, E, T, E, T, F, F], [T, T, F, T, E, F, F, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_739 (And.intro z_1517 trivial))

theorem z_1519 : le (tf [T, T, F, T, E, F, E, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, F, E, T, F, T, E, F, F] [([T, T, F, E, T, F, E, T, F, T, E, F, F], [T, T, F, F, T, E, E, T, F, T, E, F, F]), ([T, T, F, T, E, F, E, T, F, E, T, F, F], [T, T, F, T, E, F, F, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_740 (And.intro z_1518 trivial))

theorem z_1520 : le (tf [T, T, F, T, E, F, E, T, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, F, E, T, T, E, F, F, F] [([T, T, F, E, T, F, E, T, T, E, F, F, F], [T, T, F, E, T, F, E, T, T, F, E, F, F]), ([T, T, F, T, E, F, E, T, E, T, F, F, F], [T, T, F, T, E, F, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_725 (And.intro z_1519 trivial))

theorem z_1521 : le (tf [T, T, F, T, F, F, F, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, F, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1522 : le (tf [T, T, F, T, F, F, F, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, T, F, E, T] [([T, T, F, T, F, F, F, E, E, E, F, T, T], [T, T, F, T, F, F, F, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1521 trivial)

theorem z_1523 : le (tf [T, T, F, T, F, F, E, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, E, T, F, T, E] [([T, T, F, T, F, F, E, F, E, T, F, E, T], [T, T, F, T, F, F, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1522 trivial)

theorem z_1524 : le (tf [T, T, F, T, F, F, E, F, T, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, T, E, E, T, F] [([T, T, F, T, F, F, E, F, E, T, E, T, F], [T, T, F, T, F, F, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1523 trivial)

theorem z_1525 : le (tf [T, T, F, T, F, F, E, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, T, F, T, E, F] [([T, T, F, T, F, F, E, E, T, F, E, T, F], [T, T, F, T, F, F, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1524 trivial)

theorem z_1526 : le (tf [T, T, F, T, F, F, E, E, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, T, T, E, F, F] [([T, T, F, T, F, F, E, E, T, E, T, F, F], [T, T, F, T, F, F, E, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1525 trivial)

theorem z_1527 : le (tf [T, T, F, T, F, F, E, T, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, E, E, T, F, F] [([T, T, F, T, F, F, E, E, T, E, T, F, F], [T, T, F, T, F, F, E, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1525 trivial)

theorem z_1528 : le (tf [T, T, F, T, F, E, F, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, F, T, E, T, E, F, F] [([T, T, F, E, F, T, F, T, E, T, E, F, F], [T, T, F, F, E, T, F, T, E, T, E, F, F]), ([T, T, F, T, F, E, F, E, T, T, E, F, F], [T, T, F, T, F, F, E, E, T, T, E, F, F]), ([T, T, F, T, F, E, F, T, E, E, T, F, F], [T, T, F, T, F, F, E, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_734 (And.intro z_1526 (And.intro z_1527 trivial)))

theorem z_1529 : le (tf [T, T, F, T, F, E, E, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, E, F, T, F, T, E, F] [([T, T, F, E, F, T, E, F, T, F, T, E, F], [T, T, F, F, E, T, E, F, T, F, T, E, F]), ([T, T, F, T, F, E, E, F, T, F, E, T, F], [T, T, F, T, F, E, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_736 (And.intro z_1516 trivial))

theorem z_1530 : le (tf [T, T, F, T, F, E, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, T, F, E, E, T, F, F] [([T, T, F, E, F, T, T, F, E, E, T, F, F], [T, T, F, F, E, T, T, F, E, E, T, F, F]), ([T, T, F, T, F, E, E, F, T, E, T, F, F], [T, T, F, T, F, E, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_737 (And.intro z_1529 trivial))

theorem z_1531 : le (tf [T, T, F, T, F, E, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, T, E, F, T, E, F, F] [([T, T, F, E, F, T, T, E, F, T, E, F, F], [T, T, F, F, E, T, T, E, F, T, E, F, F]), ([T, T, F, T, F, E, E, T, F, T, E, F, F], [T, T, F, T, F, E, F, T, E, T, E, F, F]), ([T, T, F, T, F, E, T, E, F, E, T, F, F], [T, T, F, T, F, E, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_738 (And.intro z_1528 (And.intro z_1530 trivial)))

theorem z_1532 : le (tf [T, T, F, T, F, T, E, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, E, E, E, T, F, F, F] [([T, T, F, T, F, E, T, E, E, T, F, F, F], [T, T, F, T, F, E, T, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1531 trivial)

theorem z_1533 : le (tf [T, T, F, T, E, T, F, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, T, F, E, T, E, F, F, F] [([T, T, F, E, T, T, F, E, T, E, F, F, F], [T, T, F, E, T, T, F, E, T, F, E, F, F]), ([T, T, F, T, E, E, F, T, T, E, F, F, F], [T, T, F, T, E, F, E, T, T, E, F, F, F]), ([T, T, F, T, E, T, F, E, E, T, F, F, F], [T, T, F, T, F, T, E, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_762 (And.intro z_1520 (And.intro z_1532 trivial)))

theorem z_1534 : le (tf [T, T, F, T, E, T, T, F, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, T, T, F, E, E, F, F, F] [([T, T, F, E, T, T, T, F, E, E, F, F, F], [T, T, F, E, T, T, T, F, E, F, E, F, F]), ([T, T, F, T, E, T, E, F, T, E, F, F, F], [T, T, F, T, E, T, F, E, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1514 (And.intro z_1533 trivial))

theorem z_1535 : le (tf [F, E, T, T, T, T, E, F, T, E, F, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, E, F, T, E, F, F, F] [([F, E, T, T, T, E, T, F, T, E, F, F, F], [F, E, T, T, T, F, T, E, T, E, F, F, F]), ([F, E, T, T, T, T, E, F, E, T, F, F, F], [F, E, T, T, T, T, E, F, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_608 (And.intro z_770 trivial))

theorem z_1536 : le (tf [T, F, E, T, T, T, E, F, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, E, F, T, E, F, F, F] [([E, F, T, T, T, T, E, F, T, E, F, F, F], [F, E, T, T, T, T, E, F, T, E, F, F, F]), ([T, F, E, T, T, E, T, F, T, E, F, F, F], [T, F, E, T, T, F, T, E, T, E, F, F, F]), ([T, F, E, T, T, T, E, F, E, T, F, F, F], [T, F, E, T, T, T, E, F, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1535 (And.intro z_720 (And.intro z_771 trivial)))

theorem z_1537 : le (tf [T, T, F, E, T, T, E, F, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, T, T, E, F, T, E, F, F, F] [([T, E, F, T, T, T, E, F, T, E, F, F, F], [T, F, E, T, T, T, E, F, T, E, F, F, F]), ([T, T, F, E, T, E, T, F, T, E, F, F, F], [T, T, F, E, T, F, T, E, T, E, F, F, F]), ([T, T, F, E, T, T, E, F, E, T, F, F, F], [T, T, F, E, T, T, E, F, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1536 (And.intro z_742 (And.intro z_774 trivial)))

theorem z_1538 : le (tf [T, T, T, F, E, T, E, F, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, E, T, E, F, T, E, F, F, F] [([T, T, E, F, T, T, E, F, T, E, F, F, F], [T, T, F, E, T, T, E, F, T, E, F, F, F]), ([T, T, T, F, E, E, T, F, T, E, F, F, F], [T, T, T, F, E, F, T, E, T, E, F, F, F]), ([T, T, T, F, E, T, E, F, E, T, F, F, F], [T, T, T, F, E, T, E, F, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1537 (And.intro z_746 (And.intro z_778 trivial)))

theorem z_1539 : le (tf [T, T, T, E, F, T, T, F, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, E, F, T, T, F, E, E, F, F, F] [([T, T, E, T, F, T, T, F, E, E, F, F, F], [T, T, F, T, E, T, T, F, E, E, F, F, F]), ([T, T, T, E, F, T, E, F, T, E, F, F, F], [T, T, T, F, E, T, E, F, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1534 (And.intro z_1538 trivial))

theorem z_1540 : le (tf [T, T, F, T, F, T, E, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, E, E, F, E, T, F, F] [([T, T, F, T, F, E, T, E, F, E, T, F, F], [T, T, F, T, F, E, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1530 trivial)

theorem z_1541 : le (tf [T, T, F, T, E, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, T, F, E, F, T, E, F, F] [([T, T, F, E, T, T, F, E, F, T, E, F, F], [T, T, F, E, T, T, F, F, E, T, E, F, F]), ([T, T, F, T, E, E, F, T, F, T, E, F, F], [T, T, F, T, E, F, E, T, F, T, E, F, F]), ([T, T, F, T, E, T, F, E, F, E, T, F, F], [T, T, F, T, F, T, E, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_263 (And.intro z_1519 (And.intro z_1540 trivial)))

theorem z_1542 : le (tf [T, T, T, E, F, F, E, T, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, E, F, F, E, T, F, T, E, F, F] [([T, T, E, T, F, F, E, T, F, T, E, F, F], [T, T, F, T, E, F, E, T, F, T, E, F, F]), ([T, T, T, E, F, F, E, T, F, E, T, F, F], [T, T, T, F, E, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1519 (And.intro z_776 trivial))

theorem z_1543 : le (tf [T, T, T, E, F, T, F, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, E, F, T, F, E, F, T, E, F, F] [([T, T, E, T, F, T, F, E, F, T, E, F, F], [T, T, F, T, E, T, F, E, F, T, E, F, F]), ([T, T, T, E, F, E, F, T, F, T, E, F, F], [T, T, T, E, F, F, E, T, F, T, E, F, F]), ([T, T, T, E, F, T, F, E, F, E, T, F, F], [T, T, T, F, E, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1541 (And.intro z_1542 (And.intro z_777 trivial)))

theorem z_1544 : le (tf [T, T, T, T, F, E, F, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, E, F, E, E, T, F, F, F] [([T, T, T, E, F, T, F, E, E, T, F, F, F], [T, T, T, E, F, T, F, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1543 trivial)

theorem z_1545 : le (tf [T, T, T, T, F, E, E, F, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, E, E, F, T, E, F, F, F] [([T, T, T, E, F, T, E, F, T, E, F, F, F], [T, T, T, F, E, T, E, F, T, E, F, F, F]), ([T, T, T, T, F, E, E, F, E, T, F, F, F], [T, T, T, T, F, E, F, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1538 (And.intro z_1544 trivial))

theorem z_1546 : le (tf [E, T, T, F, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, T, F, F, E, E, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1547 : le (tf [E, T, T, F, F, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, T, T, T, F, F, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1548 : le (tf [E, T, T, F, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, E, T, T, F, F, E, F] [([E, T, T, F, E, F, T, T, T, F, F, E, F], [E, T, T, F, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1547 trivial)

theorem z_1549 : le (tf [E, T, T, F, T, T, F, E, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, F, E, T, F, F, E, F] [([E, T, T, F, T, E, F, T, T, F, F, E, F], [E, T, T, F, T, F, E, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1548 trivial)

theorem z_1550 : le (tf [E, T, T, F, T, F, T, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, F, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1551 : le (tf [E, T, T, F, T, F, T, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, F, E, T, F, E] [([E, T, T, F, T, F, T, F, F, E, E, F, T], [E, T, T, F, T, F, T, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1550 trivial)

theorem z_1552 : le (tf [E, T, T, F, T, F, T, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, F, T, E, E, F] [([E, T, T, F, T, F, T, F, F, E, T, E, F], [E, T, T, F, T, F, T, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1551 trivial)

theorem z_1553 : le (tf [E, T, T, F, T, F, T, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, T, E, F, E, F] [([E, T, T, F, T, F, T, F, E, T, F, E, F], [E, T, T, F, T, F, T, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1552 trivial)

theorem z_1554 : le (tf [T, F, T, E, F, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, F, E, T, T, T, F, F, E, F] [([T, F, E, T, F, E, T, T, T, F, F, E, F], [T, F, E, T, F, E, T, T, T, F, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_303 trivial)

theorem z_1555 : le (tf [T, F, T, E, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, E, T, T, F, F, E, F] [([T, F, E, T, T, F, E, T, T, F, F, E, F], [T, F, E, T, T, F, E, T, T, F, F, F, E]), ([T, F, T, E, E, F, T, T, T, F, F, E, F], [T, F, T, E, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_304 (And.intro z_1554 trivial))

theorem z_1556 : le (tf [T, E, T, F, T, F, T, E, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, F, T, E, T, F, F, E, F] [([E, T, T, F, T, F, T, E, T, F, F, E, F], [E, T, T, F, T, F, T, F, T, E, F, E, F]), ([T, E, T, F, T, F, E, T, T, F, F, E, F], [T, F, T, E, T, F, E, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1553 (And.intro z_1555 trivial))

theorem z_1557 : le (tf [T, E, T, F, T, T, E, F, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, T, E, F, T, F, F, E, F] [([E, T, T, F, T, T, E, F, T, F, F, E, F], [E, T, T, F, T, T, F, E, T, F, F, E, F]), ([T, E, T, F, T, E, T, F, T, F, F, E, F], [T, E, T, F, T, F, T, E, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1549 (And.intro z_1556 trivial))

theorem z_1558 : le (tf [T, E, T, F, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, F, T, T, T, F, E, F, E, F, F] [([E, T, T, F, T, T, T, F, E, F, E, F, F], [E, T, T, F, T, T, T, F, F, E, E, F, F]), ([T, E, T, F, T, T, E, F, T, F, E, F, F], [T, E, T, F, T, T, E, F, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1546 (And.intro z_1557 trivial))

theorem z_1559 : le (tf [T, T, E, F, T, T, T, F, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, F, T, T, T, F, E, E, F, F, F] [([T, E, T, F, T, T, T, F, E, E, F, F, F], [T, E, T, F, T, T, T, F, E, F, E, F, F]), ([T, T, E, F, T, T, E, F, T, E, F, F, F], [T, T, F, E, T, T, E, F, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1558 (And.intro z_1537 trivial))

theorem z_1560 : le (tf [F, T, E, T, T, T, T, F, F, F, E, F, E]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, T, F, F, F, E, F, E] [([F, E, T, T, T, T, T, F, F, F, E, F, E], [F, E, T, T, T, T, T, F, F, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_110 trivial)

theorem z_1561 : le (tf [T, E, F, T, T, T, T, F, F, F, E, F, E]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, T, F, F, F, E, F, E] [([E, T, F, T, T, T, T, F, F, F, E, F, E], [F, T, E, T, T, T, T, F, F, F, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1560 trivial)

theorem z_1562 : le (tf [F, E, T, T, T, T, T, F, F, F, E, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, T, F, F, F, E, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1563 : le (tf [F, T, E, T, T, T, T, F, F, F, E, E, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, T, F, F, F, E, E, F] [([F, E, T, T, T, T, T, F, F, F, E, E, F], [F, E, T, T, T, T, T, F, F, F, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1562 trivial)

theorem z_1564 : le (tf [T, E, F, T, T, T, T, F, F, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, T, F, F, F, E, E, F] [([E, T, F, T, T, T, T, F, F, F, E, E, F], [F, T, E, T, T, T, T, F, F, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1563 trivial)

theorem z_1565 : le (tf [F, T, E, T, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, T, F, F, E, F, E, F] [([F, E, T, T, T, T, T, F, F, E, F, E, F], [F, E, T, T, T, T, T, F, F, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_120 trivial)

theorem z_1566 : le (tf [T, E, F, T, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, T, F, F, E, F, E, F] [([E, T, F, T, T, T, T, F, F, E, F, E, F], [F, T, E, T, T, T, T, F, F, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1565 trivial)

theorem z_1567 : le (tf [F, T, E, T, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [F, T, E, T, T, T, T, F, F, E, E, F, F] [([F, E, T, T, T, T, T, F, F, E, E, F, F], [F, E, T, T, T, T, T, F, F, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_124 trivial)

theorem z_1568 : le (tf [T, E, F, T, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, T, F, F, E, E, F, F] [([E, T, F, T, T, T, T, F, F, E, E, F, F], [F, T, E, T, T, T, T, F, F, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1567 trivial)

theorem z_1569 : le (tf [E, T, F, T, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, T, F, F, E, E, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1570 : le (tf [F, T, E, E, F, T, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, T, T, F, F, E, F] [([F, E, T, E, F, T, T, T, T, F, F, E, F], [F, E, T, F, E, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 trivial)

theorem z_1571 : le (tf [E, T, F, T, F, E, T, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, T, T, F, F, E, F] [([E, T, F, E, F, T, T, T, T, F, F, E, F], [F, T, E, E, F, T, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1570 trivial)

theorem z_1572 : le (tf [E, T, F, T, T, F, E, T, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, T, T, F, F, E, F] [([E, T, F, T, E, F, T, T, T, F, F, E, F], [E, T, F, T, F, E, T, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1571 trivial)

theorem z_1573 : le (tf [E, T, F, T, T, T, F, E, T, F, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, E, T, F, F, E, F] [([E, T, F, T, T, E, F, T, T, F, F, E, F], [E, T, F, T, T, F, E, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1572 trivial)

theorem z_1574 : le (tf [F, T, E, T, T, F, T, F, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, T, T, F, T, F, F, E, E, F, T] [([F, E, T, T, T, F, T, F, F, E, E, F, T], [F, E, T, T, T, F, T, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_148 trivial)

theorem z_1575 : le (tf [E, T, F, T, T, F, T, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, F, F, E, T, F, E] [([E, T, F, T, T, F, T, F, F, E, E, F, T], [F, T, E, T, T, F, T, F, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1574 trivial)

theorem z_1576 : le (tf [E, T, F, T, T, F, T, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, F, F, T, E, E, F] [([E, T, F, T, T, F, T, F, F, E, T, E, F], [E, T, F, T, T, F, T, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1575 trivial)

theorem z_1577 : le (tf [E, T, F, T, T, F, T, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, F, T, E, F, E, F] [([E, T, F, T, T, F, T, F, E, T, F, E, F], [E, T, F, T, T, F, T, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1576 trivial)

theorem z_1578 : le (tf [T, E, F, T, T, F, T, E, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, F, T, E, T, F, F, E, F] [([E, T, F, T, T, F, T, E, T, F, F, E, F], [E, T, F, T, T, F, T, F, T, E, F, E, F]), ([T, E, F, T, T, F, E, T, T, F, F, E, F], [T, F, E, T, T, F, E, T, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1577 (And.intro z_188 trivial))

theorem z_1579 : le (tf [T, E, F, T, T, T, E, F, T, F, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, E, F, T, F, F, E, F] [([E, T, F, T, T, T, E, F, T, F, F, E, F], [E, T, F, T, T, T, F, E, T, F, F, E, F]), ([T, E, F, T, T, E, T, F, T, F, F, E, F], [T, E, F, T, T, F, T, E, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1573 (And.intro z_1578 trivial))

theorem z_1580 : le (tf [T, E, F, T, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, T, F, E, F, E, F, F] [([E, T, F, T, T, T, T, F, E, F, E, F, F], [E, T, F, T, T, T, T, F, F, E, E, F, F]), ([T, E, F, T, T, T, E, F, T, F, E, F, F], [T, E, F, T, T, T, E, F, T, F, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1569 (And.intro z_1579 trivial))

theorem z_1581 : le (tf [F, T, E, F, E, E, F, T, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, F, T, T, T, T, F, F] [([F, E, T, F, E, E, F, T, T, T, T, F, F], [F, E, T, F, E, F, E, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_387 trivial)

theorem z_1582 : le (tf [F, T, E, E, F, T, F, E, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, F, E, T, T, T, F, F] [([F, E, T, E, F, T, F, E, T, T, T, F, F], [F, E, T, F, E, T, F, E, T, T, T, F, F]), ([F, T, E, E, F, E, F, T, T, T, T, F, F], [F, T, E, F, E, E, F, T, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_388 (And.intro z_1581 trivial))

theorem z_1583 : le (tf [F, T, E, E, F, T, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, F, E, T, T, F, F] [([F, E, T, E, F, T, T, F, E, T, T, F, F], [F, E, T, F, E, T, T, F, E, T, T, F, F]), ([F, T, E, E, F, T, E, F, T, T, T, F, F], [F, T, E, E, F, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_389 (And.intro z_1582 trivial))

theorem z_1584 : le (tf [F, T, E, E, F, T, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, T, F, E, T, F, F] [([F, E, T, E, F, T, T, T, F, E, T, F, F], [F, E, T, E, F, T, T, T, F, F, T, E, F]), ([F, T, E, E, F, T, T, E, F, T, T, F, F], [F, T, E, E, F, T, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_370 (And.intro z_1583 trivial))

theorem z_1585 : le (tf [F, T, E, E, F, T, T, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, T, T, F, E, F, F] [([F, E, T, E, F, T, T, T, T, F, E, F, F], [F, E, T, E, F, T, T, T, T, F, F, E, F]), ([F, T, E, E, F, T, T, T, E, F, T, F, F], [F, T, E, E, F, T, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 (And.intro z_1584 trivial))

theorem z_1586 : le (tf [F, T, E, T, F, E, E, F, T, T, T, F, F]) zero :=
  le_zero_of_pairs [F, T, E, T, F, E, E, F, T, T, T, F, F] [([F, E, T, T, F, E, E, F, T, T, T, F, F], [F, E, T, T, F, E, F, E, T, T, T, F, F]), ([F, T, E, E, F, T, E, F, T, T, T, F, F], [F, T, E, E, F, T, F, E, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_390 (And.intro z_1582 trivial))

theorem z_1587 : le (tf [E, T, F, T, F, E, T, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, F, E, T, T, F, F] [([E, T, F, E, F, T, T, F, E, T, T, F, F], [F, T, E, E, F, T, T, F, E, T, T, F, F]), ([E, T, F, T, F, E, E, F, T, T, T, F, F], [F, T, E, T, F, E, E, F, T, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1583 (And.intro z_1586 trivial))

theorem z_1588 : le (tf [E, T, F, T, F, E, T, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, T, F, E, T, F, F] [([E, T, F, E, F, T, T, T, F, E, T, F, F], [F, T, E, E, F, T, T, T, F, E, T, F, F]), ([E, T, F, T, F, E, T, E, F, T, T, F, F], [E, T, F, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1584 (And.intro z_1587 trivial))

theorem z_1589 : le (tf [E, T, F, T, F, E, T, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, T, T, F, E, F, F] [([E, T, F, E, F, T, T, T, T, F, E, F, F], [F, T, E, E, F, T, T, T, T, F, E, F, F]), ([E, T, F, T, F, E, T, T, E, F, T, F, F], [E, T, F, T, F, E, T, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1585 (And.intro z_1588 trivial))

theorem z_1590 : le (tf [E, T, F, T, T, F, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, F, E, T, T, F, F] [([E, T, F, T, E, F, T, F, E, T, T, F, F], [E, T, F, T, F, E, T, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1587 trivial)

theorem z_1591 : le (tf [E, T, F, T, T, F, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, T, F, E, T, F, F] [([E, T, F, T, E, F, T, T, F, E, T, F, F], [E, T, F, T, F, E, T, T, F, E, T, F, F]), ([E, T, F, T, T, F, E, E, F, T, T, F, F], [E, T, F, T, T, F, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1588 (And.intro z_1590 trivial))

theorem z_1592 : le (tf [E, T, F, T, T, F, E, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, T, T, F, E, F, F] [([E, T, F, T, E, F, T, T, T, F, E, F, F], [E, T, F, T, F, E, T, T, T, F, E, F, F]), ([E, T, F, T, T, F, E, T, E, F, T, F, F], [E, T, F, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1589 (And.intro z_1591 trivial))

theorem z_1593 : le (tf [E, T, F, T, T, T, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, E, F, E, T, F, F] [([E, T, F, T, T, E, F, T, F, E, T, F, F], [E, T, F, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1591 trivial)

theorem z_1594 : le (tf [E, T, F, T, T, T, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, F, E, T, F, E, F, F] [([E, T, F, T, T, E, F, T, T, F, E, F, F], [E, T, F, T, T, F, E, T, T, F, E, F, F]), ([E, T, F, T, T, T, F, E, E, F, T, F, F], [E, T, F, T, T, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1592 (And.intro z_1593 trivial))

theorem z_1595 : le (tf [E, T, F, T, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, T, T, F, E, F, E, F, F] [([E, T, F, T, T, T, E, F, T, F, E, F, F], [E, T, F, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1594 trivial)

theorem z_1596 : le (tf [T, E, F, T, T, T, T, F, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, T, F, E, E, F, F, F] [([E, T, F, T, T, T, T, F, E, E, F, F, F], [E, T, F, T, T, T, T, F, E, F, E, F, F]), ([T, E, F, T, T, T, E, F, T, E, F, F, F], [T, F, E, T, T, T, E, F, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1595 (And.intro z_1536 trivial))

theorem z_1597 : le (tf [E, F, T, T, T, T, T, F, F, F, E, F, E]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, F, F, F, E, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1598 : le (tf [E, F, T, T, T, T, T, F, F, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, F, F, F, E, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1599 : le (tf [E, F, T, T, T, T, T, F, F, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, F, F, E, F, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1600 : le (tf [E, F, T, T, T, T, T, F, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, F, F, E, E, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1601 : le (tf [E, F, T, T, T, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, F, E, F, E, F, F] [([E, F, T, T, T, T, E, F, T, F, E, F, F], [E, F, T, T, T, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_297 trivial)

theorem z_1602 : le (tf [E, F, T, T, T, T, T, F, E, E, F, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, F, E, E, F, F, F] [([E, F, T, T, T, T, E, F, T, E, F, F, F], [F, E, T, T, T, T, E, F, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1535 trivial)

theorem z_1603 : le (tf [E, F, T, T, T, T, T, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [E, F, T, T, T, T, T, E, F, E, F, F, F] [([E, F, T, T, T, T, E, T, F, E, F, F, F], [E, F, T, T, T, T, F, T, E, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1002 trivial)

theorem z_1604 : le (tf [T, T, T, T, F, F, F, T, F, F, E, E, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, T, F, F, E, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1605 : le (tf [T, T, T, T, F, F, F, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1606 : le (tf [T, T, T, T, F, F, F, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, E, F, T, E] [([T, T, T, T, F, F, F, F, E, E, F, E, T], [T, T, T, T, F, F, F, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1605 trivial)

theorem z_1607 : le (tf [T, T, T, T, F, F, F, E, F, T, F, E, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, F, T, F, E, E] [([T, T, T, T, F, F, F, E, F, E, F, T, E], [T, T, T, T, F, F, F, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1606 trivial)

theorem z_1608 : le (tf [T, T, T, T, F, F, F, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1609 : le (tf [T, T, T, T, F, F, F, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, E, T, F, E] [([T, T, T, T, F, F, F, F, E, E, E, F, T], [T, T, T, T, F, F, F, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1608 trivial)

theorem z_1610 : le (tf [T, T, T, T, F, F, F, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, F, T, E, F, E] [([T, T, T, T, F, F, F, E, F, E, T, F, E], [T, T, T, T, F, F, F, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1609 trivial)

theorem z_1611 : le (tf [T, T, T, T, F, F, F, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, E, T, E, F] [([T, T, T, T, F, F, F, F, E, E, E, T, F], [T, T, T, T, F, F, F, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1606 trivial)

theorem z_1612 : le (tf [T, T, T, T, F, F, F, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, F, T, E, E, F] [([T, T, T, T, F, F, F, E, F, E, T, E, F], [T, T, T, T, F, F, F, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1611 trivial)

theorem z_1613 : le (tf [T, T, T, T, F, F, F, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1614 : le (tf [T, T, T, T, F, F, F, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, F, E, T, E, F] [([T, T, T, T, F, F, F, E, F, E, E, T, F], [T, T, T, T, F, F, F, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1613 trivial)

theorem z_1615 : le (tf [T, T, T, T, F, F, F, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, T, F, E, E, F] [([T, T, T, T, F, F, F, E, E, F, T, E, F], [T, T, T, T, F, F, F, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1614 trivial)

theorem z_1616 : le (tf [T, T, T, T, F, F, F, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, T, E, F, E, F] [([T, T, T, T, F, F, F, E, E, T, F, E, F], [T, T, T, T, F, F, F, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1612 trivial)

theorem z_1617 : le (tf [T, T, T, T, F, F, F, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, T, E, E, F, F] [([T, T, T, T, F, F, F, E, E, T, E, F, F], [T, T, T, T, F, F, F, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1501 trivial)

theorem z_1618 : le (tf [T, T, T, T, F, F, E, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, F, E, E, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1619 : le (tf [T, T, T, T, F, F, E, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, E, F, T, E, F, F] [([T, T, T, T, F, F, E, E, F, E, T, F, F], [T, T, T, T, F, F, E, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1618 trivial)

theorem z_1620 : le (tf [T, T, T, T, F, F, E, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, E, T, E, F, F, F] [([T, T, T, T, F, F, E, E, E, T, F, F, F], [T, T, T, T, F, F, E, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1619 trivial)

theorem z_1621 : le (tf [T, T, T, T, F, F, F, F, F, E, E, E, T]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1622 : le (tf [T, T, T, T, F, F, F, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, F, E, T, E] [([T, T, T, T, F, F, F, F, E, F, E, E, T], [T, T, T, T, F, F, F, F, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1621 trivial)

theorem z_1623 : le (tf [T, T, T, T, F, F, F, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, T, F, E, E] [([T, T, T, T, F, F, F, F, E, E, F, T, E], [T, T, T, T, F, F, F, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1622 trivial)

theorem z_1624 : le (tf [T, T, T, T, F, F, F, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, T, E, E, F, E] [([T, T, T, T, F, F, F, F, E, T, E, F, E], [T, T, T, T, F, F, F, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1623 trivial)

theorem z_1625 : le (tf [T, T, T, T, F, F, F, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, F, E, T, E, E, F] [([T, T, T, T, F, F, F, F, E, E, T, E, F], [T, T, T, T, F, F, F, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1609 trivial)

theorem z_1626 : le (tf [T, T, T, T, F, F, E, E, E, F, T, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, E, E, F, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1627 : le (tf [T, T, T, T, F, F, E, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, E, E, E, T, F, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1628 : le (tf [E, T, T, T, F, F, E, F, E, T, T, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, F, E, F, E, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1629 : le (tf [E, T, T, T, F, F, E, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, F, E, T, F, E, T, F, F] [([E, T, T, T, F, F, E, E, F, T, T, F, F], [E, T, T, T, F, F, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1628 trivial)

theorem z_1630 : le (tf [E, T, T, T, F, F, E, T, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, F, E, T, T, F, E, F, F] [([E, T, T, T, F, F, E, T, E, F, T, F, F], [E, T, T, T, F, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1629 trivial)

theorem z_1631 : le (tf [E, T, T, T, F, T, F, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, E, F, E, T, F, F] [([E, T, T, T, F, E, F, T, F, E, T, F, F], [E, T, T, T, F, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1629 trivial)

theorem z_1632 : le (tf [E, T, T, T, F, T, F, E, T, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, E, T, F, E, F, F] [([E, T, T, T, F, E, F, T, T, F, E, F, F], [E, T, T, T, F, F, E, T, T, F, E, F, F]), ([E, T, T, T, F, T, F, E, E, F, T, F, F], [E, T, T, T, F, T, F, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1630 (And.intro z_1631 trivial))

theorem z_1633 : le (tf [E, T, T, T, F, T, T, F, E, F, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, T, F, E, F, E, F, F] [([E, T, T, T, F, T, E, F, T, F, E, F, F], [E, T, T, T, F, T, F, E, T, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1632 trivial)

theorem z_1634 : le (tf [E, T, T, T, F, T, F, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1635 : le (tf [E, T, T, T, F, T, F, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, E, F, T, E, F] [([E, T, T, T, F, T, F, F, E, F, E, T, F], [E, T, T, T, F, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1634 trivial)

theorem z_1636 : le (tf [E, T, T, T, F, T, F, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, E, T, E, F, F] [([E, T, T, T, F, T, F, F, E, E, T, F, F], [E, T, T, T, F, T, F, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1635 trivial)

theorem z_1637 : le (tf [E, T, T, T, F, T, F, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, T, F, E, E, F, F] [([E, T, T, T, F, T, F, E, F, T, E, F, F], [E, T, T, T, F, T, F, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1636 trivial)

theorem z_1638 : le (tf [E, T, T, T, F, T, F, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, F, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1639 : le (tf [E, T, T, T, F, T, F, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, F, E, T, F, E] [([E, T, T, T, F, T, F, F, F, E, E, F, T], [E, T, T, T, F, T, F, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1638 trivial)

theorem z_1640 : le (tf [E, T, T, T, F, T, F, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, F, T, E, E, F] [([E, T, T, T, F, T, F, F, F, E, T, E, F], [E, T, T, T, F, T, F, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1639 trivial)

theorem z_1641 : le (tf [E, T, T, T, F, T, F, F, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, T, F, T, F, F, T, E, F, E, F] [([E, T, T, T, F, T, F, F, E, T, F, E, F], [E, T, T, T, F, T, F, F, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1640 trivial)

theorem z_1642 : le (tf [T, E, T, T, F, T, F, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, T, T, F, T, F, F, E, F, E, T, F] [([E, T, T, T, F, T, F, F, E, F, E, T, F], [E, T, T, T, F, T, F, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1634 trivial)

theorem z_1643 : le (tf [T, E, T, T, F, T, F, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, T, F, T, F, F, E, T, F, E, F] [([E, T, T, T, F, T, F, F, E, T, F, E, F], [E, T, T, T, F, T, F, F, F, T, E, E, F]), ([T, E, T, T, F, T, F, F, E, E, F, T, F], [T, E, T, T, F, T, F, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1640 (And.intro z_1642 trivial))

theorem z_1644 : le (tf [T, E, T, T, F, T, F, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, F, T, F, F, T, E, E, F, F] [([E, T, T, T, F, T, F, F, T, E, E, F, F], [E, T, T, T, F, T, F, F, T, E, F, E, F]), ([T, E, T, T, F, T, F, F, E, T, E, F, F], [T, E, T, T, F, T, F, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1641 (And.intro z_1643 trivial))

theorem z_1645 : le (tf [T, E, T, T, F, T, F, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, F, T, F, T, E, F, E, F, F] [([E, T, T, T, F, T, F, T, E, F, E, F, F], [E, T, T, T, F, T, F, T, F, E, E, F, F]), ([T, E, T, T, F, T, F, E, T, F, E, F, F], [T, E, T, T, F, T, F, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1637 (And.intro z_1644 trivial))

theorem z_1646 : le (tf [T, E, T, T, F, T, T, E, F, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, F, T, T, E, F, F, E, F, F] [([E, T, T, T, F, T, T, E, F, F, E, F, F], [E, T, T, T, F, T, T, F, E, F, E, F, F]), ([T, E, T, T, F, T, E, T, F, F, E, F, F], [T, E, T, T, F, T, F, T, E, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1633 (And.intro z_1645 trivial))

theorem z_1647 : le (tf [T, T, E, T, F, T, F, T, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, F, T, F, T, E, E, F, F, F] [([T, E, T, T, F, T, F, T, E, E, F, F, F], [T, E, T, T, F, T, F, T, E, F, E, F, F]), ([T, T, E, T, F, T, F, E, T, E, F, F, F], [T, T, F, T, E, T, F, E, T, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1645 (And.intro z_1533 trivial))

theorem z_1648 : le (tf [T, T, E, T, F, T, T, E, F, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, F, T, T, E, F, E, F, F, F] [([T, E, T, T, F, T, T, E, F, E, F, F, F], [T, E, T, T, F, T, T, E, F, F, E, F, F]), ([T, T, E, T, F, T, E, T, F, E, F, F, F], [T, T, E, T, F, T, F, T, E, E, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1646 (And.intro z_1647 trivial))

theorem z_1649 : le (tf [T, T, T, E, F, F, E, T, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, E, F, F, E, T, T, E, F, F, F] [([T, T, E, T, F, F, E, T, T, E, F, F, F], [T, T, F, T, E, F, E, T, T, E, F, F, F]), ([T, T, T, E, F, F, E, T, E, T, F, F, F], [T, T, T, E, F, F, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1520 (And.intro z_1542 trivial))

theorem z_1650 : le (tf [T, T, T, E, F, T, F, E, T, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, E, F, T, F, E, T, E, F, F, F] [([T, T, E, T, F, T, F, E, T, E, F, F, F], [T, T, F, T, E, T, F, E, T, E, F, F, F]), ([T, T, T, E, F, E, F, T, T, E, F, F, F], [T, T, T, E, F, F, E, T, T, E, F, F, F]), ([T, T, T, E, F, T, F, E, E, T, F, F, F], [T, T, T, E, F, T, F, E, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1533 (And.intro z_1649 (And.intro z_1543 trivial)))

theorem z_1651 : le (tf [T, T, F, T, E, F, T, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, F, T, E, E, T, F, F, F] [([T, T, F, E, T, F, T, E, E, T, F, F, F], [T, T, F, F, T, E, T, E, E, T, F, F, F]), ([T, T, F, T, E, F, E, T, E, T, F, F, F], [T, T, F, T, E, F, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_741 (And.intro z_1519 trivial))

theorem z_1652 : le (tf [T, T, F, T, E, T, E, F, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, T, E, F, E, T, F, F, F] [([T, T, F, E, T, T, E, F, E, T, F, F, F], [T, T, F, E, T, T, E, F, F, T, E, F, F]), ([T, T, F, T, E, E, T, F, E, T, F, F, F], [T, T, F, T, E, F, T, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_774 (And.intro z_1651 trivial))

theorem z_1653 : le (tf [T, T, T, E, F, F, T, E, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, E, F, F, T, E, E, T, F, F, F] [([T, T, E, T, F, F, T, E, E, T, F, F, F], [T, T, F, T, E, F, T, E, E, T, F, F, F]), ([T, T, T, E, F, F, E, T, E, T, F, F, F], [T, T, T, E, F, F, E, T, F, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1651 (And.intro z_1542 trivial))

theorem z_1654 : le (tf [T, T, T, E, F, T, E, F, E, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, E, F, T, E, F, E, T, F, F, F] [([T, T, E, T, F, T, E, F, E, T, F, F, F], [T, T, F, T, E, T, E, F, E, T, F, F, F]), ([T, T, T, E, F, E, T, F, E, T, F, F, F], [T, T, T, E, F, F, T, E, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1652 (And.intro z_1653 trivial))

theorem z_1655 : le (tf [T, T, T, T, F, E, E, E, F, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, E, E, E, F, T, F, F, F] [([T, T, T, E, F, T, E, E, F, T, F, F, F], [T, T, T, E, F, T, E, F, E, T, F, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1654 trivial)

theorem z_1656 : le (tf [T, T, T, T, F, F, F, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, T, T, F, F, F, E, E, E, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1657 : le (tf [E, T, T, F, F, E, T, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, T, T, F, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1658 : le (tf [E, T, T, F, T, F, E, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, E, T, F, T, F, F, E] [([E, T, T, F, E, F, T, T, F, T, F, F, E], [E, T, T, F, F, E, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1657 trivial)

theorem z_1659 : le (tf [E, T, T, F, T, F, F, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, F, F, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1660 : le (tf [E, T, T, F, T, F, F, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, F, E, F, T, E, T, F] [([E, T, T, F, T, F, F, E, F, E, T, T, F], [E, T, T, F, T, F, F, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1659 trivial)

theorem z_1661 : le (tf [E, T, T, F, T, F, F, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, F, E, T, E, F, T, F] [([E, T, T, F, T, F, F, E, E, T, F, T, F], [E, T, T, F, T, F, F, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1660 trivial)

theorem z_1662 : le (tf [E, T, T, F, T, F, T, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, F, E, E, F, T, F] [([E, T, T, F, T, F, E, F, T, E, F, T, F], [E, T, T, F, T, F, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1661 trivial)

theorem z_1663 : le (tf [E, T, T, F, T, F, T, E, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, T, E, F, T, F, E, F] [([E, T, T, F, T, F, E, T, F, T, F, E, F], [E, T, T, F, T, F, E, T, F, T, F, F, E]), ([E, T, T, F, T, F, T, E, F, E, F, T, F], [E, T, T, F, T, F, T, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1658 (And.intro z_1662 trivial))

theorem z_1664 : le (tf [E, T, T, F, F, E, F, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, F, E, T, T, F, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1665 : le (tf [E, T, T, F, F, E, T, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, T, F, E, T, F, T, F] [([E, T, T, F, F, E, E, F, T, T, F, T, F], [E, T, T, F, F, E, F, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1664 trivial)

theorem z_1666 : le (tf [E, T, T, F, F, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, T, T, F, E, F, T, F] [([E, T, T, F, F, E, T, E, F, T, F, T, F], [E, T, T, F, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1665 trivial)

theorem z_1667 : le (tf [E, T, T, F, T, F, E, F, E, T, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, E, F, E, T, F, T, F] [([E, T, T, F, E, F, T, F, E, T, F, T, F], [E, T, T, F, F, E, T, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1665 trivial)

theorem z_1668 : le (tf [E, T, T, F, T, F, E, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, F, E, T, F, E, F, T, F] [([E, T, T, F, E, F, T, T, F, E, F, T, F], [E, T, T, F, F, E, T, T, F, E, F, T, F]), ([E, T, T, F, T, F, E, E, F, T, F, T, F], [E, T, T, F, T, F, E, F, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1666 (And.intro z_1667 trivial))

theorem z_1669 : le (tf [E, T, T, F, T, T, F, E, F, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, F, E, F, E, F, T, F] [([E, T, T, F, T, E, F, T, F, E, F, T, F], [E, T, T, F, T, F, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1668 trivial)

theorem z_1670 : le (tf [E, T, T, F, T, T, E, F, F, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, T, E, F, F, T, F, E, F] [([E, T, T, F, T, E, T, F, F, T, F, E, F], [E, T, T, F, T, F, T, E, F, T, F, E, F]), ([E, T, T, F, T, T, E, F, F, E, F, T, F], [E, T, T, F, T, T, F, E, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1663 (And.intro z_1669 trivial))

theorem z_1671 : le (tf [F, E, F, E, T, T, T, F, T, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, T, T, T, F, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1672 : le (tf [F, E, T, F, E, T, T, F, T, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, T, T, F, T, T, F, F, E] [([F, E, E, F, T, T, T, F, T, T, F, F, E], [F, E, F, E, T, T, T, F, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1671 trivial)

theorem z_1673 : le (tf [F, E, T, T, F, E, T, F, T, T, F, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, E, T, F, T, T, F, F, E] [([F, E, T, E, F, T, T, F, T, T, F, F, E], [F, E, T, F, E, T, T, F, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1672 trivial)

theorem z_1674 : le (tf [T, F, E, F, E, T, T, F, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, F, E, T, T, F, T, T, F, F, E] [([E, F, T, F, E, T, T, F, T, T, F, F, E], [F, E, T, F, E, T, T, F, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1672 trivial)

theorem z_1675 : le (tf [T, F, E, T, F, E, T, F, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, E, T, F, T, T, F, F, E] [([E, F, T, T, F, E, T, F, T, T, F, F, E], [F, E, T, T, F, E, T, F, T, T, F, F, E]), ([T, F, E, E, F, T, T, F, T, T, F, F, E], [T, F, E, F, E, T, T, F, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1673 (And.intro z_1674 trivial))

theorem z_1676 : le (tf [T, F, T, E, E, F, T, F, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, F, T, E, E, F, T, F, T, T, F, F, E] [([T, F, E, T, E, F, T, F, T, T, F, F, E], [T, F, E, T, F, E, T, F, T, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1675 trivial)

theorem z_1677 : le (tf [F, F, E, F, E, T, T, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, F, E, T, T, F] [([F, F, E, F, E, T, T, E, F, T, T, T, F], [F, F, E, F, E, T, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1439 trivial)

theorem z_1678 : le (tf [F, F, E, F, E, T, T, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, T, T, T, F, E, T, F] [([F, F, E, F, E, T, T, T, E, F, T, T, F], [F, F, E, F, E, T, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1677 trivial)

theorem z_1679 : le (tf [F, F, E, T, F, E, T, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, F, E, T, T, F] [([F, F, E, E, F, T, T, T, F, E, T, T, F], [F, F, E, F, E, T, T, T, F, E, T, T, F]), ([F, F, E, T, F, E, T, E, F, T, T, T, F], [F, F, E, T, F, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1677 (And.intro z_1443 trivial))

theorem z_1680 : le (tf [F, F, E, T, F, E, T, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, T, T, T, F, E, T, F] [([F, F, E, E, F, T, T, T, T, F, E, T, F], [F, F, E, F, E, T, T, T, T, F, E, T, F]), ([F, F, E, T, F, E, T, T, E, F, T, T, F], [F, F, E, T, F, E, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1678 (And.intro z_1679 trivial))

theorem z_1681 : le (tf [F, F, T, E, F, E, E, F, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, T, E, F, E, E, F, T, T, T, T, F] [([F, F, E, T, F, E, E, F, T, T, T, T, F], [F, F, E, T, F, E, F, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1442 trivial)

theorem z_1682 : le (tf [F, F, T, E, E, F, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, F, E, T, T, T, F] [([F, F, E, T, E, F, T, F, E, T, T, T, F], [F, F, E, T, F, E, T, F, E, T, T, T, F]), ([F, F, T, E, E, F, E, F, T, T, T, T, F], [F, F, T, E, F, E, E, F, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1443 (And.intro z_1681 trivial))

theorem z_1683 : le (tf [F, F, T, E, E, F, T, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, T, F, E, T, T, F] [([F, F, E, T, E, F, T, T, F, E, T, T, F], [F, F, E, T, F, E, T, T, F, E, T, T, F]), ([F, F, T, E, E, F, T, E, F, T, T, T, F], [F, F, T, E, E, F, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1679 (And.intro z_1682 trivial))

theorem z_1684 : le (tf [F, F, T, E, E, F, T, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, F, T, E, E, F, T, T, T, F, E, T, F] [([F, F, E, T, E, F, T, T, T, F, E, T, F], [F, F, E, T, F, E, T, T, T, F, E, T, F]), ([F, F, T, E, E, F, T, T, E, F, T, T, F], [F, F, T, E, E, F, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1680 (And.intro z_1683 trivial))

theorem z_1685 : le (tf [F, F, E, T, T, F, E, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, T, F, E, F, E, T, T, T, F] [([F, F, E, T, E, F, T, F, E, T, T, T, F], [F, F, E, T, F, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1443 trivial)

theorem z_1686 : le (tf [F, F, T, E, T, F, E, E, F, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, T, E, T, F, E, E, F, T, T, T, F] [([F, F, E, T, T, F, E, E, F, T, T, T, F], [F, F, E, T, T, F, E, F, E, T, T, T, F]), ([F, F, T, E, E, F, T, E, F, T, T, T, F], [F, F, T, E, E, F, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1685 (And.intro z_1682 trivial))

theorem z_1687 : le (tf [F, E, T, F, T, F, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, T, F, E, T, T, F] [([F, E, T, F, E, F, T, T, F, E, T, T, F], [F, F, T, E, E, F, T, T, F, E, T, T, F]), ([F, E, T, F, T, F, E, E, F, T, T, T, F], [F, F, T, E, T, F, E, E, F, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1683 (And.intro z_1686 trivial))

theorem z_1688 : le (tf [F, E, T, F, T, F, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, F, E, T, T, F, E, T, F] [([F, E, T, F, E, F, T, T, T, F, E, T, F], [F, F, T, E, E, F, T, T, T, F, E, T, F]), ([F, E, T, F, T, F, E, T, E, F, T, T, F], [F, E, T, F, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1684 (And.intro z_1687 trivial))

theorem z_1689 : le (tf [F, E, T, F, T, T, F, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, T, F, E, F, E, T, T, F] [([F, E, T, F, T, E, F, T, F, E, T, T, F], [F, E, T, F, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1687 trivial)

theorem z_1690 : le (tf [F, E, T, F, T, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, T, F, E, T, F, E, T, F] [([F, E, T, F, T, E, F, T, T, F, E, T, F], [F, E, T, F, T, F, E, T, T, F, E, T, F]), ([F, E, T, F, T, T, F, E, E, F, T, T, F], [F, E, T, F, T, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1688 (And.intro z_1689 trivial))

theorem z_1691 : le (tf [T, F, F, F, E, E, T, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, T, T, F, E, T, F] [([T, F, F, F, E, E, T, T, E, F, T, T, F], [T, F, F, F, E, E, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1217 trivial)

theorem z_1692 : le (tf [T, F, F, E, F, T, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, F, T, E, T, T, F, E, T, F] [([T, F, F, E, F, E, T, T, T, F, E, T, F], [T, F, F, F, E, E, T, T, T, F, E, T, F]), ([T, F, F, E, F, T, E, T, E, F, T, T, F], [T, F, F, E, F, T, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1691 (And.intro z_1219 trivial))

theorem z_1693 : le (tf [T, F, F, E, T, E, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, E, F, T, T, F, E, T, F] [([T, F, F, E, E, T, F, T, T, F, E, T, F], [T, F, F, E, F, T, E, T, T, F, E, T, F]), ([T, F, F, E, T, E, F, T, E, F, T, T, F], [T, F, F, E, T, F, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1692 (And.intro z_1470 trivial))

theorem z_1694 : le (tf [T, F, F, E, T, T, F, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, F, E, E, F, T, T, F] [([T, F, F, E, T, E, F, T, E, F, T, T, F], [T, F, F, E, T, F, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1470 trivial)

theorem z_1695 : le (tf [T, F, E, F, T, T, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, T, F, E, T, F, E, T, F] [([E, F, T, F, T, T, F, E, T, F, E, T, F], [F, E, T, F, T, T, F, E, T, F, E, T, F]), ([T, F, E, F, T, E, F, T, T, F, E, T, F], [T, F, F, E, T, E, F, T, T, F, E, T, F]), ([T, F, E, F, T, T, F, E, E, F, T, T, F], [T, F, F, E, T, T, F, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1690 (And.intro z_1693 (And.intro z_1694 trivial)))

theorem z_1696 : le (tf [T, F, T, F, F, E, E, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, E, T, F, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1697 : le (tf [T, F, T, F, E, F, E, T, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, F, E, T, E, F, T, T, F] [([T, F, E, F, T, F, E, T, E, F, T, T, F], [T, F, F, E, T, F, E, T, E, F, T, T, F]), ([T, F, T, F, E, F, E, E, T, F, T, T, F], [T, F, T, F, F, E, E, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1470 (And.intro z_1696 trivial))

theorem z_1698 : le (tf [T, F, T, F, E, E, F, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, E, F, T, T, F, E, T, F] [([T, F, E, F, T, E, F, T, T, F, E, T, F], [T, F, F, E, T, E, F, T, T, F, E, T, F]), ([T, F, T, F, E, E, F, T, E, F, T, T, F], [T, F, T, F, E, F, E, T, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1693 (And.intro z_1697 trivial))

theorem z_1699 : le (tf [T, F, T, F, F, F, E, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, E, F, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1700 : le (tf [T, F, T, F, F, F, E, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, E, T, F, E, T, T] [([T, F, T, F, F, F, E, E, E, F, T, T, T], [T, F, T, F, F, F, E, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1699 trivial)

theorem z_1701 : le (tf [T, F, T, F, F, F, E, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, E, T, T, F, E, T] [([T, F, T, F, F, F, E, E, T, E, F, T, T], [T, F, T, F, F, F, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1700 trivial)

theorem z_1702 : le (tf [T, F, T, F, F, F, E, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, T, E, E, F, T, T] [([T, F, T, F, F, F, E, E, T, E, F, T, T], [T, F, T, F, F, F, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1700 trivial)

theorem z_1703 : le (tf [T, F, T, F, F, E, F, T, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, F, T, E, T, F, E, T] [([T, F, T, F, F, E, F, E, T, T, F, E, T], [T, F, T, F, F, F, E, E, T, T, F, E, T]), ([T, F, T, F, F, E, F, T, E, E, F, T, T], [T, F, T, F, F, F, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1701 (And.intro z_1702 trivial))

theorem z_1704 : le (tf [T, F, T, F, F, E, E, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, T, F, T, F, T, E] [([T, F, T, F, F, E, E, T, F, T, F, E, T], [T, F, T, F, F, E, F, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1703 trivial)

theorem z_1705 : le (tf [T, F, T, F, F, F, E, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, E, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1706 : le (tf [T, F, T, F, F, E, F, E, T, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, F, E, T, E, T, T, F] [([T, F, T, F, F, E, F, E, E, T, T, T, F], [T, F, T, F, F, F, E, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1705 trivial)

theorem z_1707 : le (tf [T, F, T, F, F, E, T, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, T, F, E, E, T, T, F] [([T, F, T, F, F, E, E, F, T, E, T, T, F], [T, F, T, F, F, E, F, E, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1706 trivial)

theorem z_1708 : le (tf [T, F, T, F, F, E, T, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, T, E, F, T, E, T, F] [([T, F, T, F, F, E, E, T, F, T, E, T, F], [T, F, T, F, F, E, E, T, F, T, F, T, E]), ([T, F, T, F, F, E, T, E, F, E, T, T, F], [T, F, T, F, F, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1704 (And.intro z_1707 trivial))

theorem z_1709 : le (tf [T, F, T, F, F, T, E, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, T, E, E, E, T, F, T, F] [([T, F, T, F, F, E, T, E, E, T, F, T, F], [T, F, T, F, F, E, T, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1708 trivial)

theorem z_1710 : le (tf [T, F, T, F, E, T, F, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, F, E, T, E, F, T, F] [([T, F, E, F, T, T, F, E, T, E, F, T, F], [T, F, E, F, T, T, F, E, T, F, E, T, F]), ([T, F, T, F, E, E, F, T, T, E, F, T, F], [T, F, T, F, E, E, F, T, T, F, E, T, F]), ([T, F, T, F, E, T, F, E, E, T, F, T, F], [T, F, T, F, F, T, E, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1695 (And.intro z_1698 (And.intro z_1709 trivial)))

theorem z_1711 : le (tf [T, F, T, F, T, E, F, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, F, E, E, T, F, T, F] [([T, F, T, F, E, T, F, E, E, T, F, T, F], [T, F, T, F, F, T, E, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1709 trivial)

theorem z_1712 : le (tf [T, F, T, F, T, E, E, F, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, E, F, T, E, F, T, F] [([T, F, T, F, E, T, E, F, T, E, F, T, F], [T, F, T, F, E, T, F, E, T, E, F, T, F]), ([T, F, T, F, T, E, E, F, E, T, F, T, F], [T, F, T, F, T, E, F, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1710 (And.intro z_1711 trivial))

theorem z_1713 : le (tf [T, F, T, E, T, F, E, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, E, F, T, T, F, E, F] [([T, F, E, T, T, F, E, F, T, T, F, E, F], [T, F, E, T, T, F, F, E, T, T, F, E, F]), ([T, F, T, E, E, F, T, F, T, T, F, E, F], [T, F, T, E, E, F, T, F, T, T, F, F, E]), ([T, F, T, E, T, F, E, F, T, E, F, T, F], [T, F, T, F, T, E, E, F, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_553 (And.intro z_1676 (And.intro z_1712 trivial)))

theorem z_1714 : le (tf [T, F, T, E, T, F, T, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, T, F, E, E, F, T, F] [([T, F, E, T, T, F, T, F, E, E, F, T, F], [T, F, E, T, T, F, T, F, E, F, E, T, F]), ([T, F, T, E, T, F, E, F, T, E, F, T, F], [T, F, T, F, T, E, E, F, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_554 (And.intro z_1712 trivial))

theorem z_1715 : le (tf [F, E, T, T, T, F, T, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, F, E, E, F, T, F] [([F, E, T, T, T, F, E, F, T, E, F, T, F], [F, E, T, T, T, F, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_792 trivial)

theorem z_1716 : le (tf [F, E, T, T, T, F, T, E, F, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, E, F, T, F, E, F] [([F, E, T, T, T, F, E, T, F, T, F, E, F], [F, E, T, T, T, F, E, T, F, T, F, F, E]), ([F, E, T, T, T, F, T, E, F, E, F, T, F], [F, E, T, T, T, F, T, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1008 (And.intro z_1715 trivial))

theorem z_1717 : le (tf [T, F, E, T, T, F, T, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, F, E, E, F, T, F] [([E, F, T, T, T, F, T, F, E, E, F, T, F], [F, E, T, T, T, F, T, F, E, E, F, T, F]), ([T, F, E, T, T, F, E, F, T, E, F, T, F], [T, F, E, T, T, F, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1715 (And.intro z_820 trivial))

theorem z_1718 : le (tf [T, F, E, T, T, F, T, E, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, E, F, T, F, E, F] [([E, F, T, T, T, F, T, E, F, T, F, E, F], [F, E, T, T, T, F, T, E, F, T, F, E, F]), ([T, F, E, T, T, F, E, T, F, T, F, E, F], [T, F, E, T, T, F, E, T, F, T, F, F, E]), ([T, F, E, T, T, F, T, E, F, E, F, T, F], [T, F, E, T, T, F, T, F, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1716 (And.intro z_1009 (And.intro z_1717 trivial)))

theorem z_1719 : le (tf [T, F, T, E, T, F, T, E, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, E, T, F, T, E, F, E, F, T, F] [([T, F, E, T, T, F, T, E, F, E, F, T, F], [T, F, E, T, T, F, T, F, E, E, F, T, F]), ([T, F, T, E, T, F, E, T, F, E, F, T, F], [T, F, T, F, T, E, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1717 (And.intro z_1065 trivial))

theorem z_1720 : le (tf [T, F, T, F, E, F, E, E, T, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, F, E, E, T, T, F, T, F] [([T, F, E, F, T, F, E, E, T, T, F, T, F], [T, F, F, E, T, F, E, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1223 trivial)

theorem z_1721 : le (tf [T, F, T, F, E, E, F, T, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, E, F, T, E, T, F, T, F] [([T, F, E, F, T, E, F, T, E, T, F, T, F], [T, F, F, E, T, E, F, T, E, T, F, T, F]), ([T, F, T, F, E, E, F, E, T, T, F, T, F], [T, F, T, F, E, F, E, E, T, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1224 (And.intro z_1720 trivial))

theorem z_1722 : le (tf [T, F, T, F, E, E, T, E, F, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, E, T, E, F, T, F, T, F] [([T, F, E, F, T, E, T, E, F, T, F, T, F], [T, F, F, E, T, E, T, E, F, T, F, T, F]), ([T, F, T, F, E, E, E, T, F, T, F, T, F], [T, F, T, F, E, E, F, T, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1225 (And.intro z_1721 trivial))

theorem z_1723 : le (tf [T, F, T, E, F, E, T, T, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, E, F, E, T, T, F, E, F, T, F] [([T, F, E, T, F, E, T, T, F, E, F, T, F], [T, F, E, T, F, E, T, T, F, F, E, T, F]), ([T, F, T, E, F, E, T, E, F, T, F, T, F], [T, F, T, F, E, E, T, E, F, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_375 (And.intro z_1722 trivial))

theorem z_1724 : le (tf [T, F, T, E, E, F, T, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, T, E, E, F, T, T, F, T, F, E, F] [([T, F, E, T, E, F, T, T, F, T, F, E, F], [T, F, E, T, F, E, T, T, F, T, F, E, F]), ([T, F, T, E, E, F, T, T, F, E, F, T, F], [T, F, T, E, F, E, T, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_906 (And.intro z_1723 trivial))

theorem z_1725 : le (tf [F, E, T, F, T, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, T, F, T, E, E, F, T, F] [([F, E, T, F, T, T, F, E, T, E, F, T, F], [F, E, T, F, T, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1690 trivial)

theorem z_1726 : le (tf [T, F, E, F, T, T, F, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, T, F, T, E, E, F, T, F] [([E, F, T, F, T, T, F, T, E, E, F, T, F], [F, E, T, F, T, T, F, T, E, E, F, T, F]), ([T, F, E, F, T, T, F, E, T, E, F, T, F], [T, F, E, F, T, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1725 (And.intro z_1695 trivial))

theorem z_1727 : le (tf [T, F, T, F, T, F, E, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, F, E, F, E, E, T, T, F] [([T, F, T, F, E, F, T, F, E, E, T, T, F], [T, F, T, F, F, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1707 trivial)

theorem z_1728 : le (tf [T, F, T, F, T, F, E, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, F, E, E, F, T, E, T, F] [([T, F, T, F, E, F, T, E, F, T, E, T, F], [T, F, T, F, F, E, T, E, F, T, E, T, F]), ([T, F, T, F, T, F, E, E, F, E, T, T, F], [T, F, T, F, T, F, E, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1708 (And.intro z_1727 trivial))

theorem z_1729 : le (tf [T, F, T, F, F, F, E, F, E, E, T, T, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, F, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1730 : le (tf [T, F, T, F, F, F, E, E, F, T, E, T, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, E, F, T, E, T, T] [([T, F, T, F, F, F, E, E, F, E, T, T, T], [T, F, T, F, F, F, E, F, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1729 trivial)

theorem z_1731 : le (tf [T, F, T, F, F, F, E, E, T, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, F, E, E, T, E, F, T, T] [([T, F, T, F, F, F, E, E, E, T, F, T, T], [T, F, T, F, F, F, E, E, F, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1730 trivial)

theorem z_1732 : le (tf [T, F, T, F, F, E, F, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, F, T, E, E, F, T, T] [([T, F, T, F, F, E, F, E, T, E, F, T, T], [T, F, T, F, F, F, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1731 trivial)

theorem z_1733 : le (tf [T, F, T, F, F, E, E, T, F, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, T, F, T, F, E, T] [([T, F, T, F, F, E, E, T, F, E, F, T, T], [T, F, T, F, F, E, F, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1732 trivial)

theorem z_1734 : le (tf [T, F, T, F, T, F, F, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, F, F, E, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1735 : le (tf [T, F, T, F, F, E, E, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, F, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1736 : le (tf [T, F, T, F, F, E, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, F, E, E, T, F, E, T, T, F] [([T, F, T, F, F, E, E, E, F, T, T, T, F], [T, F, T, F, F, E, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1735 trivial)

theorem z_1737 : le (tf [F, F, E, F, T, E, E, F, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, T, E, E, F, T, T, T, T, F] [([F, F, E, F, E, T, E, F, T, T, T, T, F], [F, F, F, E, E, T, E, F, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1438 trivial)

theorem z_1738 : le (tf [F, F, E, E, T, F, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, F, E, T, T, T, F] [([F, F, E, E, T, F, E, F, T, T, T, T, F], [F, F, E, F, T, E, E, F, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1737 trivial)

theorem z_1739 : le (tf [F, F, E, E, T, F, T, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, T, F, E, T, T, F] [([F, F, E, E, T, F, T, E, F, T, T, T, F], [F, F, E, E, T, F, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1738 trivial)

theorem z_1740 : le (tf [F, E, F, E, T, F, T, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, T, F, T, T, F, T, E, T, F] [([F, E, F, E, T, F, T, T, F, E, T, T, F], [F, F, E, E, T, F, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1739 trivial)

theorem z_1741 : le (tf [F, E, T, F, E, F, T, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, E, F, T, T, F, T, E, T, F] [([F, E, E, F, T, F, T, T, F, T, E, T, F], [F, E, F, E, T, F, T, T, F, T, E, T, F]), ([F, E, T, F, E, F, T, T, F, E, T, T, F], [F, F, T, E, E, F, T, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1740 (And.intro z_1683 trivial))

theorem z_1742 : le (tf [E, F, T, F, T, F, E, T, F, T, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, F, E, T, F, T, E, T, F] [([E, F, T, F, E, F, T, T, F, T, E, T, F], [F, E, T, F, E, F, T, T, F, T, E, T, F]), ([E, F, T, F, T, F, E, T, F, E, T, T, F], [F, E, T, F, T, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1741 (And.intro z_1687 trivial))

theorem z_1743 : le (tf [E, F, T, F, T, T, F, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, F, T, T, F, E, F, T, E, T, F] [([E, F, T, F, T, E, F, T, F, T, E, T, F], [E, F, T, F, T, F, E, T, F, T, E, T, F]), ([E, F, T, F, T, T, F, E, F, E, T, T, F], [F, E, T, F, T, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1742 (And.intro z_1689 trivial))

theorem z_1744 : le (tf [T, F, E, F, T, T, F, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, T, F, E, E, T, F, T, F] [([E, F, T, F, T, T, F, E, E, T, F, T, F], [E, F, T, F, T, T, F, E, F, T, E, T, F]), ([T, F, E, F, T, E, F, T, E, T, F, T, F], [T, F, F, E, T, E, F, T, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1743 (And.intro z_1224 trivial))

theorem z_1745 : le (tf [T, F, F, E, T, T, T, F, F, F, E, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, T, F, F, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1746 : le (tf [T, F, F, E, T, T, T, F, F, E, F, T, E]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, T, F, F, E, F, T, E] [([T, F, F, E, T, T, T, F, F, E, F, E, T], [T, F, F, E, T, T, T, F, F, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1745 trivial)

theorem z_1747 : le (tf [T, F, T, F, E, T, T, F, F, F, E, E, T]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, T, F, F, F, E, E, T] [([T, F, E, F, T, T, T, F, F, F, E, E, T], [T, F, F, E, T, T, T, F, F, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1745 trivial)

theorem z_1748 : le (tf [T, F, T, F, E, T, T, F, F, E, F, T, E]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, T, F, F, E, F, T, E] [([T, F, E, F, T, T, T, F, F, E, F, T, E], [T, F, F, E, T, T, T, F, F, E, F, T, E]), ([T, F, T, F, E, T, T, F, F, E, F, E, T], [T, F, T, F, E, T, T, F, F, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1746 (And.intro z_1747 trivial))

theorem z_1749 : le (tf [T, F, T, F, T, E, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, T, E, T, F, F, E, E, T, F] [([T, F, T, F, E, T, T, F, F, E, E, T, F], [T, F, T, F, E, T, T, F, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1748 trivial)

theorem z_1750 : le (tf [T, F, F, E, T, T, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, T, F, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1751 : le (tf [T, F, T, F, E, T, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, T, F, F, E, E, T, F] [([T, F, E, F, T, T, T, F, F, E, E, T, F], [T, F, F, E, T, T, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1750 trivial)

theorem z_1752 : le (tf [F, E, T, F, T, T, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, F, T, T, T, F, E, F, E, T, F] [([F, E, T, F, T, T, E, F, T, F, E, T, F], [F, E, T, F, T, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1690 trivial)

theorem z_1753 : le (tf [T, F, E, F, T, T, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, F, T, T, T, F, E, F, E, T, F] [([E, F, T, F, T, T, T, F, E, F, E, T, F], [F, E, T, F, T, T, T, F, E, F, E, T, F]), ([T, F, E, F, T, T, E, F, T, F, E, T, F], [T, F, E, F, T, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1752 (And.intro z_1695 trivial))

theorem z_1754 : le (tf [T, F, T, F, E, T, T, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, T, F, E, E, F, T, F] [([T, F, E, F, T, T, T, F, E, E, F, T, F], [T, F, E, F, T, T, T, F, E, F, E, T, F]), ([T, F, T, F, E, T, E, F, T, E, F, T, F], [T, F, T, F, E, T, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1753 (And.intro z_1710 trivial))

theorem z_1755 : le (tf [T, F, F, E, T, T, T, E, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, F, E, T, T, T, E, F, E, F, T, F] [([T, F, F, E, T, T, E, T, F, E, F, T, F], [T, F, F, E, T, T, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1011 trivial)

theorem z_1756 : le (tf [T, F, T, F, E, T, T, E, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, T, F, E, T, T, E, F, E, F, T, F] [([T, F, E, F, T, T, T, E, F, E, F, T, F], [T, F, F, E, T, T, T, E, F, E, F, T, F]), ([T, F, T, F, E, T, E, T, F, E, F, T, F], [T, F, T, F, E, T, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1755 (And.intro z_1012 trivial))

theorem z_1757 : le (tf [F, E, T, T, T, F, T, E, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, F, T, E, F, E, F, T, F] [([F, E, T, T, T, F, E, T, F, E, F, T, F], [F, E, T, T, T, F, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_901 trivial)

theorem z_1758 : le (tf [T, F, E, T, T, F, T, E, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, F, T, E, F, E, F, T, F] [([E, F, T, T, T, F, T, E, F, E, F, T, F], [F, E, T, T, T, F, T, E, F, E, F, T, F]), ([T, F, E, T, T, F, E, T, F, E, F, T, F], [T, F, E, T, T, F, F, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1757 (And.intro z_907 trivial))

theorem z_1759 : le (tf [F, E, T, T, T, T, E, F, F, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, T, T, T, E, F, F, E, F, T, F] [([F, E, T, T, T, E, T, F, F, E, F, T, F], [F, E, T, T, T, F, T, E, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1757 trivial)

theorem z_1760 : le (tf [T, F, E, T, T, T, E, F, F, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, T, T, T, E, F, F, E, F, T, F] [([E, F, T, T, T, T, E, F, F, E, F, T, F], [F, E, T, T, T, T, E, F, F, E, F, T, F]), ([T, F, E, T, T, E, T, F, F, E, F, T, F], [T, F, E, T, T, F, T, E, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1759 (And.intro z_1758 trivial))

theorem z_1761 : le (tf [T, T, F, F, T, F, T, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, T, E, E, F, E, T, F] [([T, T, F, F, T, F, E, T, E, F, E, T, F], [T, T, F, F, T, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_591 trivial)

theorem z_1762 : le (tf [T, T, F, F, T, F, T, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, T, E, E, T, F, E, F] [([T, T, F, F, T, F, E, T, E, T, F, E, F], [T, T, F, F, T, F, E, T, F, T, E, E, F]), ([T, T, F, F, T, F, T, E, E, E, F, T, F], [T, T, F, F, T, F, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1238 (And.intro z_1761 trivial))

theorem z_1763 : le (tf [T, T, F, F, E, T, E, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, F, T, T, F, E, F] [([T, T, F, F, E, E, T, F, T, T, F, E, F], [T, T, F, F, E, F, T, E, T, T, F, E, F]), ([T, T, F, F, E, T, E, F, T, E, F, T, F], [T, T, F, F, E, T, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1253 (And.intro z_847 trivial))

theorem z_1764 : le (tf [T, T, F, F, E, T, E, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, F, T, F, T, F, E] [([T, T, F, F, E, E, T, F, T, F, T, F, E], [T, T, F, F, E, F, T, E, T, F, T, F, E]), ([T, T, F, F, E, T, E, F, T, F, E, F, T], [T, T, F, F, E, T, F, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1256 (And.intro z_861 trivial))

theorem z_1765 : le (tf [T, T, F, F, E, T, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1766 : le (tf [T, T, F, F, E, T, T, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, E, F, T, E, F] [([T, T, F, F, E, T, E, F, T, F, T, E, F], [T, T, F, F, E, T, E, F, T, F, T, F, E]), ([T, T, F, F, E, T, T, F, E, F, E, T, F], [T, T, F, F, E, T, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1764 (And.intro z_1765 trivial))

theorem z_1767 : le (tf [T, T, F, F, E, T, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, E, T, E, F, F] [([T, T, F, F, E, T, E, F, T, T, E, F, F], [T, T, F, F, E, T, E, F, T, T, F, E, F]), ([T, T, F, F, E, T, T, F, E, E, T, F, F], [T, T, F, F, E, T, T, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1763 (And.intro z_1766 trivial))

theorem z_1768 : le (tf [T, T, F, F, E, F, T, E, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, F, T, E, T, T, E, F, F] [([T, T, F, F, E, F, E, T, T, T, E, F, F], [T, T, F, F, E, F, E, T, T, T, F, E, F]), ([T, T, F, F, E, F, T, E, T, E, T, F, F], [T, T, F, F, E, F, T, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_558 (And.intro z_735 trivial))

theorem z_1769 : le (tf [T, T, F, F, T, F, T, E, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, T, E, F, E, E, F, T] [([T, T, F, F, T, F, E, T, F, E, E, F, T], [T, T, F, F, T, F, E, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1236 trivial)

theorem z_1770 : le (tf [T, T, F, F, T, F, T, E, E, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, T, E, E, F, T, F, E] [([T, T, F, F, T, F, E, T, E, F, T, F, E], [T, T, F, F, T, F, E, T, F, E, T, F, E]), ([T, T, F, F, T, F, T, E, E, F, E, F, T], [T, T, F, F, T, F, T, E, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1237 (And.intro z_1769 trivial))

theorem z_1771 : le (tf [T, T, F, F, T, F, T, E, E, F, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, T, F, T, E, E, F, E, F, T] [([T, T, F, F, T, F, E, T, E, F, E, F, T], [T, T, F, F, T, F, E, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1245 trivial)

theorem z_1772 : le (tf [F, F, F, E, E, F, E, T, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, F, E, T, T, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1773 : le (tf [F, F, F, E, E, T, F, E, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, F, E, T, T, T, T, F] [([F, F, F, E, E, E, F, T, T, T, T, T, F], [F, F, F, E, E, F, E, T, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1772 trivial)

theorem z_1774 : le (tf [F, F, F, E, E, T, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, T, T, F, E, T, T, T, F] [([F, F, F, E, E, T, E, F, T, T, T, T, F], [F, F, F, E, E, T, F, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1773 trivial)

theorem z_1775 : le (tf [F, F, F, E, T, E, E, F, T, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, T, E, E, F, T, T, T, T, F] [([F, F, F, E, E, T, E, F, T, T, T, T, F], [F, F, F, E, E, T, F, E, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1773 trivial)

theorem z_1776 : le (tf [F, F, E, F, T, E, T, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, T, E, T, F, E, T, T, T, F] [([F, F, E, F, E, T, T, F, E, T, T, T, F], [F, F, F, E, E, T, T, F, E, T, T, T, F]), ([F, F, E, F, T, E, E, F, T, T, T, T, F], [F, F, F, E, T, E, E, F, T, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1774 (And.intro z_1775 trivial))

theorem z_1777 : le (tf [F, F, E, E, T, F, T, F, T, E, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, T, F, T, F, T, E, T, T, F] [([F, F, E, E, T, F, T, F, E, T, T, T, F], [F, F, E, F, T, E, T, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1776 trivial)

theorem z_1778 : le (tf [F, F, F, E, E, E, T, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, T, T, T, F, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1779 : le (tf [F, F, E, F, E, T, E, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, F, E, T, E, T, T, F, T, T, F] [([F, F, E, F, E, E, T, T, T, F, T, T, F], [F, F, F, E, E, E, T, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1778 trivial)

theorem z_1780 : le (tf [F, F, E, T, F, E, E, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, F, E, E, T, T, F, T, T, F] [([F, F, E, E, F, T, E, T, T, F, T, T, F], [F, F, E, F, E, T, E, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1779 trivial)

theorem z_1781 : le (tf [F, F, E, T, E, F, T, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, E, F, T, E, T, F, T, T, F] [([F, F, E, E, T, F, T, E, T, F, T, T, F], [F, F, E, E, T, F, T, F, T, E, T, T, F]), ([F, F, E, T, E, F, E, T, T, F, T, T, F], [F, F, E, T, F, E, E, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1777 (And.intro z_1780 trivial))

theorem z_1782 : le (tf [F, F, E, T, E, T, E, F, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, T, E, T, E, F, T, F, T, T, F] [([F, F, E, E, T, T, E, F, T, F, T, T, F], [F, F, E, E, T, T, F, E, T, F, T, T, F]), ([F, F, E, T, E, E, T, F, T, F, T, T, F], [F, F, E, T, E, F, T, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_328 (And.intro z_1781 trivial))

theorem z_1783 : le (tf [F, T, F, E, F, E, E, T, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, T, F, E, F, E, E, T, T, F, T, T, F] [([F, E, F, T, F, E, E, T, T, F, T, T, F], [F, F, E, T, F, E, E, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1780 trivial)

theorem z_1784 : le (tf [F, T, F, E, E, F, T, E, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, T, F, E, E, F, T, E, T, F, T, T, F] [([F, E, F, T, E, F, T, E, T, F, T, T, F], [F, F, E, T, E, F, T, E, T, F, T, T, F]), ([F, T, F, E, E, F, E, T, T, F, T, T, F], [F, T, F, E, F, E, E, T, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1781 (And.intro z_1783 trivial))

theorem z_1785 : le (tf [F, T, F, E, E, T, E, F, T, F, T, T, F]) zero :=
  le_zero_of_pairs [F, T, F, E, E, T, E, F, T, F, T, T, F] [([F, E, F, T, E, T, E, F, T, F, T, T, F], [F, F, E, T, E, T, E, F, T, F, T, T, F]), ([F, T, F, E, E, E, T, F, T, F, T, T, F], [F, T, F, E, E, F, T, E, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1782 (And.intro z_1784 trivial))

theorem z_1786 : le (tf [F, T, E, F, E, T, T, F, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, T, E, F, E, T, T, F, E, F, T, T, F] [([F, E, T, F, E, T, T, F, E, F, T, T, F], [F, E, T, F, E, T, T, F, F, E, T, T, F]), ([F, T, E, F, E, T, E, F, T, F, T, T, F], [F, T, F, E, E, T, E, F, T, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_333 (And.intro z_1785 trivial))

theorem z_1787 : le (tf [F, T, E, E, F, T, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, F, T, F, E, T, F] [([F, E, T, E, F, T, T, F, T, F, E, T, F], [F, E, T, F, E, T, T, F, T, F, E, T, F]), ([F, T, E, E, F, T, T, F, E, F, T, T, F], [F, T, E, F, E, T, T, F, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 (And.intro z_1786 trivial))

theorem z_1788 : le (tf [F, T, E, E, F, T, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, T, E, E, F, T, T, F, T, T, F, E, F] [([F, E, T, E, F, T, T, F, T, T, F, E, F], [F, E, T, F, E, T, T, F, T, T, F, E, F]), ([F, T, E, E, F, T, T, F, T, E, F, T, F], [F, T, E, E, F, T, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_786 (And.intro z_1787 trivial))

theorem z_1789 : le (tf [E, T, F, T, F, F, T, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, F, T, E, E, F, T, T, F] [([E, T, F, T, F, F, E, T, E, F, T, T, F], [E, T, F, T, F, F, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1304 trivial)

theorem z_1790 : le (tf [E, T, F, T, F, E, T, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, F, T, F, E, T, F] [([E, T, F, E, F, T, T, F, T, F, E, T, F], [F, T, E, E, F, T, T, F, T, F, E, T, F]), ([E, T, F, T, F, E, T, F, E, F, T, T, F], [E, T, F, T, F, F, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1787 (And.intro z_1789 trivial))

theorem z_1791 : le (tf [E, T, F, T, F, E, T, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, F, E, T, F, T, T, F, E, F] [([E, T, F, E, F, T, T, F, T, T, F, E, F], [F, T, E, E, F, T, T, F, T, T, F, E, F]), ([E, T, F, T, F, E, T, F, T, E, F, T, F], [E, T, F, T, F, E, T, F, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1788 (And.intro z_1790 trivial))

theorem z_1792 : le (tf [E, T, F, T, T, F, E, F, T, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, F, T, T, F, E, F] [([E, T, F, T, E, F, T, F, T, T, F, E, F], [E, T, F, T, F, E, T, F, T, T, F, E, F]), ([E, T, F, T, T, F, E, F, T, E, F, T, F], [E, T, F, T, T, F, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1791 (And.intro z_1333 trivial))

theorem z_1793 : le (tf [E, T, F, T, T, F, E, F, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, F, T, F, T, F, E] [([E, T, F, T, E, F, T, F, T, F, T, F, E], [E, T, F, T, F, E, T, F, T, F, T, F, E]), ([E, T, F, T, T, F, E, F, T, F, E, F, T], [E, T, F, T, T, F, F, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1162 (And.intro z_1336 trivial))

theorem z_1794 : le (tf [E, T, F, T, T, F, T, F, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, F, F, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1795 : le (tf [E, T, F, T, T, F, T, F, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, F, E, F, T, E, F] [([E, T, F, T, T, F, E, F, T, F, T, E, F], [E, T, F, T, T, F, E, F, T, F, T, F, E]), ([E, T, F, T, T, F, T, F, E, F, E, T, F], [E, T, F, T, T, F, T, F, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1793 (And.intro z_1794 trivial))

theorem z_1796 : le (tf [E, T, F, T, T, F, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, F, E, T, E, F, F] [([E, T, F, T, T, F, E, F, T, T, E, F, F], [E, T, F, T, T, F, E, F, T, T, F, E, F]), ([E, T, F, T, T, F, T, F, E, E, T, F, F], [E, T, F, T, T, F, T, F, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1792 (And.intro z_1795 trivial))

theorem z_1797 : le (tf [E, T, F, T, T, F, E, T, F, T, F, F, E]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, E, T, F, T, F, F, E] [([E, T, F, T, E, F, T, T, F, T, F, F, E], [E, T, F, T, F, E, T, T, F, T, F, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1302 trivial)

theorem z_1798 : le (tf [T, E, F, T, T, F, E, T, F, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, F, E, T, F, T, F, E, F] [([E, T, F, T, T, F, E, T, F, T, F, E, F], [E, T, F, T, T, F, E, T, F, T, F, F, E]), ([T, E, F, T, E, F, T, T, F, T, F, E, F], [T, F, E, T, E, F, T, T, F, T, F, E, F]), ([T, E, F, T, T, F, E, T, F, E, F, T, F], [T, F, E, T, T, F, E, T, F, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1797 (And.intro z_1087 (And.intro z_976 trivial)))

theorem z_1799 : le (tf [T, E, F, T, T, F, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, F, T, F, E, E, T, F, F] [([E, T, F, T, T, F, T, F, E, E, T, F, F], [E, T, F, T, T, F, T, F, E, F, T, E, F]), ([T, E, F, T, T, F, E, F, T, E, T, F, F], [T, F, E, T, T, F, E, F, T, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1795 (And.intro z_1122 trivial))

theorem z_1800 : le (tf [T, E, F, T, T, F, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, F, T, E, F, T, E, F, F] [([E, T, F, T, T, F, T, E, F, T, E, F, F], [E, T, F, T, T, F, T, F, E, T, E, F, F]), ([T, E, F, T, T, F, E, T, F, T, E, F, F], [T, E, F, T, T, F, E, T, F, T, F, E, F]), ([T, E, F, T, T, F, T, E, F, E, T, F, F], [T, E, F, T, T, F, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1796 (And.intro z_1798 (And.intro z_1799 trivial)))

theorem z_1801 : le (tf [T, T, F, F, T, E, F, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, F, E, E, F, T, T, F] [([T, T, F, F, E, T, F, E, E, F, T, T, F], [T, T, F, F, E, T, F, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_561 trivial)

theorem z_1802 : le (tf [T, T, F, F, T, E, E, F, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, T, E, E, F, T, F, E, T, F] [([T, T, F, F, E, T, E, F, T, F, E, T, F], [T, T, F, F, E, T, F, E, T, F, E, T, F]), ([T, T, F, F, T, E, E, F, E, F, T, T, F], [T, T, F, F, T, E, F, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 (And.intro z_1801 trivial))

theorem z_1803 : le (tf [T, T, F, F, E, T, T, F, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, F, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1804 : le (tf [T, T, F, F, E, T, T, F, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, F, E, T, F, E] [([T, T, F, F, E, T, T, F, F, E, E, F, T], [T, T, F, F, E, T, T, F, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1803 trivial)

theorem z_1805 : le (tf [T, T, F, F, E, T, T, F, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, F, E, E, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1806 : le (tf [T, T, F, F, E, E, T, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, E, T, F, T, F, T, E, F] [([T, T, F, F, E, E, T, F, T, F, E, T, F], [T, T, F, F, E, F, T, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_505 trivial)

theorem z_1807 : le (tf [T, T, F, F, E, T, E, F, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, F, T, E, T, F, F] [([T, T, F, F, E, E, T, F, T, E, T, F, F], [T, T, F, F, E, E, T, F, T, F, T, E, F]), ([T, T, F, F, E, T, E, F, E, T, T, F, F], [T, T, F, F, E, T, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1806 (And.intro z_1168 trivial))

theorem z_1808 : le (tf [E, T, F, T, T, F, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, F, E, F, E, T, F] [([E, T, F, T, T, F, E, F, T, F, E, T, F], [E, T, F, T, T, F, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1187 trivial)

theorem z_1809 : le (tf [E, T, F, T, T, F, T, E, F, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, T, F, T, E, F, F, T, E, F] [([E, T, F, T, T, F, E, T, F, F, T, E, F], [E, T, F, T, T, F, F, T, E, F, T, E, F]), ([E, T, F, T, T, F, T, E, F, F, E, T, F], [E, T, F, T, T, F, T, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1197 (And.intro z_1808 trivial))

theorem z_1810 : le (tf [T, E, F, T, T, F, T, E, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, F, T, E, F, E, T, F, F] [([E, T, F, T, T, F, T, E, F, E, T, F, F], [E, T, F, T, T, F, T, E, F, F, T, E, F]), ([T, E, F, T, T, F, E, T, F, E, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1809 (And.intro z_611 trivial))

theorem z_1811 : le (tf [T, E, F, T, T, T, E, F, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, E, F, T, T, T, E, F, F, E, T, F, F] [([E, T, F, T, T, T, E, F, F, E, T, F, F], [E, T, F, T, T, T, F, E, F, E, T, F, F]), ([T, E, F, T, T, E, T, F, F, E, T, F, F], [T, E, F, T, T, F, T, E, F, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1593 (And.intro z_1810 trivial))

theorem z_1812 : le (tf [T, T, T, F, F, F, T, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, F, T, E, E, E, F, T, F] [([T, T, T, F, F, F, E, T, E, E, F, T, F], [T, T, T, F, F, F, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 trivial)

theorem z_1813 : le (tf [T, T, T, F, F, E, E, E, T, T, F, F, F]) zero :=
  le_zero_of_pairs [T, T, T, F, F, E, E, E, T, T, F, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1814 : le (tf [T, T, F, T, F, T, F, F, F, E, E, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1815 : le (tf [T, T, F, T, F, T, F, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, F, E, T, E] [([T, T, F, T, F, T, F, F, E, F, E, E, T], [T, T, F, T, F, T, F, F, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1814 trivial)

theorem z_1816 : le (tf [T, T, F, T, F, T, F, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, T, F, E, E] [([T, T, F, T, F, T, F, F, E, E, F, T, E], [T, T, F, T, F, T, F, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1815 trivial)

theorem z_1817 : le (tf [T, T, F, T, F, T, F, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1818 : le (tf [T, T, F, T, F, T, F, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, E, F, T, E] [([T, T, F, T, F, T, F, F, E, E, F, E, T], [T, T, F, T, F, T, F, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1817 trivial)

theorem z_1819 : le (tf [T, T, F, T, F, T, F, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1820 : le (tf [T, T, F, T, F, T, F, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, E, T, F, E] [([T, T, F, T, F, T, F, F, E, E, E, F, T], [T, T, F, T, F, T, F, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1819 trivial)

theorem z_1821 : le (tf [T, T, F, T, F, T, F, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, E, T, E, F] [([T, T, F, T, F, T, F, F, E, E, E, T, F], [T, T, F, T, F, T, F, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1818 trivial)

theorem z_1822 : le (tf [T, T, F, T, F, F, E, F, E, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, E, T, T, E, F] [([T, T, F, T, F, F, E, F, E, T, E, T, F], [T, T, F, T, F, F, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1523 trivial)

theorem z_1823 : le (tf [T, T, F, T, F, F, F, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, F, E, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1824 : le (tf [T, T, F, T, F, F, F, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, F, E, T, E, T] [([T, T, F, T, F, F, F, E, F, E, E, T, T], [T, T, F, T, F, F, F, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1823 trivial)

theorem z_1825 : le (tf [T, T, F, T, F, F, F, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, T, F, E, E, T] [([T, T, F, T, F, F, F, E, E, F, T, E, T], [T, T, F, T, F, F, F, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1824 trivial)

theorem z_1826 : le (tf [T, T, F, T, F, F, F, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, T, E, E, F, E, T] [([T, T, F, T, F, F, F, E, T, E, F, E, T], [T, T, F, T, F, F, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1825 trivial)

theorem z_1827 : le (tf [T, T, F, T, F, F, E, T, F, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, F, E, F, T, E] [([T, T, F, T, F, F, E, E, F, T, F, T, E], [T, T, F, T, F, F, E, F, E, T, F, T, E]), ([T, T, F, T, F, F, E, T, F, E, F, E, T], [T, T, F, T, F, F, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1523 (And.intro z_1826 trivial))

theorem z_1828 : le (tf [T, T, F, T, F, F, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, F, E, T, E, F] [([T, T, F, T, F, F, E, E, F, T, T, E, F], [T, T, F, T, F, F, E, F, E, T, T, E, F]), ([T, T, F, T, F, F, E, T, F, E, E, T, F], [T, T, F, T, F, F, E, T, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1822 (And.intro z_1827 trivial))

theorem z_1829 : le (tf [T, T, F, T, F, E, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, F, T, F, T, E, E, F] [([T, T, F, E, F, T, F, T, F, T, E, E, F], [T, T, F, F, E, T, F, T, F, T, E, E, F]), ([T, T, F, T, F, E, F, T, F, E, T, E, F], [T, T, F, T, F, F, E, T, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1269 (And.intro z_1828 trivial))

theorem z_1830 : le (tf [T, T, F, T, F, T, F, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, F, E, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1831 : le (tf [T, T, F, T, F, T, F, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, E, F, E, T, E, F] [([T, T, F, T, F, E, F, T, F, E, T, E, F], [T, T, F, T, F, F, E, T, F, E, T, E, F]), ([T, T, F, T, F, T, F, E, F, E, E, T, F], [T, T, F, T, F, T, F, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1828 (And.intro z_1830 trivial))

theorem z_1832 : le (tf [T, T, F, E, F, T, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, F, T, F, T, F, E, T, F, E] [([T, E, F, T, F, T, F, T, F, E, T, F, E], [T, F, E, T, F, T, F, T, F, E, T, F, E]), ([T, T, F, E, F, T, F, E, F, T, T, F, E], [T, T, F, F, E, T, F, E, F, T, T, F, E]), ([T, T, F, E, F, T, F, T, F, E, E, F, T], [T, T, F, F, E, T, F, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1371 (And.intro z_1274 (And.intro z_1275 trivial)))

theorem z_1833 : le (tf [T, T, F, E, F, T, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, T, F, T, F, T, E, E, F] [([T, E, F, T, F, T, F, T, F, T, E, E, F], [T, F, E, T, F, T, F, T, F, T, E, E, F]), ([T, T, F, E, F, T, F, T, F, E, T, E, F], [T, T, F, E, F, T, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1372 (And.intro z_1832 trivial))

theorem z_1834 : le (tf [T, T, F, T, F, F, E, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, F, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1835 : le (tf [T, T, F, T, F, F, E, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, T, F, E, T, F] [([T, T, F, T, F, F, E, E, E, F, T, T, F], [T, T, F, T, F, F, E, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1834 trivial)

theorem z_1836 : le (tf [T, T, F, T, F, F, E, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, T, T, F, E, F] [([T, T, F, T, F, F, E, E, T, E, F, T, F], [T, T, F, T, F, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1835 trivial)

theorem z_1837 : le (tf [T, T, F, T, F, F, E, T, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, E, E, F, T, F] [([T, T, F, T, F, F, E, E, T, E, F, T, F], [T, T, F, T, F, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1835 trivial)

theorem z_1838 : le (tf [T, T, F, T, F, E, F, T, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, F, T, E, T, F, E, F] [([T, T, F, E, F, T, F, T, E, T, F, E, F], [T, T, F, E, F, T, F, T, F, T, E, E, F]), ([T, T, F, T, F, E, F, E, T, T, F, E, F], [T, T, F, T, F, F, E, E, T, T, F, E, F]), ([T, T, F, T, F, E, F, T, E, E, F, T, F], [T, T, F, T, F, F, E, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1833 (And.intro z_1836 (And.intro z_1837 trivial)))

theorem z_1839 : le (tf [T, T, F, T, F, T, F, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, E, E, E, F, T, F] [([T, T, F, T, F, E, F, T, E, E, F, T, F], [T, T, F, T, F, F, E, T, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1837 trivial)

theorem z_1840 : le (tf [T, T, F, T, F, T, F, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, F, E, E, E, T, F, F] [([T, T, F, T, F, E, F, T, E, E, T, F, F], [T, T, F, T, F, F, E, T, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1527 trivial)

theorem z_1841 : le (tf [T, T, F, E, F, T, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, T, F, E, T, T, F, E, F] [([T, E, F, T, F, T, F, E, T, T, F, E, F], [T, F, E, T, F, T, F, E, T, T, F, E, F]), ([T, T, F, E, F, E, F, T, T, T, F, E, F], [T, T, F, F, E, E, F, T, T, T, F, E, F]), ([T, T, F, E, F, T, F, E, T, E, F, T, F], [T, T, F, F, E, T, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1430 (And.intro z_1279 (And.intro z_847 trivial)))

theorem z_1842 : le (tf [F, E, T, T, F, F, E, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1843 : le (tf [F, E, T, T, F, F, E, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, F, E, T, T, F, T, F, E] [([F, E, T, T, F, F, E, T, T, F, E, F, T], [F, E, T, T, F, F, E, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1842 trivial)

theorem z_1844 : le (tf [F, E, T, T, F, T, F, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, F, T, E, E, F, T] [([F, E, T, T, F, T, F, F, E, T, E, F, T], [F, E, T, T, F, T, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1361 trivial)

theorem z_1845 : le (tf [F, E, T, T, F, T, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, F, E, T, F, T, F, E] [([F, E, T, T, F, E, F, T, T, F, T, F, E], [F, E, T, T, F, F, E, T, T, F, T, F, E]), ([F, E, T, T, F, T, F, E, T, F, E, F, T], [F, E, T, T, F, T, F, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1843 (And.intro z_1844 trivial))

theorem z_1846 : le (tf [T, F, F, F, E, E, F, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, F, E, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1847 : le (tf [T, F, F, F, E, E, T, F, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, F, E, T, T, F, T] [([T, F, F, F, E, E, E, F, T, T, T, F, T], [T, F, F, F, E, E, F, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1846 trivial)

theorem z_1848 : le (tf [T, F, F, F, E, E, T, T, F, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, T, F, E, T, F, T] [([T, F, F, F, E, E, T, E, F, T, T, F, T], [T, F, F, F, E, E, T, F, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1847 trivial)

theorem z_1849 : le (tf [T, F, F, F, E, E, T, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, T, T, F, E, F, T] [([T, F, F, F, E, E, T, T, E, F, T, F, T], [T, F, F, F, E, E, T, T, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1848 trivial)

theorem z_1850 : le (tf [T, F, F, E, F, E, T, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, T, F, T, F, E] [([T, F, F, E, F, E, T, T, T, F, E, F, T], [T, F, F, F, E, E, T, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1849 trivial)

theorem z_1851 : le (tf [T, F, F, E, F, E, T, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, F, E, T, T, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1852 : le (tf [T, F, F, E, T, F, E, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, T, F, F, E, T] [([T, F, F, E, E, F, T, T, T, F, F, E, T], [T, F, F, E, F, E, T, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1851 trivial)

theorem z_1853 : le (tf [T, F, F, E, T, F, E, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, F, E, T, F, E, T, T, F, T, F, E] [([T, F, F, E, E, F, T, T, T, F, T, F, E], [T, F, F, E, F, E, T, T, T, F, T, F, E]), ([T, F, F, E, T, F, E, T, T, F, E, F, T], [T, F, F, E, T, F, E, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1850 (And.intro z_1852 trivial))

theorem z_1854 : le (tf [T, F, F, F, F, E, E, T, T, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, T, T, F, E, T, T] [([T, F, F, F, F, E, E, T, E, F, T, T, T], [T, F, F, F, F, E, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1016 trivial)

theorem z_1855 : le (tf [T, F, F, F, F, E, T, E, E, F, T, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, T, E, E, F, T, T, T] [([T, F, F, F, F, E, E, T, E, F, T, T, T], [T, F, F, F, F, E, E, T, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1016 trivial)

theorem z_1856 : le (tf [T, F, F, F, E, F, T, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, T, E, T, F, E, T, T] [([T, F, F, F, E, F, E, T, T, F, E, T, T], [T, F, F, F, F, E, E, T, T, F, E, T, T]), ([T, F, F, F, E, F, T, E, E, F, T, T, T], [T, F, F, F, F, E, T, E, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1854 (And.intro z_1855 trivial))

theorem z_1857 : le (tf [T, F, F, F, E, E, T, F, T, F, T, E, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, E, T, F, T, F, T, E, T] [([T, F, F, F, E, E, T, F, T, F, E, T, T], [T, F, F, F, E, F, T, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1856 trivial)

theorem z_1858 : le (tf [T, F, F, F, F, E, E, E, T, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, F, E, E, E, T, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1859 : le (tf [T, F, F, F, E, F, E, T, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, F, E, T, E, T, T, F, T] [([T, F, F, F, E, F, E, E, T, T, T, F, T], [T, F, F, F, F, E, E, E, T, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1858 trivial)

theorem z_1860 : le (tf [T, F, F, F, E, T, F, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, F, E, E, T, T, F, T] [([T, F, F, F, E, E, F, T, E, T, T, F, T], [T, F, F, F, E, F, E, T, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1859 trivial)

theorem z_1861 : le (tf [T, F, F, F, E, T, E, F, T, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, E, F, T, E, T, F, T] [([T, F, F, F, E, E, T, F, T, E, T, F, T], [T, F, F, F, E, E, T, F, T, F, T, E, T]), ([T, F, F, F, E, T, E, F, E, T, T, F, T], [T, F, F, F, E, T, F, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1857 (And.intro z_1860 trivial))

theorem z_1862 : le (tf [T, F, F, F, E, T, E, T, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, F, E, T, E, T, E, F, T, F, T] [([T, F, F, F, E, E, T, T, E, F, T, F, T], [T, F, F, F, E, E, T, T, F, E, T, F, T]), ([T, F, F, F, E, T, E, E, T, F, T, F, T], [T, F, F, F, E, T, E, F, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1848 (And.intro z_1861 trivial))

theorem z_1863 : le (tf [T, F, F, T, F, E, F, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, E, F, E, E, T, T, F, T] [([T, F, F, E, F, T, F, E, E, T, T, F, T], [T, F, F, F, E, T, F, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1860 trivial)

theorem z_1864 : le (tf [T, F, F, T, F, E, E, F, T, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, E, E, F, T, E, T, F, T] [([T, F, F, E, F, T, E, F, T, E, T, F, T], [T, F, F, F, E, T, E, F, T, E, T, F, T]), ([T, F, F, T, F, E, E, F, E, T, T, F, T], [T, F, F, T, F, E, F, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1861 (And.intro z_1863 trivial))

theorem z_1865 : le (tf [T, F, F, T, F, E, E, T, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, F, E, E, T, E, F, T, F, T] [([T, F, F, E, F, T, E, T, E, F, T, F, T], [T, F, F, F, E, T, E, T, E, F, T, F, T]), ([T, F, F, T, F, E, E, E, T, F, T, F, T], [T, F, F, T, F, E, E, F, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1862 (And.intro z_1864 trivial))

theorem z_1866 : le (tf [T, F, F, T, E, F, E, T, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, F, F, T, E, F, E, T, T, F, E, F, T] [([T, F, F, E, T, F, E, T, T, F, E, F, T], [T, F, F, E, T, F, E, T, T, F, F, E, T]), ([T, F, F, T, E, F, E, T, E, F, T, F, T], [T, F, F, T, F, E, E, T, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1852 (And.intro z_1865 trivial))

theorem z_1867 : le (tf [T, F, F, T, E, E, F, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, F, T, E, E, F, T, T, F, T, F, E] [([T, F, F, E, T, E, F, T, T, F, T, F, E], [T, F, F, E, T, F, E, T, T, F, T, F, E]), ([T, F, F, T, E, E, F, T, T, F, E, F, T], [T, F, F, T, E, F, E, T, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1853 (And.intro z_1866 trivial))

theorem z_1868 : le (tf [T, F, E, T, F, T, F, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, F, T, E, E, F, T] [([E, F, T, T, F, T, F, F, T, E, E, F, T], [F, E, T, T, F, T, F, F, T, E, E, F, T]), ([T, F, E, T, F, T, F, F, E, T, E, F, T], [T, F, E, T, F, T, F, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1844 (And.intro z_1368 trivial))

theorem z_1869 : le (tf [T, F, E, T, F, T, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, F, E, T, F, T, F, E] [([E, F, T, T, F, T, F, E, T, F, T, F, E], [F, E, T, T, F, T, F, E, T, F, T, F, E]), ([T, F, E, T, F, E, F, T, T, F, T, F, E], [T, F, F, T, E, E, F, T, T, F, T, F, E]), ([T, F, E, T, F, T, F, E, T, F, E, F, T], [T, F, E, T, F, T, F, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1845 (And.intro z_1867 (And.intro z_1868 trivial)))

theorem z_1870 : le (tf [T, T, F, E, F, T, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, E, F, T, F, E, T, F, T, F, E] [([T, E, F, T, F, T, F, E, T, F, T, F, E], [T, F, E, T, F, T, F, E, T, F, T, F, E]), ([T, T, F, E, F, E, F, T, T, F, T, F, E], [T, T, F, F, E, E, F, T, T, F, T, F, E]), ([T, T, F, E, F, T, F, E, T, F, E, F, T], [T, T, F, F, E, T, F, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1869 (And.intro z_1282 (And.intro z_861 trivial)))

theorem z_1871 : le (tf [T, T, F, T, F, E, F, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, F, E, T, F, T, E, F] [([T, T, F, E, F, T, F, E, T, F, T, E, F], [T, T, F, E, F, T, F, E, T, F, T, F, E]), ([T, T, F, T, F, E, F, E, T, F, E, T, F], [T, T, F, T, F, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1870 (And.intro z_1835 trivial))

theorem z_1872 : le (tf [T, T, F, T, F, E, F, E, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, F, E, T, T, E, F, F] [([T, T, F, E, F, T, F, E, T, T, E, F, F], [T, T, F, E, F, T, F, E, T, T, F, E, F]), ([T, T, F, T, F, E, F, E, T, E, T, F, F], [T, T, F, T, F, E, F, E, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1841 (And.intro z_1871 trivial))

theorem z_1873 : le (tf [T, T, F, T, F, F, F, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, F, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1874 : le (tf [T, T, F, T, F, F, F, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, F, T, E, T] [([T, T, F, T, F, F, F, E, E, F, E, T, T], [T, T, F, T, F, F, F, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1873 trivial)

theorem z_1875 : le (tf [T, T, F, T, F, F, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, T, E, F, T] [([T, T, F, T, F, F, F, E, E, E, T, F, T], [T, T, F, T, F, F, F, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1874 trivial)

theorem z_1876 : le (tf [T, T, F, T, F, F, E, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, T, E, E, F, T] [([T, T, F, T, F, F, E, F, E, T, E, F, T], [T, T, F, T, F, F, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1875 trivial)

theorem z_1877 : le (tf [T, T, F, T, F, F, E, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, T, F, T, F, E] [([T, T, F, T, F, F, E, E, T, F, E, F, T], [T, T, F, T, F, F, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1876 trivial)

theorem z_1878 : le (tf [T, T, F, T, F, F, F, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1879 : le (tf [T, T, F, T, F, F, E, F, E, T, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, E, T, E, T, F] [([T, T, F, T, F, F, E, F, E, E, T, T, F], [T, T, F, T, F, F, F, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1878 trivial)

theorem z_1880 : le (tf [T, T, F, T, F, F, E, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, F, E, E, T, F] [([T, T, F, T, F, F, E, E, F, T, E, T, F], [T, T, F, T, F, F, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1879 trivial)

theorem z_1881 : le (tf [T, T, F, T, F, F, E, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, E, F, T, E, F] [([T, T, F, T, F, F, E, E, T, F, T, E, F], [T, T, F, T, F, F, E, E, T, F, T, F, E]), ([T, T, F, T, F, F, E, T, E, F, E, T, F], [T, T, F, T, F, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1877 (And.intro z_1880 trivial))

theorem z_1882 : le (tf [T, T, F, T, F, F, T, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, E, E, E, T, F, F] [([T, T, F, T, F, F, E, T, E, E, T, F, F], [T, T, F, T, F, F, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1881 trivial)

theorem z_1883 : le (tf [T, T, F, T, F, E, T, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, T, F, E, T, E, F, F] [([T, T, F, E, F, T, T, F, E, T, E, F, F], [T, T, F, F, E, T, T, F, E, T, E, F, F]), ([T, T, F, T, F, E, E, F, T, T, E, F, F], [T, T, F, T, F, E, F, E, T, T, E, F, F]), ([T, T, F, T, F, E, T, F, E, E, T, F, F], [T, T, F, T, F, F, T, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1767 (And.intro z_1872 (And.intro z_1882 trivial)))

theorem z_1884 : le (tf [T, T, F, T, F, T, E, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, T, E, F, E, E, T, F, F] [([T, T, F, T, F, E, T, F, E, E, T, F, F], [T, T, F, T, F, F, T, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1882 trivial)

theorem z_1885 : le (tf [T, T, F, T, F, F, E, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, E, T, T, F, E] [([T, T, F, T, F, F, E, F, E, T, E, F, T], [T, T, F, T, F, F, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1875 trivial)

theorem z_1886 : le (tf [T, T, F, T, F, F, F, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, E, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1887 : le (tf [T, T, F, T, F, F, E, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, E, T, F, E, T] [([T, T, F, T, F, F, E, F, E, E, F, T, T], [T, T, F, T, F, F, F, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1886 trivial)

theorem z_1888 : le (tf [T, T, F, T, F, F, E, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, F, E, F, E, T] [([T, T, F, T, F, F, E, E, F, T, F, E, T], [T, T, F, T, F, F, E, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1887 trivial)

theorem z_1889 : le (tf [T, T, F, T, F, F, E, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, F, E, T, F, E] [([T, T, F, T, F, F, E, E, F, T, T, F, E], [T, T, F, T, F, F, E, F, E, T, T, F, E]), ([T, T, F, T, F, F, E, T, F, E, E, F, T], [T, T, F, T, F, F, E, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1885 (And.intro z_1888 trivial))

theorem z_1890 : le (tf [T, T, F, T, F, F, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, F, T, E, E, F] [([T, T, F, T, F, F, E, T, F, E, T, E, F], [T, T, F, T, F, F, E, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1889 trivial)

theorem z_1891 : le (tf [T, T, F, T, F, F, T, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, E, E, F, E, T, F] [([T, T, F, T, F, F, E, T, E, F, E, T, F], [T, T, F, T, F, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1880 trivial)

theorem z_1892 : le (tf [T, T, F, T, F, F, T, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, E, E, T, F, E, F] [([T, T, F, T, F, F, E, T, E, T, F, E, F], [T, T, F, T, F, F, E, T, F, T, E, E, F]), ([T, T, F, T, F, F, T, E, E, E, F, T, F], [T, T, F, T, F, F, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1890 (And.intro z_1891 trivial))

theorem z_1893 : le (tf [T, T, F, T, F, F, E, E, T, T, F, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, T, T, F, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1894 : le (tf [T, T, F, T, F, F, E, T, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, E, F, E, T, F] [([T, T, F, T, F, F, E, E, T, F, E, T, F], [T, T, F, T, F, F, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1524 trivial)

theorem z_1895 : le (tf [T, T, F, T, F, F, E, T, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, E, T, F, E, F] [([T, T, F, T, F, F, E, E, T, T, F, E, F], [T, T, F, T, F, F, E, E, T, T, F, F, E]), ([T, T, F, T, F, F, E, T, E, E, F, T, F], [T, T, F, T, F, F, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1893 (And.intro z_1894 trivial))

theorem z_1896 : le (tf [T, T, F, T, F, F, T, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, E, E, E, F, T, F] [([T, T, F, T, F, F, E, T, E, E, F, T, F], [T, T, F, T, F, F, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1894 trivial)

theorem z_1897 : le (tf [T, T, F, T, F, F, E, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, E, T, E, F, F] [([T, T, F, T, F, F, E, E, T, T, E, F, F], [T, T, F, T, F, F, E, E, T, T, F, E, F]), ([T, T, F, T, F, F, E, T, E, E, T, F, F], [T, T, F, T, F, F, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1836 (And.intro z_1881 trivial))

theorem z_1898 : le (tf [T, T, F, F, E, T, T, F, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, F, T, E, E, F] [([T, T, F, F, E, T, T, F, F, E, T, E, F], [T, T, F, F, E, T, T, F, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1804 trivial)

theorem z_1899 : le (tf [T, T, F, F, E, T, T, F, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, T, F, E, E, F, T, F] [([T, T, F, F, E, T, E, F, T, E, F, T, F], [T, T, F, F, E, T, F, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_847 trivial)

theorem z_1900 : le (tf [T, T, F, F, E, T, E, F, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, F, E, T, E, F, T, T, E, F, F] [([T, T, F, F, E, E, T, F, T, T, E, F, F], [T, T, F, F, E, F, T, E, T, T, E, F, F]), ([T, T, F, F, E, T, E, F, T, E, T, F, F], [T, T, F, F, E, T, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1768 (And.intro z_736 trivial))

theorem z_1901 : le (tf [T, T, F, T, F, E, E, F, T, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, E, F, T, T, E, F, F] [([T, T, F, E, F, T, E, F, T, T, E, F, F], [T, T, F, F, E, T, E, F, T, T, E, F, F]), ([T, T, F, T, F, E, E, F, T, E, T, F, F], [T, T, F, T, F, E, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1900 (And.intro z_1529 trivial))

theorem z_1902 : le (tf [F, E, T, T, F, T, E, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, E, F, T, F, T, E, F] [([F, E, T, T, F, E, T, F, T, F, T, E, F], [F, E, T, T, F, E, T, F, T, F, T, F, E]), ([F, E, T, T, F, T, E, F, T, F, E, T, F], [F, E, T, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_801 (And.intro z_933 trivial))

theorem z_1903 : le (tf [F, E, T, T, F, T, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, T, F, E, E, T, F, F] [([F, E, T, T, F, T, E, F, T, E, T, F, F], [F, E, T, T, F, T, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1902 trivial)

theorem z_1904 : le (tf [F, E, T, T, F, T, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, T, F, T, T, E, F, T, E, F, F] [([F, E, T, T, F, T, E, T, F, T, E, F, F], [F, E, T, T, F, T, E, T, F, T, F, E, F]), ([F, E, T, T, F, T, T, E, F, E, T, F, F], [F, E, T, T, F, T, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_935 (And.intro z_1903 trivial))

theorem z_1905 : le (tf [T, F, E, T, F, T, E, F, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, E, F, T, F, T, E, F] [([E, F, T, T, F, T, E, F, T, F, T, E, F], [F, E, T, T, F, T, E, F, T, F, T, E, F]), ([T, F, E, T, F, E, T, F, T, F, T, E, F], [T, F, E, T, F, E, T, F, T, F, T, F, E]), ([T, F, E, T, F, T, E, F, T, F, E, T, F], [T, F, E, T, F, T, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1902 (And.intro z_827 (And.intro z_962 trivial)))

theorem z_1906 : le (tf [T, F, E, T, F, T, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, T, F, E, E, T, F, F] [([E, F, T, T, F, T, T, F, E, E, T, F, F], [F, E, T, T, F, T, T, F, E, E, T, F, F]), ([T, F, E, T, F, T, E, F, T, E, T, F, F], [T, F, E, T, F, T, E, F, T, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1903 (And.intro z_1905 trivial))

theorem z_1907 : le (tf [T, F, E, T, F, T, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, T, F, T, T, E, F, T, E, F, F] [([E, F, T, T, F, T, T, E, F, T, E, F, F], [F, E, T, T, F, T, T, E, F, T, E, F, F]), ([T, F, E, T, F, T, E, T, F, T, E, F, F], [T, F, E, T, F, T, E, T, F, T, F, E, F]), ([T, F, E, T, F, T, T, E, F, E, T, F, F], [T, F, E, T, F, T, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1904 (And.intro z_964 (And.intro z_1906 trivial)))

theorem z_1908 : le (tf [T, T, F, E, F, T, T, F, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, T, T, F, E, E, T, F, F] [([T, E, F, T, F, T, T, F, E, E, T, F, F], [T, F, E, T, F, T, T, F, E, E, T, F, F]), ([T, T, F, E, F, T, E, F, T, E, T, F, F], [T, T, F, F, E, T, E, F, T, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1906 (And.intro z_1807 trivial))

theorem z_1909 : le (tf [T, T, F, E, F, T, T, E, F, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, F, E, F, T, T, E, F, T, E, F, F] [([T, E, F, T, F, T, T, E, F, T, E, F, F], [T, F, E, T, F, T, T, E, F, T, E, F, F]), ([T, T, F, E, F, T, E, T, F, T, E, F, F], [T, T, F, E, F, T, E, T, F, T, F, E, F]), ([T, T, F, E, F, T, T, E, F, E, T, F, F], [T, T, F, E, F, T, T, F, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1907 (And.intro z_984 (And.intro z_1908 trivial)))

theorem z_1910 : le (tf [T, T, F, T, F, F, F, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, E, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1911 : le (tf [T, T, F, T, F, F, E, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, E, T, E, F, T] [([T, T, F, T, F, F, E, F, E, E, T, F, T], [T, T, F, T, F, F, F, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1910 trivial)

theorem z_1912 : le (tf [T, T, F, T, F, F, E, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, F, T, T, F, E] [([T, T, F, T, F, F, E, E, F, T, E, F, T], [T, T, F, T, F, F, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1911 trivial)

theorem z_1913 : le (tf [T, T, F, T, F, F, E, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, T, F, E, E, F, T] [([T, T, F, T, F, F, E, E, F, T, E, F, T], [T, T, F, T, F, F, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1911 trivial)

theorem z_1914 : le (tf [T, T, F, T, F, F, E, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, F, T, T, E, F] [([T, T, F, T, F, F, E, E, F, T, E, T, F], [T, T, F, T, F, F, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1879 trivial)

theorem z_1915 : le (tf [T, T, F, T, F, F, F, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, T, T, F, E] [([T, T, F, T, F, F, F, E, E, T, E, F, T], [T, T, F, T, F, F, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1522 trivial)

theorem z_1916 : le (tf [T, T, F, T, F, F, F, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, T, E, E, F, T] [([T, T, F, T, F, F, F, E, E, T, E, F, T], [T, T, F, T, F, F, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1522 trivial)

theorem z_1917 : le (tf [T, T, F, T, F, F, E, F, T, E, T, F, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, T, E, T, F, E] [([T, T, F, T, F, F, E, F, E, T, T, F, E], [T, T, F, T, F, F, F, E, E, T, T, F, E]), ([T, T, F, T, F, F, E, F, T, E, E, F, T], [T, T, F, T, F, F, F, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1915 (And.intro z_1916 trivial))

theorem z_1918 : le (tf [T, T, F, T, F, F, F, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, F, E, E, F, T, T, E] [([T, T, F, T, F, F, F, E, E, F, T, E, T], [T, T, F, T, F, F, F, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1824 trivial)

theorem z_1919 : le (tf [T, T, F, T, F, F, E, F, T, F, E, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, T, F, E, T, E] [([T, T, F, T, F, F, E, F, E, F, T, T, E], [T, T, F, T, F, F, F, E, E, F, T, T, E]), ([T, T, F, T, F, F, E, F, T, F, E, E, T], [T, T, F, T, F, F, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1918 (And.intro z_1825 trivial))

theorem z_1920 : le (tf [T, T, F, T, F, F, T, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, F, E, F, E, E, T] [([T, T, F, T, F, F, E, F, T, F, E, E, T], [T, T, F, T, F, F, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1825 trivial)

theorem z_1921 : le (tf [T, T, F, T, F, F, T, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, F, E, E, F, T, E] [([T, T, F, T, F, F, E, F, T, E, F, T, E], [T, T, F, T, F, F, E, F, T, F, E, T, E]), ([T, T, F, T, F, F, T, F, E, E, F, E, T], [T, T, F, T, F, F, T, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1919 (And.intro z_1920 trivial))

theorem z_1922 : le (tf [T, T, F, T, F, F, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, F, E, E, T, E, F] [([T, T, F, T, F, F, E, F, T, E, T, E, F], [T, T, F, T, F, F, E, F, T, E, T, F, E]), ([T, T, F, T, F, F, T, F, E, E, E, T, F], [T, T, F, T, F, F, T, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1917 (And.intro z_1921 trivial))

theorem z_1923 : le (tf [T, T, F, T, F, F, E, F, E, F, T, T, E]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, E, F, T, T, E] [([T, T, F, T, F, F, E, F, E, F, T, E, T], [T, T, F, T, F, F, F, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1874 trivial)

theorem z_1924 : le (tf [T, T, F, T, F, F, E, F, T, F, E, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, F, T, F, E, E, T] [([T, T, F, T, F, F, E, F, E, F, T, E, T], [T, T, F, T, F, F, F, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1874 trivial)

theorem z_1925 : le (tf [T, T, F, T, F, F, T, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, F, E, E, F, E, T] [([T, T, F, T, F, F, E, F, T, E, F, E, T], [T, T, F, T, F, F, E, F, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1924 trivial)

theorem z_1926 : le (tf [T, T, F, T, F, F, T, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, T, E, F, E, E, T, F] [([T, T, F, T, F, F, E, T, F, E, E, T, F], [T, T, F, T, F, F, E, T, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1827 trivial)

theorem z_1927 : le (tf [T, T, F, T, F, E, F, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, F, E, E, T, T, F, F] [([T, T, F, E, F, T, F, E, E, T, T, F, F], [T, T, F, F, E, T, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1168 trivial)

theorem z_1928 : le (tf [T, T, F, T, F, E, E, F, T, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, E, F, T, E, T, F, F] [([T, T, F, E, F, T, E, F, T, E, T, F, F], [T, T, F, F, E, T, E, F, T, E, T, F, F]), ([T, T, F, T, F, E, E, F, E, T, T, F, F], [T, T, F, T, F, E, F, E, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1807 (And.intro z_1927 trivial))

theorem z_1929 : le (tf [T, T, F, T, F, F, E, E, E, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, F, E, E, E, T, T, F, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1930 : le (tf [T, T, F, T, F, E, E, E, F, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, F, E, E, E, F, T, T, F, F] [([T, T, F, E, F, T, E, E, F, T, T, F, F], [T, T, F, F, E, T, E, E, F, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_515 trivial)

theorem z_1931 : le (tf [T, T, F, T, E, F, E, E, F, T, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, F, E, E, F, T, T, F, F] [([T, T, F, E, T, F, E, E, F, T, T, F, F], [T, T, F, E, T, F, E, F, E, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_723 trivial)

theorem z_1932 : le (tf [T, T, F, T, E, E, F, T, F, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, F, T, E, E, F, T, F, E, T, F, F] [([T, T, F, E, T, E, F, T, F, E, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F]), ([T, T, F, T, E, E, F, E, F, T, T, F, F], [T, T, F, T, E, F, E, E, F, T, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_724 (And.intro z_1931 trivial))

theorem n_0 : UpperZero (tf [T, T, T, F, T, F, T, F, F, F, E, E, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, F, F, F, E, E, E] ((lfZero_tf_iff _).2 (Or.inl z_44)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_1 : UpperZero (tf [T, T, T, F, T, F, T, F, F, E, F, E, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, F, F, E, F, E, E] (lfZero_of_reply [T, T, T, F, T, F, T, F, F, E, F, E, E] [T, T, T, F, T, F, T, F, F, F, E, E, E] (by decide +kernel) n_0) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_2 : UpperZero (tf [T, T, T, F, T, F, T, F, F, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, F, F, E, E, F, E] (lfZero_of_reply [T, T, T, F, T, F, T, F, F, E, E, F, E] [T, T, T, F, T, F, T, F, F, E, F, E, E] (by decide +kernel) n_1) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_3 : UpperZero (tf [T, T, T, F, T, F, T, F, F, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, F, F, E, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, T, F, F, E, E, E, F] [T, T, T, F, T, F, T, F, F, E, E, F, E] (by decide +kernel) n_2) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_4 : UpperZero (tf [T, T, T, F, T, F, T, F, E, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, F, E, F, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, T, F, E, F, E, E, F] [T, T, T, F, T, F, T, F, F, E, E, E, F] (by decide +kernel) n_3) [[T, T, T, F, T, F, E, F, T, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_60 trivial)
    trivial

theorem n_5 : UpperZero (tf [T, T, T, F, T, F, T, F, E, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, F, E, E, F, E, F] (lfZero_of_reply [T, T, T, F, T, F, T, F, E, E, F, E, F] [T, T, T, F, T, F, T, F, E, F, E, E, F] (by decide +kernel) n_4) [[T, T, T, F, T, F, E, F, T, E, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_78 trivial)
    trivial

theorem n_6 : UpperZero (tf [T, T, T, F, T, F, T, F, E, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, F, E, E, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, T, F, E, E, E, F, F] [T, T, T, F, T, F, T, F, E, E, F, E, F] (by decide +kernel) n_5) [[T, T, T, F, T, F, E, F, T, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_86 trivial)
    trivial

theorem n_7 : UpperZero (tf [T, T, T, F, T, F, T, E, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, E, F, E, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, T, E, F, E, E, F, F] [T, T, T, F, T, F, T, F, E, E, E, F, F] (by decide +kernel) n_6) [[T, T, T, F, T, F, E, T, F, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_99 trivial)
    trivial

theorem n_8 : UpperZero (tf [T, T, T, F, T, F, T, E, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, E, E, F, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, T, E, E, F, E, F, F] [T, T, T, F, T, F, T, E, F, E, E, F, F] (by decide +kernel) n_7) [[T, T, T, F, T, F, E, T, E, F, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_101 trivial)
    trivial

theorem n_9 : UpperZero (tf [T, T, T, F, T, F, T, E, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, T, E, E, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, F, T, E, E, E, F, F, F] [T, T, T, F, T, F, T, E, E, F, E, F, F] (by decide +kernel) n_8) [[T, T, T, F, T, F, E, T, E, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_109 trivial)
    trivial

theorem n_10 : UpperZero (tf [T, F, E, T, T, T, T, F, F, F, F, E, E]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, F, F, F, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_111)) [[E, F, T, T, T, T, T, F, F, F, F, E, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_114 trivial)
    trivial

theorem n_11 : UpperZero (tf [T, T, F, E, T, T, T, F, F, F, F, E, E]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, F, F, F, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_112)) [] [([T, E, F, T, T, T, T, F, F, F, F, E, E], [T, F, E, T, T, T, T, F, F, F, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_10 trivial)

theorem n_12 : UpperZero (tf [T, T, T, F, E, T, T, F, F, F, F, E, E]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, F, F, F, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_113)) [] [([T, T, E, F, T, T, T, F, F, F, F, E, E], [T, T, F, E, T, T, T, F, F, F, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_11 trivial)

theorem n_13 : UpperZero (tf [T, T, T, F, E, T, T, F, F, F, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, F, F, F, E, F, E] (lfZero_of_reply [T, T, T, F, E, T, T, F, F, F, E, F, E] [T, T, T, F, E, T, T, F, F, F, F, E, E] (by decide +kernel) n_12) [[T, T, E, F, T, T, T, F, F, F, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_116 trivial)
    trivial

theorem n_14 : UpperZero (tf [T, T, T, F, E, T, T, F, F, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, F, F, F, E, E, F] (lfZero_of_reply [T, T, T, F, E, T, T, F, F, F, E, E, F] [T, T, T, F, E, T, T, F, F, F, E, F, E] (by decide +kernel) n_13) [[T, T, E, F, T, T, T, F, F, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_119 trivial)
    trivial

theorem n_15 : UpperZero (tf [T, T, T, F, E, T, T, F, F, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, F, F, E, F, E, F] (lfZero_of_reply [T, T, T, F, E, T, T, F, F, E, F, E, F] [T, T, T, F, E, T, T, F, F, F, E, E, F] (by decide +kernel) n_14) [[T, T, E, F, T, T, T, F, F, E, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_123 trivial)
    trivial

theorem n_16 : UpperZero (tf [T, T, T, F, E, T, T, F, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, F, F, E, E, F, F] (lfZero_of_reply [T, T, T, F, E, T, T, F, F, E, E, F, F] [T, T, T, F, E, T, T, F, F, E, F, E, F] (by decide +kernel) n_15) [[T, T, E, F, T, T, T, F, F, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_127 trivial)
    trivial

theorem n_17 : UpperZero (tf [T, T, T, F, F, T, F, F, E, T, F, E, E]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, F, E, T, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_196)) [[T, T, T, F, F, T, F, F, E, E, F, T, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_199 trivial)
    trivial

theorem n_18 : UpperZero (tf [T, T, T, F, F, T, F, F, T, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, F, T, E, E, F, E] ((lfZero_tf_iff _).2 (Or.inl z_197)) [] [([T, T, T, F, F, T, F, F, E, T, E, F, E], [T, T, T, F, F, T, F, F, E, T, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_17 trivial)

theorem n_19 : UpperZero (tf [T, T, T, F, F, T, F, F, T, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, F, T, E, E, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, F, T, E, E, E, F] [T, T, T, F, F, T, F, F, T, E, E, F, E] (by decide +kernel) n_18) [[T, T, T, F, F, T, F, F, E, T, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_202 trivial)
    trivial

theorem n_20 : UpperZero (tf [T, T, T, F, F, T, F, E, T, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, T, F, E, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, T, F, E, E, F] [T, T, T, F, F, T, F, F, T, E, E, E, F] (by decide +kernel) n_19) [[T, T, T, F, F, E, F, T, T, F, E, E, F], [T, T, T, F, F, T, F, E, E, F, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_203 (And.intro z_205 trivial))
    trivial

theorem n_21 : UpperZero (tf [T, T, T, F, F, T, F, E, T, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, T, E, F, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, T, E, F, E, F] [T, T, T, F, F, T, F, E, T, F, E, E, F] (by decide +kernel) n_20) [[T, T, T, F, F, E, F, T, T, E, F, E, F], [T, T, T, F, F, T, F, E, E, T, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_206 (And.intro z_208 trivial))
    trivial

theorem n_22 : UpperZero (tf [T, T, T, F, F, T, F, E, T, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, T, E, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, T, E, E, F, F] [T, T, T, F, F, T, F, E, T, E, F, E, F] (by decide +kernel) n_21) [[T, T, T, F, F, E, F, T, T, E, E, F, F], [T, T, T, F, F, T, F, E, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_211 (And.intro z_212 trivial))
    trivial

theorem n_23 : UpperZero (tf [T, T, T, F, F, T, E, F, T, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, F, T, E, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, F, T, E, E, F, F] [T, T, T, F, F, T, F, E, T, E, E, F, F] (by decide +kernel) n_22) [[T, T, T, F, F, E, T, F, T, E, E, F, F], [T, T, T, F, F, T, E, F, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_84 (And.intro z_216 trivial))
    trivial

theorem n_24 : UpperZero (tf [T, T, T, F, F, T, E, E, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, E, T, F, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, E, T, F, E, F, F] [T, T, T, F, F, T, E, F, T, E, E, F, F] (by decide +kernel) n_23) [[T, T, T, F, F, E, T, E, T, F, E, F, F], [T, T, T, F, F, T, E, E, E, F, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_217 trivial))
    trivial

theorem n_25 : UpperZero (tf [T, F, E, T, T, T, F, F, T, F, F, E, E]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, T, F, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_219)) [[E, F, T, T, T, T, F, F, T, F, F, E, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_221 trivial)
    trivial

theorem n_26 : UpperZero (tf [T, T, F, E, T, T, F, F, T, F, F, E, E]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, T, F, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_220)) [] [([T, E, F, T, T, T, F, F, T, F, F, E, E], [T, F, E, T, T, T, F, F, T, F, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_25 trivial)

theorem n_27 : UpperZero (tf [T, T, F, E, T, T, F, F, T, F, E, F, E]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, T, F, E, F, E] (lfZero_of_reply [T, T, F, E, T, T, F, F, T, F, E, F, E] [T, T, F, E, T, T, F, F, T, F, F, E, E] (by decide +kernel) n_26) [[T, E, F, T, T, T, F, F, T, F, E, F, E], [T, T, F, E, T, T, F, F, E, F, T, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_227 (And.intro z_229 trivial))
    trivial

theorem n_28 : UpperZero (tf [T, T, F, E, T, T, F, F, T, F, E, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, T, F, E, E, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, T, F, E, E, F] [T, T, F, E, T, T, F, F, T, F, E, F, E] (by decide +kernel) n_27) [[T, E, F, T, T, T, F, F, T, F, E, E, F], [T, T, F, E, T, T, F, F, E, F, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_240 (And.intro z_242 trivial))
    trivial

theorem n_29 : UpperZero (tf [T, T, F, E, T, T, F, F, T, E, F, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, T, E, F, E, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, T, E, F, E, F] [T, T, F, E, T, T, F, F, T, F, E, E, F] (by decide +kernel) n_28) [[T, E, F, T, T, T, F, F, T, E, F, E, F], [T, T, F, E, T, T, F, F, E, T, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_252 (And.intro z_254 trivial))
    trivial

theorem n_30 : UpperZero (tf [T, T, F, E, T, T, F, F, T, E, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, T, E, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, T, E, E, F, F] [T, T, F, E, T, T, F, F, T, E, F, E, F] (by decide +kernel) n_29) [[T, E, F, T, T, T, F, F, T, E, E, F, F], [T, T, F, E, T, T, F, F, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_262 (And.intro z_263 trivial))
    trivial

theorem n_31 : UpperZero (tf [T, F, E, T, T, T, F, F, T, F, E, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, T, F, E, F, E] (lfZero_of_reply [T, F, E, T, T, T, F, F, T, F, E, F, E] [T, F, E, T, T, T, F, F, T, F, F, E, E] (by decide +kernel) n_25) [[E, F, T, T, T, T, F, F, T, F, E, F, E], [T, F, E, T, T, T, F, F, E, F, T, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_264 (And.intro z_226 trivial))
    trivial

theorem n_32 : UpperZero (tf [T, F, E, T, T, T, F, F, T, F, E, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, T, F, E, E, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, T, F, E, E, F] [T, F, E, T, T, T, F, F, T, F, E, F, E] (by decide +kernel) n_31) [[E, F, T, T, T, T, F, F, T, F, E, E, F], [T, F, E, T, T, T, F, F, E, F, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_265 (And.intro z_239 trivial))
    trivial

theorem n_33 : UpperZero (tf [T, F, E, T, T, T, F, F, T, E, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, T, E, F, E, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, T, E, F, E, F] [T, F, E, T, T, T, F, F, T, F, E, E, F] (by decide +kernel) n_32) [[E, F, T, T, T, T, F, F, T, E, F, E, F], [T, F, E, T, T, T, F, F, E, T, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_266 (And.intro z_251 trivial))
    trivial

theorem n_34 : UpperZero (tf [T, F, E, T, T, T, F, F, T, E, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, T, E, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, T, E, E, F, F] [T, F, E, T, T, T, F, F, T, E, F, E, F] (by decide +kernel) n_33) [[E, F, T, T, T, T, F, F, T, E, E, F, F], [T, F, E, T, T, T, F, F, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_267 (And.intro z_261 trivial))
    trivial

theorem n_35 : UpperZero (tf [T, F, E, T, F, E, T, T, T, F, F, F, E]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, T, F, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_303)) [[E, F, T, T, F, E, T, T, T, F, F, F, E], [T, F, E, E, F, T, T, T, T, F, F, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_308 (And.intro z_310 trivial))
    trivial

theorem n_36 : UpperZero (tf [T, F, E, T, T, F, E, T, T, F, F, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, F, E, T, T, F, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_304)) [[E, F, T, T, T, F, E, T, T, F, F, F, E]] [([T, F, E, T, E, F, T, T, T, F, F, F, E], [T, F, E, T, F, E, T, T, T, F, F, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_309 trivial)
    (And.intro n_35 trivial)

theorem n_37 : UpperZero (tf [T, F, E, T, T, F, E, T, T, F, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, E, T, T, F, F, E, F] (lfZero_of_reply [T, F, E, T, T, F, E, T, T, F, F, E, F] [T, F, E, T, T, F, E, T, T, F, F, F, E] (by decide +kernel) n_36) [[E, F, T, T, T, F, E, T, T, F, F, E, F], [T, F, E, T, E, F, T, T, T, F, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_313 (And.intro z_315 trivial))
    trivial

theorem n_38 : UpperZero (tf [T, F, E, T, F, E, T, T, T, F, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, T, F, F, E, F] (lfZero_of_reply [T, F, E, T, F, E, T, T, T, F, F, E, F] [T, F, E, T, F, E, T, T, T, F, F, F, E] (by decide +kernel) n_35) [[E, F, T, T, F, E, T, T, T, F, F, E, F], [T, F, E, E, F, T, T, T, T, F, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_318 (And.intro z_319 trivial))
    trivial

theorem n_39 : UpperZero (tf [T, F, E, T, F, E, T, T, F, F, T, F, E]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, F, F, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_353)) [[E, F, T, T, F, E, T, T, F, F, T, F, E], [T, F, E, E, F, T, T, T, F, F, T, F, E], [T, F, E, T, F, E, T, T, F, F, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_362 (And.intro z_364 (And.intro z_365 trivial)))
    trivial

theorem n_40 : UpperZero (tf [T, F, E, T, F, E, T, T, F, F, T, E, F]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, F, F, T, E, F] (lfZero_of_reply [T, F, E, T, F, E, T, T, F, F, T, E, F] [T, F, E, T, F, E, T, T, F, F, T, F, E] (by decide +kernel) n_39) [[E, F, T, T, F, E, T, T, F, F, T, E, F], [T, F, E, E, F, T, T, T, F, F, T, E, F], [T, F, E, T, F, E, T, T, F, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_372 (And.intro z_374 (And.intro z_375 trivial)))
    trivial

theorem n_41 : UpperZero (tf [T, F, E, T, F, E, T, F, E, T, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, F, E, T, T, F, F] ((lfZero_tf_iff _).2 (Or.inl z_399)) [[E, F, T, T, F, E, T, F, E, T, T, F, F], [T, F, E, E, F, T, T, F, E, T, T, F, F], [T, F, E, T, F, E, E, F, T, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_290 (And.intro z_378 (And.intro z_400 trivial)))
    trivial

theorem n_42 : UpperZero (tf [T, F, E, T, F, E, T, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, F, E, T, F, F] (lfZero_of_reply [T, F, E, T, F, E, T, T, F, E, T, F, F] [T, F, E, T, F, E, T, T, F, F, T, E, F] (by decide +kernel) n_40) [[E, F, T, T, F, E, T, T, F, E, T, F, F], [T, F, E, E, F, T, T, T, F, E, T, F, F]] [([T, F, E, T, F, E, T, E, F, T, T, F, F], [T, F, E, T, F, E, T, F, E, T, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_291 (And.intro z_379 trivial))
    (And.intro n_41 trivial)

theorem n_43 : UpperZero (tf [T, F, E, T, F, E, T, T, T, F, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, T, F, E, F, F] (lfZero_of_reply [T, F, E, T, F, E, T, T, T, F, E, F, F] [T, F, E, T, F, E, T, T, T, F, F, E, F] (by decide +kernel) n_38) [[E, F, T, T, F, E, T, T, T, F, E, F, F], [T, F, E, E, F, T, T, T, T, F, E, F, F]] [([T, F, E, T, F, E, T, T, E, F, T, F, F], [T, F, E, T, F, E, T, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_292 (And.intro z_341 trivial))
    (And.intro n_42 trivial)

theorem n_44 : UpperZero (tf [T, F, E, T, T, F, F, T, F, E, T, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_410)) [[E, F, T, T, T, F, F, T, F, E, T, F, E], [T, F, E, T, T, F, F, E, F, T, T, F, E], [T, F, E, T, T, F, F, T, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_416 (And.intro z_420 (And.intro z_421 trivial)))
    trivial

theorem n_45 : UpperZero (tf [T, F, E, T, T, F, F, T, F, E, T, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, F, E, T, E, F] (lfZero_of_reply [T, F, E, T, T, F, F, T, F, E, T, E, F] [T, F, E, T, T, F, F, T, F, E, T, F, E] (by decide +kernel) n_44) [[E, F, T, T, T, F, F, T, F, E, T, E, F], [T, F, E, T, T, F, F, E, F, T, T, E, F], [T, F, E, T, T, F, F, T, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_425 (And.intro z_427 (And.intro z_428 trivial)))
    trivial

theorem n_46 : UpperZero (tf [T, F, E, T, T, F, F, E, T, F, T, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, E, T, F, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_439)) [[E, F, T, T, T, F, F, E, T, F, T, F, E], [T, F, E, T, T, F, F, E, T, F, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_431 (And.intro z_441 trivial))
    trivial

theorem n_47 : UpperZero (tf [T, F, E, T, T, F, F, T, F, E, E, T, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, F, E, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_428)) [[E, F, T, T, T, F, F, T, F, E, E, T, F], [T, F, E, T, T, F, F, E, F, T, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_434 (And.intro z_443 trivial))
    trivial

theorem n_48 : UpperZero (tf [T, F, E, T, T, F, F, T, E, F, T, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, E, F, T, E, F] (lfZero_of_reply [T, F, E, T, T, F, F, T, E, F, T, E, F] [T, F, E, T, T, F, F, T, F, E, T, E, F] (by decide +kernel) n_45) [[E, F, T, T, T, F, F, T, E, F, T, E, F]] [([T, F, E, T, T, F, F, E, T, F, T, E, F], [T, F, E, T, T, F, F, E, T, F, T, F, E]), ([T, F, E, T, T, F, F, T, E, F, E, T, F], [T, F, E, T, T, F, F, T, F, E, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_435 trivial)
    (And.intro n_46 (And.intro n_47 trivial))

theorem n_49 : UpperZero (tf [T, F, E, T, T, F, F, E, T, F, T, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, E, T, F, T, E, F] (lfZero_of_reply [T, F, E, T, T, F, F, E, T, F, T, E, F] [T, F, E, T, T, F, F, E, T, F, T, F, E] (by decide +kernel) n_46) [[E, F, T, T, T, F, F, E, T, F, T, E, F], [T, F, E, T, T, F, F, E, T, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_446 (And.intro z_449 trivial))
    trivial

theorem n_50 : UpperZero (tf [T, F, E, T, T, F, F, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, E, E, T, F, F] (lfZero_of_reply [T, F, E, T, T, F, F, T, E, E, T, F, F] [T, F, E, T, T, F, F, T, E, F, T, E, F] (by decide +kernel) n_48) [[E, F, T, T, T, F, F, T, E, E, T, F, F]] [([T, F, E, T, T, F, F, E, T, E, T, F, F], [T, F, E, T, T, F, F, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_447 trivial)
    (And.intro n_49 trivial)

theorem n_51 : UpperZero (tf [T, F, E, T, T, F, F, E, E, T, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, E, E, T, T, F, F] ((lfZero_tf_iff _).2 (Or.inl z_451)) [[E, F, T, T, T, F, F, E, E, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_452 trivial)
    trivial

theorem n_52 : UpperZero (tf [T, F, E, T, T, F, E, F, E, T, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, E, F, E, T, T, F, F] (lfZero_of_reply [T, F, E, T, T, F, E, F, E, T, T, F, F] [T, F, E, T, T, F, F, E, E, T, T, F, F] (by decide +kernel) n_51) [[E, F, T, T, T, F, E, F, E, T, T, F, F]] [([T, F, E, T, E, F, T, F, E, T, T, F, F], [T, F, E, T, F, E, T, F, E, T, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_293 trivial)
    (And.intro n_41 trivial)

theorem n_53 : UpperZero (tf [T, F, E, T, T, F, E, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, E, T, F, E, T, F, F] (lfZero_of_reply [T, F, E, T, T, F, E, T, F, E, T, F, F] [T, F, E, T, T, F, F, T, E, E, T, F, F] (by decide +kernel) n_50) [[E, F, T, T, T, F, E, T, F, E, T, F, F]] [([T, F, E, T, E, F, T, T, F, E, T, F, F], [T, F, E, T, F, E, T, T, F, E, T, F, F]), ([T, F, E, T, T, F, E, E, F, T, T, F, F], [T, F, E, T, T, F, E, F, E, T, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_294 trivial)
    (And.intro n_42 (And.intro n_52 trivial))

theorem n_54 : UpperZero (tf [T, F, E, T, T, F, E, T, T, F, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, E, T, T, F, E, F, F] (lfZero_of_reply [T, F, E, T, T, F, E, T, T, F, E, F, F] [T, F, E, T, T, F, E, T, T, F, F, E, F] (by decide +kernel) n_37) [[E, F, T, T, T, F, E, T, T, F, E, F, F]] [([T, F, E, T, E, F, T, T, T, F, E, F, F], [T, F, E, T, F, E, T, T, T, F, E, F, F]), ([T, F, E, T, T, F, E, T, E, F, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_295 trivial)
    (And.intro n_43 (And.intro n_53 trivial))

theorem n_55 : UpperZero (tf [T, F, E, T, T, T, F, F, F, E, T, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_454)) [[E, F, T, T, T, T, F, F, F, E, T, F, E], [T, F, E, T, T, T, F, F, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_455 (And.intro z_225 trivial))
    trivial

theorem n_56 : UpperZero (tf [T, F, E, T, T, T, F, F, F, E, T, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, F, E, T, E, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, F, E, T, E, F] [T, F, E, T, T, T, F, F, F, E, T, F, E] (by decide +kernel) n_55) [[E, F, T, T, T, T, F, F, F, E, T, E, F], [T, F, E, T, T, T, F, F, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_456 (And.intro z_238 trivial))
    trivial

theorem n_57 : UpperZero (tf [T, F, E, T, T, T, F, F, E, F, T, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, E, F, T, E, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, E, F, T, E, F] [T, F, E, T, T, T, F, F, F, E, T, E, F] (by decide +kernel) n_56) [[E, F, T, T, T, T, F, F, E, F, T, E, F], [T, F, E, T, T, T, F, F, E, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_457 (And.intro z_250 trivial))
    trivial

theorem n_58 : UpperZero (tf [T, F, E, T, T, T, F, F, E, E, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, E, E, T, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, E, E, T, F, F] [T, F, E, T, T, T, F, F, E, F, T, E, F] (by decide +kernel) n_57) [[E, F, T, T, T, T, F, F, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_458 trivial)
    trivial

theorem n_59 : UpperZero (tf [T, F, E, T, T, T, F, E, F, E, T, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, E, F, E, T, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, E, F, E, T, F, F] [T, F, E, T, T, T, F, F, E, E, T, F, F] (by decide +kernel) n_58) [[E, F, T, T, T, T, F, E, F, E, T, F, F]] [([T, F, E, T, T, E, F, T, F, E, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_296 trivial)
    (And.intro n_53 trivial)

theorem n_60 : UpperZero (tf [T, F, E, T, T, T, F, E, T, F, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, E, T, F, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, E, T, F, E, F, F] [T, F, E, T, T, T, F, F, T, E, E, F, F] (by decide +kernel) n_34) [[E, F, T, T, T, T, F, E, T, F, E, F, F]] [([T, F, E, T, T, E, F, T, T, F, E, F, F], [T, F, E, T, T, F, E, T, T, F, E, F, F]), ([T, F, E, T, T, T, F, E, E, F, T, F, F], [T, F, E, T, T, T, F, E, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_297 trivial)
    (And.intro n_54 (And.intro n_59 trivial))

theorem n_61 : UpperZero (tf [T, T, F, F, E, E, T, T, T, F, F, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, T, F, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_461)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_62 : UpperZero (tf [T, T, F, E, F, E, T, T, T, F, F, F, E]) :=
  upperZero_of_pairs [T, T, F, E, F, E, T, T, T, F, F, F, E] (lfZero_of_reply [T, T, F, E, F, E, T, T, T, F, F, F, E] [T, T, F, F, E, E, T, T, T, F, F, F, E] (by decide +kernel) n_61) [] [([T, E, F, T, F, E, T, T, T, F, F, F, E], [T, F, E, T, F, E, T, T, T, F, F, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_35 trivial)

theorem n_63 : UpperZero (tf [T, T, F, E, T, F, E, T, T, F, F, F, E]) :=
  upperZero_of_pairs [T, T, F, E, T, F, E, T, T, F, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_460)) [] [([T, E, F, T, T, F, E, T, T, F, F, F, E], [T, F, E, T, T, F, E, T, T, F, F, F, E]), ([T, T, F, E, E, F, T, T, T, F, F, F, E], [T, T, F, E, F, E, T, T, T, F, F, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_36 (And.intro n_62 trivial))

theorem n_64 : UpperZero (tf [T, T, F, E, T, F, E, T, T, F, F, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, F, E, T, T, F, F, E, F] (lfZero_of_reply [T, T, F, E, T, F, E, T, T, F, F, E, F] [T, T, F, E, T, F, E, T, T, F, F, F, E] (by decide +kernel) n_63) [[T, T, F, E, E, F, T, T, T, F, F, E, F]] [([T, E, F, T, T, F, E, T, T, F, F, E, F], [T, F, E, T, T, F, E, T, T, F, F, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_462 trivial)
    (And.intro n_37 trivial)

theorem n_65 : UpperZero (tf [T, T, F, F, E, E, T, T, T, F, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, T, F, F, E, F] (lfZero_of_reply [T, T, F, F, E, E, T, T, T, F, F, E, F] [T, T, F, F, E, E, T, T, T, F, F, F, E] (by decide +kernel) n_61) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_66 : UpperZero (tf [T, T, F, F, E, E, T, T, F, F, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, F, F, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_464)) [[T, T, F, F, E, E, T, T, F, F, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_465 trivial)
    trivial

theorem n_67 : UpperZero (tf [T, T, F, F, E, E, T, T, F, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, F, F, T, E, F] (lfZero_of_reply [T, T, F, F, E, E, T, T, F, F, T, E, F] [T, T, F, F, E, E, T, T, F, F, T, F, E] (by decide +kernel) n_66) [[T, T, F, F, E, E, T, T, F, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_466 trivial)
    trivial

theorem n_68 : UpperZero (tf [T, T, F, F, E, E, T, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, F, E, T, F, F] (lfZero_of_reply [T, T, F, F, E, E, T, T, F, E, T, F, F] [T, T, F, F, E, E, T, T, F, F, T, E, F] (by decide +kernel) n_67) [[T, T, F, F, E, E, T, E, F, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_469 trivial)
    trivial

theorem n_69 : UpperZero (tf [T, T, F, F, E, E, T, T, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, T, F, E, F, F] (lfZero_of_reply [T, T, F, F, E, E, T, T, T, F, E, F, F] [T, T, F, F, E, E, T, T, T, F, F, E, F] (by decide +kernel) n_65) [] [([T, T, F, F, E, E, T, T, E, F, T, F, F], [T, T, F, F, E, E, T, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_68 trivial)

theorem n_70 : UpperZero (tf [T, T, F, F, E, F, T, F, T, E, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, F, T, F, T, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_481)) [[T, T, F, F, E, F, T, F, E, T, T, F, E], [T, T, F, F, E, F, T, F, T, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_493 (And.intro z_494 trivial))
    trivial

theorem n_71 : UpperZero (tf [T, T, F, F, E, F, T, F, T, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, F, T, F, T, E, T, E, F] (lfZero_of_reply [T, T, F, F, E, F, T, F, T, E, T, E, F] [T, T, F, F, E, F, T, F, T, E, T, F, E] (by decide +kernel) n_70) [[T, T, F, F, E, F, T, F, E, T, T, E, F], [T, T, F, F, E, F, T, F, T, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_498 (And.intro z_499 trivial))
    trivial

theorem n_72 : UpperZero (tf [T, T, F, F, E, F, T, E, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, F, T, E, T, F, T, E, F] (lfZero_of_reply [T, T, F, F, E, F, T, E, T, F, T, E, F] [T, T, F, F, E, F, T, F, T, E, T, E, F] (by decide +kernel) n_71) [[T, T, F, F, E, F, E, T, T, F, T, E, F], [T, T, F, F, E, F, T, E, T, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_503 (And.intro z_505 trivial))
    trivial

theorem n_73 : UpperZero (tf [T, T, F, F, E, E, T, F, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, F, T, F, T, E, F] (lfZero_of_reply [T, T, F, F, E, E, T, F, T, F, T, E, F] [T, T, F, F, E, F, T, E, T, F, T, E, F] (by decide +kernel) n_72) [[T, T, F, F, E, E, T, F, T, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_510 trivial)
    trivial

theorem n_74 : UpperZero (tf [T, T, F, F, E, E, T, F, T, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, F, T, E, T, F, F] (lfZero_of_reply [T, T, F, F, E, E, T, F, T, E, T, F, F] [T, T, F, F, E, E, T, F, T, F, T, E, F] (by decide +kernel) n_73) [[T, T, F, F, E, E, T, F, E, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_512 trivial)
    trivial

theorem n_75 : UpperZero (tf [T, T, F, F, E, E, T, T, E, F, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, E, F, T, F, F] (lfZero_of_reply [T, T, F, F, E, E, T, T, E, F, T, F, F] [T, T, F, F, E, E, T, T, F, E, T, F, F] (by decide +kernel) n_68) [] [([T, T, F, F, E, E, T, E, T, F, T, F, F], [T, T, F, F, E, E, T, F, T, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_74 trivial)

theorem n_76 : UpperZero (tf [T, T, F, E, F, E, T, T, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, F, E, T, T, T, F, E, F, F] (lfZero_of_reply [T, T, F, E, F, E, T, T, T, F, E, F, F] [T, T, F, F, E, E, T, T, T, F, E, F, F] (by decide +kernel) n_69) [] [([T, E, F, T, F, E, T, T, T, F, E, F, F], [T, F, E, T, F, E, T, T, T, F, E, F, F]), ([T, T, F, E, F, E, T, T, E, F, T, F, F], [T, T, F, F, E, E, T, T, E, F, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_43 (And.intro n_75 trivial))

theorem n_77 : UpperZero (tf [T, T, F, F, E, E, T, F, E, T, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, F, E, T, T, F, F] ((lfZero_tf_iff _).2 (Or.inl z_512)) [[T, T, F, F, E, E, E, F, T, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_513 trivial)
    trivial

theorem n_78 : UpperZero (tf [T, T, F, F, E, E, T, E, F, T, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, E, F, T, T, F, F] (lfZero_of_reply [T, T, F, F, E, E, T, E, F, T, T, F, F] [T, T, F, F, E, E, T, F, E, T, T, F, F] (by decide +kernel) n_77) [[T, T, F, F, E, E, E, T, F, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_514 trivial)
    trivial

theorem n_79 : UpperZero (tf [T, T, F, E, F, E, T, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, E, F, E, T, T, F, E, T, F, F] (lfZero_of_reply [T, T, F, E, F, E, T, T, F, E, T, F, F] [T, T, F, F, E, E, T, T, F, E, T, F, F] (by decide +kernel) n_68) [] [([T, E, F, T, F, E, T, T, F, E, T, F, F], [T, F, E, T, F, E, T, T, F, E, T, F, F]), ([T, T, F, E, F, E, T, E, F, T, T, F, F], [T, T, F, F, E, E, T, E, F, T, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_42 (And.intro n_78 trivial))

theorem n_80 : UpperZero (tf [T, T, F, F, T, E, E, E, F, T, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, E, E, F, T, T, F, F] (lfZero_of_mirror_dec [T, T, F, F, T, E, E, E, F, T, T, F, F] (by decide +kernel)) [[T, T, F, F, E, T, E, E, F, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_515 trivial)
    trivial

theorem n_81 : UpperZero (tf [T, T, F, E, T, F, E, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, F, E, T, F, E, T, F, F] (lfZero_of_mirror_dec [T, T, F, E, T, F, E, T, F, E, T, F, F] (by decide +kernel)) [] [([T, E, F, T, T, F, E, T, F, E, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F]), ([T, T, F, E, E, F, T, T, F, E, T, F, F], [T, T, F, E, F, E, T, T, F, E, T, F, F]), ([T, T, F, E, T, F, E, E, F, T, T, F, F], [T, T, F, F, T, E, E, E, F, T, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_53 (And.intro n_79 (And.intro n_80 trivial)))

theorem n_82 : UpperZero (tf [T, T, F, E, T, F, E, T, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, F, E, T, T, F, E, F, F] (lfZero_of_reply [T, T, F, E, T, F, E, T, T, F, E, F, F] [T, T, F, E, T, F, E, T, T, F, F, E, F] (by decide +kernel) n_64) [] [([T, E, F, T, T, F, E, T, T, F, E, F, F], [T, F, E, T, T, F, E, T, T, F, E, F, F]), ([T, T, F, E, E, F, T, T, T, F, E, F, F], [T, T, F, E, F, E, T, T, T, F, E, F, F]), ([T, T, F, E, T, F, E, T, E, F, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_54 (And.intro n_76 (And.intro n_81 trivial)))

theorem n_83 : UpperZero (tf [T, T, F, E, T, T, F, F, F, E, T, F, E]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_517)) [[T, T, F, E, T, T, F, F, F, E, E, F, T]] [([T, E, F, T, T, T, F, F, F, E, T, F, E], [T, F, E, T, T, T, F, F, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_228 trivial)
    (And.intro n_55 trivial)

theorem n_84 : UpperZero (tf [T, T, F, E, T, T, F, F, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, F, E, T, E, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, F, E, T, E, F] [T, T, F, E, T, T, F, F, F, E, T, F, E] (by decide +kernel) n_83) [[T, T, F, E, T, T, F, F, F, E, E, T, F]] [([T, E, F, T, T, T, F, F, F, E, T, E, F], [T, F, E, T, T, T, F, F, F, E, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_241 trivial)
    (And.intro n_56 trivial)

theorem n_85 : UpperZero (tf [T, T, F, E, T, T, F, F, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, E, F, T, E, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, E, F, T, E, F] [T, T, F, E, T, T, F, F, F, E, T, E, F] (by decide +kernel) n_84) [[T, T, F, E, T, T, F, F, E, F, E, T, F]] [([T, E, F, T, T, T, F, F, E, F, T, E, F], [T, F, E, T, T, T, F, F, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_253 trivial)
    (And.intro n_57 trivial)

theorem n_86 : UpperZero (tf [T, T, F, E, T, T, F, F, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, E, E, T, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, E, E, T, F, F] [T, T, F, E, T, T, F, F, E, F, T, E, F] (by decide +kernel) n_85) [] [([T, E, F, T, T, T, F, F, E, E, T, F, F], [T, F, E, T, T, T, F, F, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_58 trivial)

theorem n_87 : UpperZero (tf [T, T, F, E, T, T, F, E, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, E, F, E, T, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, E, F, E, T, F, F] [T, T, F, E, T, T, F, F, E, E, T, F, F] (by decide +kernel) n_86) [] [([T, E, F, T, T, T, F, E, F, E, T, F, F], [T, F, E, T, T, T, F, E, F, E, T, F, F]), ([T, T, F, E, T, E, F, T, F, E, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_59 (And.intro n_81 trivial))

theorem n_88 : UpperZero (tf [T, T, F, E, T, T, F, E, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, E, T, F, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, E, T, F, E, F, F] [T, T, F, E, T, T, F, F, T, E, E, F, F] (by decide +kernel) n_30) [] [([T, E, F, T, T, T, F, E, T, F, E, F, F], [T, F, E, T, T, T, F, E, T, F, E, F, F]), ([T, T, F, E, T, E, F, T, T, F, E, F, F], [T, T, F, E, T, F, E, T, T, F, E, F, F]), ([T, T, F, E, T, T, F, E, E, F, T, F, F], [T, T, F, E, T, T, F, E, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_60 (And.intro n_82 (And.intro n_87 trivial)))

theorem n_89 : UpperZero (tf [T, T, T, F, F, E, E, T, T, F, F, F, E]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, T, T, F, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_518)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_90 : UpperZero (tf [T, T, T, F, F, E, E, T, T, F, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, T, T, F, F, E, F] (lfZero_of_reply [T, T, T, F, F, E, E, T, T, F, F, E, F] [T, T, T, F, F, E, E, T, T, F, F, F, E] (by decide +kernel) n_89) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_91 : UpperZero (tf [T, T, T, F, F, E, E, T, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, T, T, F, E, F, F] (lfZero_of_reply [T, T, T, F, F, E, E, T, T, F, E, F, F] [T, T, T, F, F, E, E, T, T, F, F, E, F] (by decide +kernel) n_90) [[T, T, T, F, F, E, E, T, E, F, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_521 trivial)
    trivial

theorem n_92 : UpperZero (tf [T, T, T, F, F, F, E, T, F, E, T, F, E]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, T, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_68)) [[T, T, T, F, F, F, E, E, F, T, T, F, E], [T, T, T, F, F, F, E, T, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_524 (And.intro z_525 trivial))
    trivial

theorem n_93 : UpperZero (tf [T, T, T, F, F, F, E, T, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, T, F, E, T, E, F] (lfZero_of_reply [T, T, T, F, F, F, E, T, F, E, T, E, F] [T, T, T, F, F, F, E, T, F, E, T, F, E] (by decide +kernel) n_92) [[T, T, T, F, F, F, E, E, F, T, T, E, F], [T, T, T, F, F, F, E, T, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_526 (And.intro z_72 trivial))
    trivial

theorem n_94 : UpperZero (tf [T, T, T, F, F, F, E, T, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, T, E, F, T, E, F] (lfZero_of_reply [T, T, T, F, F, F, E, T, E, F, T, E, F] [T, T, T, F, F, F, E, T, F, E, T, E, F] (by decide +kernel) n_93) [[T, T, T, F, F, F, E, E, T, F, T, E, F], [T, T, T, F, F, F, E, T, E, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_213 (And.intro z_81 trivial))
    trivial

theorem n_95 : UpperZero (tf [T, T, T, F, F, F, E, F, T, E, T, F, E]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, F, T, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_529)) [[T, T, T, F, F, F, E, F, E, T, T, F, E], [T, T, T, F, F, F, E, F, T, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_64 (And.intro z_91 trivial))
    trivial

theorem n_96 : UpperZero (tf [T, T, T, F, F, F, E, F, T, E, T, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, F, T, E, T, E, F] (lfZero_of_reply [T, T, T, F, F, F, E, F, T, E, T, E, F] [T, T, T, F, F, F, E, F, T, E, T, F, E] (by decide +kernel) n_95) [[T, T, T, F, F, F, E, F, E, T, T, E, F], [T, T, T, F, F, F, E, F, T, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_80 trivial))
    trivial

theorem n_97 : UpperZero (tf [T, T, T, F, F, F, E, E, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, E, T, F, T, E, F] (lfZero_of_reply [T, T, T, F, F, F, E, E, T, F, T, E, F] [T, T, T, F, F, F, E, F, T, E, T, E, F] (by decide +kernel) n_96) [[T, T, T, F, F, F, E, E, T, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_88 trivial)
    trivial

theorem n_98 : UpperZero (tf [T, T, T, F, F, F, E, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, T, E, E, T, F, F] (lfZero_of_reply [T, T, T, F, F, F, E, T, E, E, T, F, F] [T, T, T, F, F, F, E, T, E, F, T, E, F] (by decide +kernel) n_94) [] [([T, T, T, F, F, F, E, E, T, E, T, F, F], [T, T, T, F, F, F, E, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_97 trivial)

theorem n_99 : UpperZero (tf [T, T, T, F, F, E, F, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, F, T, E, E, T, F, F] (lfZero_of_reply [T, T, T, F, F, E, F, T, E, E, T, F, F] [T, T, T, F, F, F, E, T, E, E, T, F, F] (by decide +kernel) n_98) [[T, T, T, F, F, E, F, E, T, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_531 trivial)
    trivial

theorem n_100 : UpperZero (tf [T, T, T, F, F, E, E, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, T, F, E, T, F, F] (lfZero_of_reply [T, T, T, F, F, E, E, T, F, E, T, F, F] [T, T, T, F, F, E, F, T, E, E, T, F, F] (by decide +kernel) n_99) [[T, T, T, F, F, E, E, E, F, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_532 trivial)
    trivial

theorem n_101 : UpperZero (tf [T, T, T, F, F, E, E, T, E, F, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, T, E, F, T, F, F] (lfZero_of_reply [T, T, T, F, F, E, E, T, E, F, T, F, F] [T, T, T, F, F, E, E, T, F, E, T, F, F] (by decide +kernel) n_100) [[T, T, T, F, F, E, E, E, T, F, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_533 trivial)
    trivial

theorem n_102 : UpperZero (tf [T, T, T, F, E, F, E, T, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, F, E, T, T, F, E, F, F] (lfZero_of_reply [T, T, T, F, E, F, E, T, T, F, E, F, F] [T, T, T, F, F, E, E, T, T, F, E, F, F] (by decide +kernel) n_91) [] [([T, T, E, F, T, F, E, T, T, F, E, F, F], [T, T, F, E, T, F, E, T, T, F, E, F, F]), ([T, T, T, F, E, F, E, T, E, F, T, F, F], [T, T, T, F, F, E, E, T, E, F, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_82 (And.intro n_101 trivial))

theorem n_103 : UpperZero (tf [T, T, T, F, F, T, F, F, E, E, T, F, E]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, F, E, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_201)) [[T, T, T, F, F, T, F, F, E, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_534 trivial)
    trivial

theorem n_104 : UpperZero (tf [T, T, T, F, F, T, F, F, E, E, T, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, F, E, E, T, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, F, E, E, T, E, F] [T, T, T, F, F, T, F, F, E, E, T, F, E] (by decide +kernel) n_103) [[T, T, T, F, F, T, F, F, E, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_535 trivial)
    trivial

theorem n_105 : UpperZero (tf [T, T, T, F, F, T, F, E, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, F, E, T, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, F, E, T, E, F] [T, T, T, F, F, T, F, F, E, E, T, E, F] (by decide +kernel) n_104) [[T, T, T, F, F, T, F, E, F, E, E, T, F]] [([T, T, T, F, F, E, F, T, F, E, T, E, F], [T, T, T, F, F, F, E, T, F, E, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_204 trivial)
    (And.intro n_93 trivial)

theorem n_106 : UpperZero (tf [T, T, T, F, F, T, F, E, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, E, F, T, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, E, F, T, E, F] [T, T, T, F, F, T, F, E, F, E, T, E, F] (by decide +kernel) n_105) [[T, T, T, F, F, T, F, E, E, F, E, T, F]] [([T, T, T, F, F, E, F, T, E, F, T, E, F], [T, T, T, F, F, F, E, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_207 trivial)
    (And.intro n_94 trivial)

theorem n_107 : UpperZero (tf [T, T, T, F, F, T, F, E, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, E, E, T, F, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, E, E, T, F, F] [T, T, T, F, F, T, F, E, E, F, T, E, F] (by decide +kernel) n_106) [] [([T, T, T, F, F, E, F, T, E, E, T, F, F], [T, T, T, F, F, F, E, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_98 trivial)

theorem n_108 : UpperZero (tf [T, T, T, F, F, T, E, F, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, F, E, E, T, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, F, E, E, T, F, F] [T, T, T, F, F, T, F, E, E, E, T, F, F] (by decide +kernel) n_107) [[T, T, T, F, F, E, T, F, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_536 trivial)
    trivial

theorem n_109 : UpperZero (tf [T, T, T, F, F, T, E, E, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, E, F, E, T, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, E, F, E, T, F, F] [T, T, T, F, F, T, E, F, E, E, T, F, F] (by decide +kernel) n_108) [[T, T, T, F, F, E, T, E, F, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_104 trivial)
    trivial

theorem n_110 : UpperZero (tf [T, T, T, F, F, T, E, E, E, F, T, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, E, E, F, T, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, E, E, F, T, F, F] [T, T, T, F, F, T, E, E, F, E, T, F, F] (by decide +kernel) n_109) [[T, T, T, F, F, E, T, E, E, F, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_539 trivial)
    trivial

theorem n_111 : UpperZero (tf [T, T, T, F, E, T, F, E, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, F, E, T, F, E, F, F] (lfZero_of_reply [T, T, T, F, E, T, F, E, T, F, E, F, F] [T, T, T, F, F, T, E, E, T, F, E, F, F] (by decide +kernel) n_24) [] [([T, T, E, F, T, T, F, E, T, F, E, F, F], [T, T, F, E, T, T, F, E, T, F, E, F, F]), ([T, T, T, F, E, E, F, T, T, F, E, F, F], [T, T, T, F, E, F, E, T, T, F, E, F, F]), ([T, T, T, F, E, T, F, E, E, F, T, F, F], [T, T, T, F, F, T, E, E, E, F, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_88 (And.intro n_102 (And.intro n_110 trivial)))

theorem n_112 : UpperZero (tf [T, T, T, F, E, T, T, F, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, F, E, F, E, F, F] (lfZero_of_reply [T, T, T, F, E, T, T, F, E, F, E, F, F] [T, T, T, F, E, T, T, F, F, E, E, F, F] (by decide +kernel) n_16) [[T, T, E, F, T, T, T, F, E, F, E, F, F]] [([T, T, T, F, E, T, E, F, T, F, E, F, F], [T, T, T, F, E, T, F, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_193 trivial)
    (And.intro n_111 trivial)

theorem n_113 : UpperZero (tf [T, T, T, F, T, F, F, F, E, T, F, E, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, F, E, T, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_542)) [[T, T, T, F, T, F, F, F, E, E, F, T, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_545 trivial)
    trivial

theorem n_114 : UpperZero (tf [T, T, T, F, T, F, F, F, T, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, F, T, E, E, F, E] ((lfZero_tf_iff _).2 (Or.inl z_543)) [] [([T, T, T, F, T, F, F, F, E, T, E, F, E], [T, T, T, F, T, F, F, F, E, T, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_113 trivial)

theorem n_115 : UpperZero (tf [T, T, T, F, T, F, F, F, T, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, F, T, E, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, F, T, E, E, E, F] [T, T, T, F, T, F, F, F, T, E, E, F, E] (by decide +kernel) n_114) [[T, T, T, F, T, F, F, F, E, T, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_548 trivial)
    trivial

theorem n_116 : UpperZero (tf [T, T, T, F, T, F, F, E, T, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, E, T, F, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, E, T, F, E, E, F] [T, T, T, F, T, F, F, F, T, E, E, E, F] (by decide +kernel) n_115) [[T, T, T, F, T, F, F, E, E, F, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_59 trivial)
    trivial

theorem n_117 : UpperZero (tf [T, T, T, F, T, F, F, E, T, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, E, T, E, F, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, E, T, E, F, E, F] [T, T, T, F, T, F, F, E, T, F, E, E, F] (by decide +kernel) n_116) [[T, T, T, F, T, F, F, E, E, T, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_77 trivial)
    trivial

theorem n_118 : UpperZero (tf [T, T, T, F, T, F, F, E, T, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, E, T, E, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, F, E, T, E, E, F, F] [T, T, T, F, T, F, F, E, T, E, F, E, F] (by decide +kernel) n_117) [[T, T, T, F, T, F, F, E, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_85 trivial)
    trivial

theorem n_119 : UpperZero (tf [T, T, T, F, T, F, E, F, T, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, F, T, E, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, F, T, E, E, F, F] [T, T, T, F, T, F, F, E, T, E, E, F, F] (by decide +kernel) n_118) [[T, T, T, F, E, F, T, F, T, E, E, F, F], [T, T, T, F, T, F, E, F, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_596 (And.intro z_98 trivial))
    trivial

theorem n_120 : UpperZero (tf [T, T, T, F, T, F, E, E, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, E, T, F, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, E, T, F, E, F, F] [T, T, T, F, T, F, E, F, T, E, E, F, F] (by decide +kernel) n_119) [[T, T, T, F, E, F, T, E, T, F, E, F, F], [T, T, T, F, T, F, E, E, E, F, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_598 (And.intro z_599 trivial))
    trivial

theorem n_121 : UpperZero (tf [T, T, T, F, T, F, E, E, T, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, E, T, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, E, T, E, F, F, F] [T, T, T, F, T, F, E, E, T, F, E, F, F] (by decide +kernel) n_120) [[T, T, T, F, E, F, T, E, T, E, F, F, F], [T, T, T, F, T, F, E, E, E, T, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_746 (And.intro z_747 trivial))
    trivial

theorem n_122 : UpperZero (tf [T, T, T, F, T, E, F, E, T, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, E, F, E, T, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, E, F, E, T, E, F, F, F] [T, T, T, F, T, F, E, E, T, E, F, F, F] (by decide +kernel) n_121) [[T, T, T, F, T, E, F, E, E, T, F, F, F]] [([T, T, T, F, E, T, F, E, T, E, F, F, F], [T, T, T, F, E, T, F, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_752 trivial)
    (And.intro n_111 trivial)

theorem n_123 : UpperZero (tf [T, T, T, F, T, E, T, F, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, E, T, F, E, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, E, T, F, E, E, F, F, F] [T, T, T, F, T, F, T, E, E, E, F, F, F] (by decide +kernel) n_9) [] [([T, T, T, F, E, T, T, F, E, E, F, F, F], [T, T, T, F, E, T, T, F, E, F, E, F, F]), ([T, T, T, F, T, E, E, F, T, E, F, F, F], [T, T, T, F, T, E, F, E, T, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_112 (And.intro n_122 trivial))

theorem n_124 : UpperZero (tf [T, T, T, F, T, E, T, E, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, E, T, E, F, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, E, T, E, F, E, F, F, F] [T, T, T, F, T, E, T, F, E, E, F, F, F] (by decide +kernel) n_123) [[T, T, T, F, E, T, T, E, F, E, F, F, F], [T, T, T, F, T, E, E, T, F, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_769 (And.intro z_780 trivial))
    trivial

theorem n_125 : UpperZero (tf [T, T, T, F, T, F, F, T, F, F, E, E, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, T, F, F, E, E, E] ((lfZero_tf_iff _).2 (Or.inl z_781)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_126 : UpperZero (tf [T, T, T, F, T, F, F, T, F, E, F, E, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, T, F, E, F, E, E] (lfZero_of_reply [T, T, T, F, T, F, F, T, F, E, F, E, E] [T, T, T, F, T, F, F, T, F, F, E, E, E] (by decide +kernel) n_125) [] [([T, T, T, F, T, F, F, E, F, T, F, E, E], [T, T, T, F, T, F, F, F, E, T, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_113 trivial)

theorem n_127 : UpperZero (tf [T, T, T, F, T, F, F, T, F, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, T, F, E, E, F, E] (lfZero_of_reply [T, T, T, F, T, F, F, T, F, E, E, F, E] [T, T, T, F, T, F, F, T, F, E, F, E, E] (by decide +kernel) n_126) [[T, T, T, F, T, F, F, E, F, T, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_782 trivial)
    trivial

theorem n_128 : UpperZero (tf [T, T, T, F, T, F, F, T, F, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, T, F, E, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, T, F, E, E, E, F] [T, T, T, F, T, F, F, T, F, E, E, F, E] (by decide +kernel) n_127) [[T, T, T, F, T, F, F, E, F, T, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_784 trivial)
    trivial

theorem n_129 : UpperZero (tf [T, T, T, F, T, F, F, T, E, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, T, E, F, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, T, E, F, E, E, F] [T, T, T, F, T, F, F, T, F, E, E, E, F] (by decide +kernel) n_128) [] [([T, T, T, F, T, F, F, E, T, F, E, E, F], [T, T, T, F, T, F, F, F, T, E, E, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_115 trivial)

theorem n_130 : UpperZero (tf [T, T, T, F, T, F, F, T, E, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, T, E, E, F, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, T, E, E, F, E, F] [T, T, T, F, T, F, F, T, E, F, E, E, F] (by decide +kernel) n_129) [] [([T, T, T, F, T, F, F, E, T, E, F, E, F], [T, T, T, F, T, F, F, E, T, F, E, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_116 trivial)

theorem n_131 : UpperZero (tf [T, T, T, F, T, F, F, T, E, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, T, E, E, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, F, T, E, E, E, F, F] [T, T, T, F, T, F, F, T, E, E, F, E, F] (by decide +kernel) n_130) [] [([T, T, T, F, T, F, F, E, T, E, E, F, F], [T, T, T, F, T, F, F, E, T, E, F, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_117 trivial)

theorem n_132 : UpperZero (tf [T, T, T, F, T, F, E, T, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, T, F, E, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, T, F, E, E, F, F] [T, T, T, F, T, F, F, T, E, E, E, F, F] (by decide +kernel) n_131) [[T, T, T, F, E, F, T, T, F, E, E, F, F], [T, T, T, F, T, F, E, E, F, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_869 (And.intro z_871 trivial))
    trivial

theorem n_133 : UpperZero (tf [T, T, T, F, T, F, E, T, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, T, E, F, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, T, E, F, E, F, F] [T, T, T, F, T, F, E, T, F, E, E, F, F] (by decide +kernel) n_132) [[T, T, T, F, E, F, T, T, E, F, E, F, F]] [([T, T, T, F, T, F, E, E, T, F, E, F, F], [T, T, T, F, T, F, E, F, T, E, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_875 trivial)
    (And.intro n_119 trivial)

theorem n_134 : UpperZero (tf [T, T, T, F, T, F, E, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, T, E, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, T, E, E, F, F, F] [T, T, T, F, T, F, E, T, E, F, E, F, F] (by decide +kernel) n_133) [[T, T, T, F, E, F, T, T, E, E, F, F, F]] [([T, T, T, F, T, F, E, E, T, E, F, F, F], [T, T, T, F, T, F, E, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_881 trivial)
    (And.intro n_120 trivial)

theorem n_135 : UpperZero (tf [T, T, T, F, T, E, F, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, E, F, T, E, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, E, F, T, E, E, F, F, F] [T, T, T, F, T, F, E, T, E, E, F, F, F] (by decide +kernel) n_134) [[T, T, T, F, E, T, F, T, E, E, F, F, F]] [([T, T, T, F, T, E, F, E, T, E, F, F, F], [T, T, T, F, T, F, E, E, T, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_768 trivial)
    (And.intro n_121 trivial)

theorem n_136 : UpperZero (tf [T, T, T, F, F, T, F, T, F, F, E, E, E]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, T, F, F, E, E, E] ((lfZero_tf_iff _).2 (Or.inl z_882)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_137 : UpperZero (tf [T, T, T, F, F, T, F, T, F, E, F, E, E]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, T, F, E, F, E, E] (lfZero_of_reply [T, T, T, F, F, T, F, T, F, E, F, E, E] [T, T, T, F, F, T, F, T, F, F, E, E, E] (by decide +kernel) n_136) [] [([T, T, T, F, F, T, F, E, F, T, F, E, E], [T, T, T, F, F, T, F, F, E, T, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_17 trivial)

theorem n_138 : UpperZero (tf [T, T, T, F, F, T, F, T, F, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, T, F, E, E, F, E] (lfZero_of_reply [T, T, T, F, F, T, F, T, F, E, E, F, E] [T, T, T, F, F, T, F, T, F, E, F, E, E] (by decide +kernel) n_137) [[T, T, T, F, F, T, F, E, F, T, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_884 trivial)
    trivial

theorem n_139 : UpperZero (tf [T, T, T, F, F, T, F, T, F, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, T, F, E, E, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, T, F, E, E, E, F] [T, T, T, F, F, T, F, T, F, E, E, F, E] (by decide +kernel) n_138) [[T, T, T, F, F, T, F, E, F, T, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_886 trivial)
    trivial

theorem n_140 : UpperZero (tf [T, T, T, F, F, T, F, T, E, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, T, E, F, E, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, T, E, F, E, E, F] [T, T, T, F, F, T, F, T, F, E, E, E, F] (by decide +kernel) n_139) [] [([T, T, T, F, F, T, F, E, T, F, E, E, F], [T, T, T, F, F, T, F, F, T, E, E, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_19 trivial)

theorem n_141 : UpperZero (tf [T, T, T, F, F, T, F, T, E, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, T, E, E, F, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, T, E, E, F, E, F] [T, T, T, F, F, T, F, T, E, F, E, E, F] (by decide +kernel) n_140) [] [([T, T, T, F, F, T, F, E, T, E, F, E, F], [T, T, T, F, F, T, F, E, T, F, E, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_20 trivial)

theorem n_142 : UpperZero (tf [T, T, T, F, F, T, F, T, E, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, T, E, E, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, F, T, E, E, E, F, F] [T, T, T, F, F, T, F, T, E, E, F, E, F] (by decide +kernel) n_141) [] [([T, T, T, F, F, T, F, E, T, E, E, F, F], [T, T, T, F, F, T, F, E, T, E, F, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_21 trivial)

theorem n_143 : UpperZero (tf [T, T, T, F, F, T, E, T, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, T, F, E, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, T, F, E, E, F, F] [T, T, T, F, F, T, F, T, E, E, E, F, F] (by decide +kernel) n_142) [[T, T, T, F, F, E, T, T, F, E, E, F, F], [T, T, T, F, F, T, E, E, F, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_96 (And.intro z_766 trivial))
    trivial

theorem n_144 : UpperZero (tf [T, T, T, F, F, T, E, T, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, T, E, F, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, T, E, F, E, F, F] [T, T, T, F, F, T, E, T, F, E, E, F, F] (by decide +kernel) n_143) [[T, T, T, F, F, E, T, T, E, F, E, F, F]] [([T, T, T, F, F, T, E, E, T, F, E, F, F], [T, T, T, F, F, T, E, F, T, E, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_100 trivial)
    (And.intro n_23 trivial)

theorem n_145 : UpperZero (tf [T, T, T, F, F, T, E, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, T, E, E, F, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, T, E, E, F, F, F] [T, T, T, F, F, T, E, T, E, F, E, F, F] (by decide +kernel) n_144) [[T, T, T, F, F, E, T, T, E, E, F, F, F]] [([T, T, T, F, F, T, E, E, T, E, F, F, F], [T, T, T, F, F, T, E, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_106 trivial)
    (And.intro n_24 trivial)

theorem n_146 : UpperZero (tf [T, F, E, T, T, T, F, T, F, F, F, E, E]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, T, F, F, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_888)) [[E, F, T, T, T, T, F, T, F, F, F, E, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_890 trivial)
    trivial

theorem n_147 : UpperZero (tf [T, T, F, E, T, T, F, T, F, F, F, E, E]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, T, F, F, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_889)) [] [([T, E, F, T, T, T, F, T, F, F, F, E, E], [T, F, E, T, T, T, F, T, F, F, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_146 trivial)

theorem n_148 : UpperZero (tf [T, T, F, E, T, T, F, T, F, F, E, F, E]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, T, F, F, E, F, E] (lfZero_of_reply [T, T, F, E, T, T, F, T, F, F, E, F, E] [T, T, F, E, T, T, F, T, F, F, F, E, E] (by decide +kernel) n_147) [[T, E, F, T, T, T, F, T, F, F, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_892 trivial)
    trivial

theorem n_149 : UpperZero (tf [T, T, F, E, T, T, F, T, F, F, E, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, T, F, F, E, E, F] (lfZero_of_reply [T, T, F, E, T, T, F, T, F, F, E, E, F] [T, T, F, E, T, T, F, T, F, F, E, F, E] (by decide +kernel) n_148) [[T, E, F, T, T, T, F, T, F, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_895 trivial)
    trivial

theorem n_150 : UpperZero (tf [T, T, F, E, T, T, F, T, F, E, F, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, T, F, E, F, E, F] (lfZero_of_reply [T, T, F, E, T, T, F, T, F, E, F, E, F] [T, T, F, E, T, T, F, T, F, F, E, E, F] (by decide +kernel) n_149) [[T, E, F, T, T, T, F, T, F, E, F, E, F], [T, T, F, E, T, T, F, E, F, T, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_911 (And.intro z_924 trivial))
    trivial

theorem n_151 : UpperZero (tf [T, T, F, E, T, T, F, T, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, T, F, E, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, T, F, E, E, F, F] [T, T, F, E, T, T, F, T, F, E, F, E, F] (by decide +kernel) n_150) [[T, E, F, T, T, T, F, T, F, E, E, F, F], [T, T, F, E, T, T, F, E, F, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_980 (And.intro z_993 trivial))
    trivial

theorem n_152 : UpperZero (tf [T, T, F, E, T, T, F, T, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, T, E, F, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, T, E, F, E, F, F] [T, T, F, E, T, T, F, T, F, E, E, F, F] (by decide +kernel) n_151) [[T, E, F, T, T, T, F, T, E, F, E, F, F]] [([T, T, F, E, T, T, F, E, T, F, E, F, F], [T, T, F, E, T, T, F, F, T, E, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_996 trivial)
    (And.intro n_30 trivial)

theorem n_153 : UpperZero (tf [T, F, E, T, T, T, F, T, F, F, E, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, T, F, F, E, F, E] (lfZero_of_reply [T, F, E, T, T, T, F, T, F, F, E, F, E] [T, F, E, T, T, T, F, T, F, F, F, E, E] (by decide +kernel) n_146) [[E, F, T, T, T, T, F, T, F, F, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_997 trivial)
    trivial

theorem n_154 : UpperZero (tf [T, F, E, T, T, T, F, T, F, F, E, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, T, F, F, E, E, F] (lfZero_of_reply [T, F, E, T, T, T, F, T, F, F, E, E, F] [T, F, E, T, T, T, F, T, F, F, E, F, E] (by decide +kernel) n_153) [[E, F, T, T, T, T, F, T, F, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_998 trivial)
    trivial

theorem n_155 : UpperZero (tf [T, F, E, T, T, T, F, T, F, E, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, T, F, E, F, E, F] (lfZero_of_reply [T, F, E, T, T, T, F, T, F, E, F, E, F] [T, F, E, T, T, T, F, T, F, F, E, E, F] (by decide +kernel) n_154) [[E, F, T, T, T, T, F, T, F, E, F, E, F], [T, F, E, T, T, T, F, E, F, T, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_999 (And.intro z_910 trivial))
    trivial

theorem n_156 : UpperZero (tf [T, F, E, T, T, T, F, T, F, E, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, T, F, E, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, T, F, E, E, F, F] [T, F, E, T, T, T, F, T, F, E, F, E, F] (by decide +kernel) n_155) [[E, F, T, T, T, T, F, T, F, E, E, F, F], [T, F, E, T, T, T, F, E, F, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1000 (And.intro z_979 trivial))
    trivial

theorem n_157 : UpperZero (tf [T, F, E, T, T, T, F, T, E, F, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, T, E, F, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, T, E, F, E, F, F] [T, F, E, T, T, T, F, T, F, E, E, F, F] (by decide +kernel) n_156) [[E, F, T, T, T, T, F, T, E, F, E, F, F]] [([T, F, E, T, T, T, F, E, T, F, E, F, F], [T, F, E, T, T, T, F, F, T, E, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1001 trivial)
    (And.intro n_34 trivial)

theorem n_158 : UpperZero (tf [T, F, E, T, T, T, F, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, T, E, E, F, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, T, E, E, F, F, F] [T, F, E, T, T, T, F, T, E, F, E, F, F] (by decide +kernel) n_157) [[E, F, T, T, T, T, F, T, E, E, F, F, F]] [([T, F, E, T, T, T, F, E, T, E, F, F, F], [T, F, E, T, T, T, F, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1002 trivial)
    (And.intro n_60 trivial)

theorem n_159 : UpperZero (tf [T, T, F, E, T, T, F, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, T, E, E, F, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, T, E, E, F, F, F] [T, T, F, E, T, T, F, T, E, F, E, F, F] (by decide +kernel) n_152) [] [([T, E, F, T, T, T, F, T, E, E, F, F, F], [T, F, E, T, T, T, F, T, E, E, F, F, F]), ([T, T, F, E, T, T, F, E, T, E, F, F, F], [T, T, F, E, T, T, F, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_158 (And.intro n_88 trivial))

theorem n_160 : UpperZero (tf [T, T, T, F, E, T, F, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, F, T, E, E, F, F, F] (lfZero_of_reply [T, T, T, F, E, T, F, T, E, E, F, F, F] [T, T, T, F, F, T, E, T, E, E, F, F, F] (by decide +kernel) n_145) [] [([T, T, E, F, T, T, F, T, E, E, F, F, F], [T, T, F, E, T, T, F, T, E, E, F, F, F]), ([T, T, T, F, E, T, F, E, T, E, F, F, F], [T, T, T, F, E, T, F, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_159 (And.intro n_111 trivial))

theorem n_161 : UpperZero (tf [T, T, T, F, T, F, F, F, E, T, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, F, E, T, E, F, E] (lfZero_of_reply [T, T, T, F, T, F, F, F, E, T, E, F, E] [T, T, T, F, T, F, F, F, E, T, F, E, E] (by decide +kernel) n_113) [[T, T, T, F, T, F, F, F, E, E, T, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_547 trivial)
    trivial

theorem n_162 : UpperZero (tf [T, T, T, F, T, F, F, F, E, T, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, F, E, T, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, F, E, T, E, E, F] [T, T, T, F, T, F, F, F, E, T, E, F, E] (by decide +kernel) n_161) [[T, T, T, F, T, F, F, F, E, E, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_783 trivial)
    trivial

theorem n_163 : UpperZero (tf [T, T, T, F, T, F, F, E, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, E, F, T, E, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, E, F, T, E, E, F] [T, T, T, F, T, F, F, F, E, T, E, E, F] (by decide +kernel) n_162) [[T, T, T, F, T, F, F, E, F, E, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1004 trivial)
    trivial

theorem n_164 : UpperZero (tf [T, T, T, F, T, F, F, E, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, E, E, T, F, E, F] (lfZero_of_reply [T, T, T, F, T, F, F, E, E, T, F, E, F] [T, T, T, F, T, F, F, E, F, T, E, E, F] (by decide +kernel) n_163) [[T, T, T, F, T, F, F, E, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1005 trivial)
    trivial

theorem n_165 : UpperZero (tf [T, T, T, F, T, F, F, E, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, F, E, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, F, E, E, T, E, F, F] [T, T, T, F, T, F, F, E, E, T, F, E, F] (by decide +kernel) n_164) [[T, T, T, F, T, F, F, E, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_97 trivial)
    trivial

theorem n_166 : UpperZero (tf [T, T, T, F, T, F, E, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, F, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, F, E, T, E, F, F] [T, T, T, F, T, F, F, E, E, T, E, F, F] (by decide +kernel) n_165) [[T, T, T, F, E, F, T, F, E, T, E, F, F], [T, T, T, F, T, F, E, F, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1007 (And.intro z_870 trivial))
    trivial

theorem n_167 : UpperZero (tf [T, T, T, F, T, F, E, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, E, F, T, E, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, E, F, T, E, F, F] [T, T, T, F, T, F, E, F, E, T, E, F, F] (by decide +kernel) n_166) [[T, T, T, F, E, F, T, E, F, T, E, F, F], [T, T, T, F, T, F, E, E, F, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_775 (And.intro z_107 trivial))
    trivial

theorem n_168 : UpperZero (tf [T, T, T, F, T, F, E, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, F, E, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, T, F, E, E, E, T, F, F, F] [T, T, T, F, T, F, E, E, F, T, E, F, F] (by decide +kernel) n_167) [[T, T, T, F, E, F, T, E, E, T, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1174 trivial)
    trivial

theorem n_169 : UpperZero (tf [T, T, T, F, F, T, F, F, E, T, E, F, E]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, F, E, T, E, F, E] (lfZero_of_reply [T, T, T, F, F, T, F, F, E, T, E, F, E] [T, T, T, F, F, T, F, F, E, T, F, E, E] (by decide +kernel) n_17) [[T, T, T, F, F, T, F, F, E, E, T, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_201 trivial)
    trivial

theorem n_170 : UpperZero (tf [T, T, T, F, F, T, F, F, E, T, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, F, E, T, E, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, F, E, T, E, E, F] [T, T, T, F, F, T, F, F, E, T, E, F, E] (by decide +kernel) n_169) [] [([T, T, T, F, F, T, F, F, E, E, T, E, F], [T, T, T, F, F, T, F, F, E, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_103 trivial)

theorem n_171 : UpperZero (tf [T, T, T, F, F, T, F, E, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, F, T, E, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, F, T, E, E, F] [T, T, T, F, F, T, F, F, E, T, E, E, F] (by decide +kernel) n_170) [[T, T, T, F, F, E, F, T, F, T, E, E, F]] [([T, T, T, F, F, T, F, E, F, E, T, E, F], [T, T, T, F, F, T, F, F, E, E, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1175 trivial)
    (And.intro n_104 trivial)

theorem n_172 : UpperZero (tf [T, T, T, F, F, T, F, E, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, E, T, F, E, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, E, T, F, E, F] [T, T, T, F, F, T, F, E, F, T, E, E, F] (by decide +kernel) n_171) [[T, T, T, F, F, E, F, T, E, T, F, E, F], [T, T, T, F, F, T, F, E, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1177 (And.intro z_1178 trivial))
    trivial

theorem n_173 : UpperZero (tf [T, T, T, F, F, T, F, E, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, F, E, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, F, E, E, T, E, F, F] [T, T, T, F, F, T, F, E, E, T, F, E, F] (by decide +kernel) n_172) [[T, T, T, F, F, E, F, T, E, T, E, F, F]] [([T, T, T, F, F, T, F, E, E, E, T, F, F], [T, T, T, F, F, T, F, E, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_749 trivial)
    (And.intro n_106 trivial)

theorem n_174 : UpperZero (tf [T, T, T, F, F, T, E, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, F, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, F, E, T, E, F, F] [T, T, T, F, F, T, F, E, E, T, E, F, F] (by decide +kernel) n_173) [[T, T, T, F, F, E, T, F, E, T, E, F, F]] [([T, T, T, F, F, T, E, F, E, E, T, F, F], [T, T, T, F, F, T, F, E, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_95 trivial)
    (And.intro n_107 trivial)

theorem n_175 : UpperZero (tf [T, T, T, F, F, T, E, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, E, F, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, E, F, T, E, F, F] [T, T, T, F, F, T, E, F, E, T, E, F, F] (by decide +kernel) n_174) [[T, T, T, F, F, E, T, E, F, T, E, F, F]] [([T, T, T, F, F, T, E, E, F, E, T, F, F], [T, T, T, F, F, T, E, F, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_750 trivial)
    (And.intro n_108 trivial)

theorem n_176 : UpperZero (tf [T, T, T, F, F, T, E, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, T, E, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, F, T, E, E, E, T, F, F, F] [T, T, T, F, F, T, E, E, F, T, E, F, F] (by decide +kernel) n_175) [[T, T, T, F, F, E, T, E, E, T, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_745 trivial)
    trivial

theorem n_177 : UpperZero (tf [T, T, T, F, T, E, F, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, E, F, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, T, E, F, E, E, T, F, F, F] [T, T, T, F, T, F, E, E, E, T, F, F, F] (by decide +kernel) n_168) [] [([T, T, T, F, E, T, F, E, E, T, F, F, F], [T, T, T, F, F, T, E, E, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_176 trivial)

theorem n_178 : UpperZero (tf [T, F, E, T, T, T, F, F, F, T, E, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1179)) [[E, F, T, T, T, T, F, F, F, T, E, E, F]] [([T, F, E, T, T, T, F, F, F, E, T, E, F], [T, F, E, T, T, T, F, F, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1181 trivial)
    (And.intro n_55 trivial)

theorem n_179 : UpperZero (tf [T, T, F, E, T, T, F, F, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1180)) [] [([T, E, F, T, T, T, F, F, F, T, E, E, F], [T, F, E, T, T, T, F, F, F, T, E, E, F]), ([T, T, F, E, T, T, F, F, F, E, T, E, F], [T, T, F, E, T, T, F, F, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_178 (And.intro n_83 trivial))

theorem n_180 : UpperZero (tf [T, T, F, E, T, T, F, F, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, E, T, F, E, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, E, T, F, E, F] [T, T, F, E, T, T, F, F, F, T, E, E, F] (by decide +kernel) n_179) [[T, E, F, T, T, T, F, F, E, T, F, E, F], [T, T, F, E, T, T, F, F, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1182 (And.intro z_923 trivial))
    trivial

theorem n_181 : UpperZero (tf [T, T, F, E, T, T, F, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, F, E, T, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, F, E, T, E, F, F] [T, T, F, E, T, T, F, F, E, T, F, E, F] (by decide +kernel) n_180) [[T, E, F, T, T, T, F, F, E, T, E, F, F]] [([T, T, F, E, T, T, F, F, E, E, T, F, F], [T, T, F, E, T, T, F, F, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1183 trivial)
    (And.intro n_85 trivial)

theorem n_182 : UpperZero (tf [T, T, F, F, T, F, E, T, F, E, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1237)) [[T, T, F, F, E, F, T, T, F, E, T, F, E], [T, T, F, F, T, F, E, E, F, T, T, F, E], [T, T, F, F, T, F, E, T, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1240 (And.intro z_1244 (And.intro z_1245 trivial)))
    trivial

theorem n_183 : UpperZero (tf [T, T, F, F, T, F, E, T, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1238)) [[T, T, F, F, E, F, T, T, F, T, E, E, F]] [([T, T, F, F, T, F, E, T, F, E, T, E, F], [T, T, F, F, T, F, E, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1241 trivial)
    (And.intro n_182 trivial)

theorem n_184 : UpperZero (tf [T, T, F, F, T, F, E, T, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, E, T, F, E, F] (lfZero_of_reply [T, T, F, F, T, F, E, T, E, T, F, E, F] [T, T, F, F, T, F, E, T, F, T, E, E, F] (by decide +kernel) n_183) [[T, T, F, F, E, F, T, T, E, T, F, E, F], [T, T, F, F, T, F, E, E, T, T, F, E, F], [T, T, F, F, T, F, E, T, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1249 (And.intro z_1250 (And.intro z_1251 trivial)))
    trivial

theorem n_185 : UpperZero (tf [T, T, F, F, T, F, E, E, T, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, E, T, T, F, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1250)) [[T, T, F, F, E, F, T, E, T, T, F, E, F], [T, T, F, F, T, F, E, E, T, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1253 (And.intro z_1262 trivial))
    trivial

theorem n_186 : UpperZero (tf [T, T, F, F, T, F, E, T, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, F, E, T, E, F] (lfZero_of_reply [T, T, F, F, T, F, E, T, F, E, T, E, F] [T, T, F, F, T, F, E, T, F, E, T, F, E] (by decide +kernel) n_182) [[T, T, F, F, E, F, T, T, F, E, T, E, F], [T, T, F, F, T, F, E, E, F, T, T, E, F], [T, T, F, F, T, F, E, T, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_583 (And.intro z_1263 (And.intro z_591 trivial)))
    trivial

theorem n_187 : UpperZero (tf [T, T, F, F, T, F, E, E, T, F, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, E, T, F, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_588)) [[T, T, F, F, T, F, E, E, T, F, E, F, T]] [([T, T, F, F, E, F, T, E, T, F, T, F, E], [T, T, F, F, E, F, T, F, T, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1265 trivial)
    (And.intro n_70 trivial)

theorem n_188 : UpperZero (tf [T, T, F, F, T, F, E, T, F, E, E, T, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, F, E, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_591)) [[T, T, F, F, E, F, T, T, F, E, E, T, F], [T, T, F, F, T, F, E, E, F, T, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1257 (And.intro z_1261 trivial))
    trivial

theorem n_189 : UpperZero (tf [T, T, F, F, T, F, E, T, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, E, F, T, E, F] (lfZero_of_reply [T, T, F, F, T, F, E, T, E, F, T, E, F] [T, T, F, F, T, F, E, T, F, E, T, E, F] (by decide +kernel) n_186) [[T, T, F, F, E, F, T, T, E, F, T, E, F]] [([T, T, F, F, T, F, E, E, T, F, T, E, F], [T, T, F, F, T, F, E, E, T, F, T, F, E]), ([T, T, F, F, T, F, E, T, E, F, E, T, F], [T, T, F, F, T, F, E, T, F, E, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1258 trivial)
    (And.intro n_187 (And.intro n_188 trivial))

theorem n_190 : UpperZero (tf [T, T, F, F, T, F, E, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, E, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, F, E, T, E, T, E, F, F] [T, T, F, F, T, F, E, T, E, T, F, E, F] (by decide +kernel) n_184) [[T, T, F, F, E, F, T, T, E, T, E, F, F]] [([T, T, F, F, T, F, E, E, T, T, E, F, F], [T, T, F, F, T, F, E, E, T, T, F, E, F]), ([T, T, F, F, T, F, E, T, E, E, T, F, F], [T, T, F, F, T, F, E, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1259 trivial)
    (And.intro n_185 (And.intro n_189 trivial))

theorem n_191 : UpperZero (tf [T, T, F, F, T, E, F, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, F, T, E, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, E, F, T, E, T, E, F, F] [T, T, F, F, T, F, E, T, E, T, E, F, F] (by decide +kernel) n_190) [[T, T, F, F, E, T, F, T, E, T, E, F, F], [T, T, F, F, T, E, F, E, T, T, E, F, F], [T, T, F, F, T, E, F, T, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_734 (And.intro z_580 (And.intro z_739 trivial)))
    trivial

theorem n_192 : UpperZero (tf [T, T, F, F, E, T, F, T, F, E, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1268)) [[T, T, F, F, E, T, F, E, F, T, T, F, E], [T, T, F, F, E, T, F, T, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1274 (And.intro z_1275 trivial))
    trivial

theorem n_193 : UpperZero (tf [T, T, F, F, E, T, F, T, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1269)) [] [([T, T, F, F, E, T, F, T, F, E, T, E, F], [T, T, F, F, E, T, F, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_192 trivial)

theorem n_194 : UpperZero (tf [T, T, F, F, E, T, F, T, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, E, T, F, E, F] (lfZero_of_reply [T, T, F, F, E, T, F, T, E, T, F, E, F] [T, T, F, F, E, T, F, T, F, T, E, E, F] (by decide +kernel) n_193) [[T, T, F, F, E, T, F, E, T, T, F, E, F], [T, T, F, F, E, T, F, T, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_563 (And.intro z_916 trivial))
    trivial

theorem n_195 : UpperZero (tf [T, T, F, F, E, T, F, E, T, T, F, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, E, T, T, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1277)) [[T, T, F, F, E, E, F, T, T, T, F, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1278 trivial)
    trivial

theorem n_196 : UpperZero (tf [T, T, F, F, E, T, F, E, T, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, E, T, T, F, E, F] (lfZero_of_reply [T, T, F, F, E, T, F, E, T, T, F, E, F] [T, T, F, F, E, T, F, E, T, T, F, F, E] (by decide +kernel) n_195) [[T, T, F, F, E, E, F, T, T, T, F, E, F], [T, T, F, F, E, T, F, E, T, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1279 (And.intro z_847 trivial))
    trivial

theorem n_197 : UpperZero (tf [T, T, F, F, E, T, F, T, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, F, E, T, E, F] (lfZero_of_reply [T, T, F, F, E, T, F, T, F, E, T, E, F] [T, T, F, F, E, T, F, T, F, E, T, F, E] (by decide +kernel) n_192) [[T, T, F, F, E, T, F, E, F, T, T, E, F], [T, T, F, F, E, T, F, T, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1281 (And.intro z_732 trivial))
    trivial

theorem n_198 : UpperZero (tf [T, T, F, F, E, T, F, E, T, F, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, E, T, F, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_575)) [[T, T, F, F, E, E, F, T, T, F, T, F, E], [T, T, F, F, E, T, F, E, T, F, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1282 (And.intro z_861 trivial))
    trivial

theorem n_199 : UpperZero (tf [T, T, F, F, E, T, F, T, F, E, E, T, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, F, E, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_732)) [[T, T, F, F, E, T, F, E, F, T, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1284 trivial)
    trivial

theorem n_200 : UpperZero (tf [T, T, F, F, E, T, F, T, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, E, F, T, E, F] (lfZero_of_reply [T, T, F, F, E, T, F, T, E, F, T, E, F] [T, T, F, F, E, T, F, T, F, E, T, E, F] (by decide +kernel) n_197) [] [([T, T, F, F, E, T, F, E, T, F, T, E, F], [T, T, F, F, E, T, F, E, T, F, T, F, E]), ([T, T, F, F, E, T, F, T, E, F, E, T, F], [T, T, F, F, E, T, F, T, F, E, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_198 (And.intro n_199 trivial))

theorem n_201 : UpperZero (tf [T, T, F, F, E, T, F, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, E, T, E, F, F] (lfZero_of_reply [T, T, F, F, E, T, F, T, E, T, E, F, F] [T, T, F, F, E, T, F, T, E, T, F, E, F] (by decide +kernel) n_194) [] [([T, T, F, F, E, T, F, E, T, T, E, F, F], [T, T, F, F, E, T, F, E, T, T, F, E, F]), ([T, T, F, F, E, T, F, T, E, E, T, F, F], [T, T, F, F, E, T, F, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_196 (And.intro n_200 trivial))

theorem n_202 : UpperZero (tf [T, T, F, F, T, F, E, E, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, E, T, F, T, E, F] (lfZero_of_reply [T, T, F, F, T, F, E, E, T, F, T, E, F] [T, T, F, F, T, F, E, E, T, F, T, F, E] (by decide +kernel) n_187) [[T, T, F, F, T, F, E, E, T, F, E, T, F]] [([T, T, F, F, E, F, T, E, T, F, T, E, F], [T, T, F, F, E, F, T, F, T, E, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_578 trivial)
    (And.intro n_71 trivial)

theorem n_203 : UpperZero (tf [T, T, F, F, T, F, E, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, T, E, E, T, F, F] (lfZero_of_reply [T, T, F, F, T, F, E, T, E, E, T, F, F] [T, T, F, F, T, F, E, T, E, F, T, E, F] (by decide +kernel) n_189) [[T, T, F, F, E, F, T, T, E, E, T, F, F]] [([T, T, F, F, T, F, E, E, T, E, T, F, F], [T, T, F, F, T, F, E, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1285 trivial)
    (And.intro n_202 trivial)

theorem n_204 : UpperZero (tf [T, T, F, F, T, F, E, E, T, F, E, T, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, E, T, F, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_578)) [[T, T, F, F, E, F, T, E, T, F, E, T, F], [T, T, F, F, T, F, E, E, E, F, T, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_505 (And.intro z_1286 trivial))
    trivial

theorem n_205 : UpperZero (tf [T, T, F, F, T, E, F, E, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, F, E, T, F, T, E, F] (lfZero_of_reply [T, T, F, F, T, E, F, E, T, F, T, E, F] [T, T, F, F, T, F, E, E, T, F, T, E, F] (by decide +kernel) n_202) [] [([T, T, F, F, E, T, F, E, T, F, T, E, F], [T, T, F, F, E, T, F, E, T, F, T, F, E]), ([T, T, F, F, T, E, F, E, T, F, E, T, F], [T, T, F, F, T, F, E, E, T, F, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_198 (And.intro n_204 trivial))

theorem n_206 : UpperZero (tf [T, T, F, F, T, E, F, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, F, T, E, E, T, F, F] (lfZero_of_reply [T, T, F, F, T, E, F, T, E, E, T, F, F] [T, T, F, F, T, F, E, T, E, E, T, F, F] (by decide +kernel) n_203) [] [([T, T, F, F, E, T, F, T, E, E, T, F, F], [T, T, F, F, E, T, F, T, E, F, T, E, F]), ([T, T, F, F, T, E, F, E, T, E, T, F, F], [T, T, F, F, T, E, F, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_200 (And.intro n_205 trivial))

theorem n_207 : UpperZero (tf [T, T, F, F, T, E, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, E, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, E, E, T, F, T, E, F, F] [T, T, F, F, T, E, F, T, E, T, E, F, F] (by decide +kernel) n_191) [] [([T, T, F, F, E, T, E, T, F, T, E, F, F], [T, T, F, F, E, T, F, T, E, T, E, F, F]), ([T, T, F, F, T, E, E, T, F, E, T, F, F], [T, T, F, F, T, E, F, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_201 (And.intro n_206 trivial))

theorem n_208 : UpperZero (tf [T, T, F, E, T, F, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, F, E, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, E, T, F, E, T, F, T, E, F, F] [T, T, F, F, T, E, E, T, F, T, E, F, F] (by decide +kernel) n_207) [[T, E, F, T, T, F, E, T, F, T, E, F, F], [T, T, F, E, E, F, T, T, F, T, E, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1229 (And.intro z_1287 (And.intro z_724 trivial)))
    trivial

theorem n_209 : UpperZero (tf [T, T, F, E, T, T, F, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, E, F, T, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, E, F, T, E, F, F] [T, T, F, E, T, T, F, F, E, T, E, F, F] (by decide +kernel) n_181) [[T, E, F, T, T, T, F, E, F, T, E, F, F]] [([T, T, F, E, T, E, F, T, F, T, E, F, F], [T, T, F, E, T, F, E, T, F, T, E, F, F]), ([T, T, F, E, T, T, F, E, F, E, T, F, F], [T, T, F, E, T, T, F, F, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1230 trivial)
    (And.intro n_208 (And.intro n_86 trivial))

theorem n_210 : UpperZero (tf [T, F, E, T, T, T, F, F, E, T, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, E, T, F, E, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, E, T, F, E, F] [T, F, E, T, T, T, F, F, F, T, E, E, F] (by decide +kernel) n_178) [[E, F, T, T, T, T, F, F, E, T, F, E, F], [T, F, E, T, T, T, F, F, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1288 (And.intro z_909 trivial))
    trivial

theorem n_211 : UpperZero (tf [T, F, E, T, T, T, F, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, F, E, T, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, F, E, T, E, F, F] [T, F, E, T, T, T, F, F, E, T, F, E, F] (by decide +kernel) n_210) [[E, F, T, T, T, T, F, F, E, T, E, F, F]] [([T, F, E, T, T, T, F, F, E, E, T, F, F], [T, F, E, T, T, T, F, F, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1289 trivial)
    (And.intro n_57 trivial)

theorem n_212 : UpperZero (tf [T, F, E, T, T, F, F, T, F, T, E, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1293)) [[E, F, T, T, T, F, F, T, F, T, E, E, F]] [([T, F, E, T, T, F, F, T, F, E, T, E, F], [T, F, E, T, T, F, F, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1294 trivial)
    (And.intro n_44 trivial)

theorem n_213 : UpperZero (tf [T, F, E, T, T, F, F, T, E, T, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, E, T, F, E, F] (lfZero_of_reply [T, F, E, T, T, F, F, T, E, T, F, E, F] [T, F, E, T, T, F, F, T, F, T, E, E, F] (by decide +kernel) n_212) [[E, F, T, T, T, F, F, T, E, T, F, E, F], [T, F, E, T, T, F, F, E, T, T, F, E, F], [T, F, E, T, T, F, F, T, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1295 (And.intro z_553 (And.intro z_907 trivial)))
    trivial

theorem n_214 : UpperZero (tf [T, F, E, T, T, F, F, E, T, T, F, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, E, T, T, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1299)) [[E, F, T, T, T, F, F, E, T, T, F, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1300 trivial)
    trivial

theorem n_215 : UpperZero (tf [T, F, E, T, T, F, F, E, T, T, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, E, T, T, F, E, F] (lfZero_of_reply [T, F, E, T, T, F, F, E, T, T, F, E, F] [T, F, E, T, T, F, F, E, T, T, F, F, E] (by decide +kernel) n_214) [[E, F, T, T, T, F, F, E, T, T, F, E, F], [T, F, E, T, T, F, F, E, T, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1296 (And.intro z_820 trivial))
    trivial

theorem n_216 : UpperZero (tf [T, F, E, T, T, F, F, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, F, T, E, T, E, F, F] (lfZero_of_reply [T, F, E, T, T, F, F, T, E, T, E, F, F] [T, F, E, T, T, F, F, T, E, T, F, E, F] (by decide +kernel) n_213) [[E, F, T, T, T, F, F, T, E, T, E, F, F]] [([T, F, E, T, T, F, F, E, T, T, E, F, F], [T, F, E, T, T, F, F, E, T, T, F, E, F]), ([T, F, E, T, T, F, F, T, E, E, T, F, F], [T, F, E, T, T, F, F, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1297 trivial)
    (And.intro n_215 (And.intro n_48 trivial))

theorem n_217 : UpperZero (tf [T, F, E, T, T, F, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, F, E, T, F, T, E, F, F] (lfZero_of_reply [T, F, E, T, T, F, E, T, F, T, E, F, F] [T, F, E, T, T, F, F, T, E, T, E, F, F] (by decide +kernel) n_216) [[E, F, T, T, T, F, E, T, F, T, E, F, F], [T, F, E, T, E, F, T, T, F, T, E, F, F]] [([T, F, E, T, T, F, E, T, F, E, T, F, F], [T, F, E, T, T, F, F, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1290 (And.intro z_1228 trivial))
    (And.intro n_50 trivial)

theorem n_218 : UpperZero (tf [T, F, E, T, T, T, F, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, F, E, F, T, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, F, E, F, T, E, F, F] [T, F, E, T, T, T, F, F, E, T, E, F, F] (by decide +kernel) n_211) [[E, F, T, T, T, T, F, E, F, T, E, F, F]] [([T, F, E, T, T, E, F, T, F, T, E, F, F], [T, F, E, T, T, F, E, T, F, T, E, F, F]), ([T, F, E, T, T, T, F, E, F, E, T, F, F], [T, F, E, T, T, T, F, F, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1291 trivial)
    (And.intro n_217 (And.intro n_58 trivial))

theorem n_219 : UpperZero (tf [E, T, F, T, T, F, F, T, F, E, T, F, E]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, T, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1324)) [[E, T, F, T, T, F, F, E, F, T, T, F, E], [E, T, F, T, T, F, F, T, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1328 (And.intro z_1329 trivial))
    trivial

theorem n_220 : UpperZero (tf [E, T, F, T, T, F, F, T, F, T, E, E, F]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, T, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1325)) [] [([E, T, F, T, T, F, F, T, F, E, T, E, F], [E, T, F, T, T, F, F, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_219 trivial)

theorem n_221 : UpperZero (tf [E, T, F, T, T, F, F, T, E, T, F, E, F]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, T, E, T, F, E, F] (lfZero_of_reply [E, T, F, T, T, F, F, T, E, T, F, E, F] [E, T, F, T, T, F, F, T, F, T, E, E, F] (by decide +kernel) n_220) [[E, T, F, T, T, F, F, E, T, T, F, E, F], [E, T, F, T, T, F, F, T, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1188 (And.intro z_1330 trivial))
    trivial

theorem n_222 : UpperZero (tf [E, T, F, T, T, F, F, E, T, T, F, F, E]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, E, T, T, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1331)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_223 : UpperZero (tf [E, T, F, T, T, F, F, E, T, T, F, E, F]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, E, T, T, F, E, F] (lfZero_of_reply [E, T, F, T, T, F, F, E, T, T, F, E, F] [E, T, F, T, T, F, F, E, T, T, F, F, E] (by decide +kernel) n_222) [[E, T, F, T, T, F, F, E, T, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1333 trivial)
    trivial

theorem n_224 : UpperZero (tf [E, T, F, T, T, F, F, T, F, E, T, E, F]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, T, F, E, T, E, F] (lfZero_of_reply [E, T, F, T, T, F, F, T, F, E, T, E, F] [E, T, F, T, T, F, F, T, F, E, T, F, E] (by decide +kernel) n_219) [[E, T, F, T, T, F, F, E, F, T, T, E, F], [E, T, F, T, T, F, F, T, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1334 (And.intro z_1196 trivial))
    trivial

theorem n_225 : UpperZero (tf [E, T, F, T, T, F, F, E, T, F, T, F, E]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, E, T, F, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1192)) [[E, T, F, T, T, F, F, E, T, F, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1336 trivial)
    trivial

theorem n_226 : UpperZero (tf [E, T, F, T, T, F, F, T, F, E, E, T, F]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, T, F, E, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1196)) [[E, T, F, T, T, F, F, E, F, T, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1338 trivial)
    trivial

theorem n_227 : UpperZero (tf [E, T, F, T, T, F, F, T, E, F, T, E, F]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, T, E, F, T, E, F] (lfZero_of_reply [E, T, F, T, T, F, F, T, E, F, T, E, F] [E, T, F, T, T, F, F, T, F, E, T, E, F] (by decide +kernel) n_224) [] [([E, T, F, T, T, F, F, E, T, F, T, E, F], [E, T, F, T, T, F, F, E, T, F, T, F, E]), ([E, T, F, T, T, F, F, T, E, F, E, T, F], [E, T, F, T, T, F, F, T, F, E, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_225 (And.intro n_226 trivial))

theorem n_228 : UpperZero (tf [E, T, F, T, T, F, F, T, E, T, E, F, F]) :=
  upperZero_of_pairs [E, T, F, T, T, F, F, T, E, T, E, F, F] (lfZero_of_reply [E, T, F, T, T, F, F, T, E, T, E, F, F] [E, T, F, T, T, F, F, T, E, T, F, E, F] (by decide +kernel) n_221) [] [([E, T, F, T, T, F, F, E, T, T, E, F, F], [E, T, F, T, T, F, F, E, T, T, F, E, F]), ([E, T, F, T, T, F, F, T, E, E, T, F, F], [E, T, F, T, T, F, F, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_223 (And.intro n_227 trivial))

theorem n_229 : UpperZero (tf [T, F, E, T, F, E, T, T, F, T, F, F, E]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, F, T, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_957)) [[E, F, T, T, F, E, T, T, F, T, F, F, E], [T, F, E, E, F, T, T, T, F, T, F, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1342 (And.intro z_1343 trivial))
    trivial

theorem n_230 : UpperZero (tf [T, F, E, T, F, E, T, T, F, T, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, F, T, F, E, F] (lfZero_of_reply [T, F, E, T, F, E, T, T, F, T, F, E, F] [T, F, E, T, F, E, T, T, F, T, F, F, E] (by decide +kernel) n_229) [[E, F, T, T, F, E, T, T, F, T, F, E, F], [T, F, E, E, F, T, T, T, F, T, F, E, F], [T, F, E, T, F, E, T, T, F, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1084 (And.intro z_1344 (And.intro z_974 trivial)))
    trivial

theorem n_231 : UpperZero (tf [T, F, E, T, F, E, T, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, F, E, T, T, F, T, E, F, F] (lfZero_of_reply [T, F, E, T, F, E, T, T, F, T, E, F, F] [T, F, E, T, F, E, T, T, F, T, F, E, F] (by decide +kernel) n_230) [[E, F, T, T, F, E, T, T, F, T, E, F, F], [T, F, E, E, F, T, T, T, F, T, E, F, F]] [([T, F, E, T, F, E, T, T, F, E, T, F, F], [T, F, E, T, F, E, T, T, F, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1209 (And.intro z_1345 trivial))
    (And.intro n_40 trivial)

theorem n_232 : UpperZero (tf [T, F, E, E, T, F, T, T, F, T, F, F, E]) :=
  upperZero_of_pairs [T, F, E, E, T, F, T, T, F, T, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1086)) [[E, F, T, E, T, F, T, T, F, T, F, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1354 trivial)
    trivial

theorem n_233 : UpperZero (tf [T, F, E, E, T, F, T, T, F, T, F, E, F]) :=
  upperZero_of_pairs [T, F, E, E, T, F, T, T, F, T, F, E, F] (lfZero_of_reply [T, F, E, E, T, F, T, T, F, T, F, E, F] [T, F, E, E, T, F, T, T, F, T, F, F, E] (by decide +kernel) n_232) [[E, F, T, E, T, F, T, T, F, T, F, E, F], [T, F, E, E, T, F, T, T, F, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1351 (And.intro z_1357 trivial))
    trivial

theorem n_234 : UpperZero (tf [T, F, E, T, E, F, T, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, E, F, T, T, F, T, E, F, F] (lfZero_of_reply [T, F, E, T, E, F, T, T, F, T, E, F, F] [T, F, E, T, F, E, T, T, F, T, E, F, F] (by decide +kernel) n_231) [[E, F, T, T, E, F, T, T, F, T, E, F, F]] [([T, F, E, E, T, F, T, T, F, T, E, F, F], [T, F, E, E, T, F, T, T, F, T, F, E, F]), ([T, F, E, T, E, F, T, T, F, E, T, F, F], [T, F, E, T, F, E, T, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1352 trivial)
    (And.intro n_233 (And.intro n_42 trivial))

theorem n_235 : UpperZero (tf [T, E, F, T, T, F, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, E, F, T, T, F, E, T, F, T, E, F, F] (lfZero_of_reply [T, E, F, T, T, F, E, T, F, T, E, F, F] [T, F, E, T, T, F, E, T, F, T, E, F, F] (by decide +kernel) n_217) [] [([E, T, F, T, T, F, E, T, F, T, E, F, F], [E, T, F, T, T, F, F, T, E, T, E, F, F]), ([T, E, F, T, E, F, T, T, F, T, E, F, F], [T, F, E, T, E, F, T, T, F, T, E, F, F]), ([T, E, F, T, T, F, E, T, F, E, T, F, F], [T, F, E, T, T, F, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_228 (And.intro n_234 (And.intro n_53 trivial)))

theorem n_236 : UpperZero (tf [T, E, F, T, T, T, F, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, E, F, T, T, T, F, E, F, T, E, F, F] (lfZero_of_reply [T, E, F, T, T, T, F, E, F, T, E, F, F] [T, F, E, T, T, T, F, E, F, T, E, F, F] (by decide +kernel) n_218) [[E, T, F, T, T, T, F, E, F, T, E, F, F]] [([T, E, F, T, T, E, F, T, F, T, E, F, F], [T, E, F, T, T, F, E, T, F, T, E, F, F]), ([T, E, F, T, T, T, F, E, F, E, T, F, F], [T, F, E, T, T, T, F, E, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1321 trivial)
    (And.intro n_235 (And.intro n_59 trivial))

theorem n_237 : UpperZero (tf [T, T, F, F, E, E, T, T, F, T, F, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, F, T, F, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1358)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_238 : UpperZero (tf [T, T, F, F, E, E, T, T, F, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, F, T, F, E, F] (lfZero_of_reply [T, T, F, F, E, E, T, T, F, T, F, E, F] [T, T, F, F, E, E, T, T, F, T, F, F, E] (by decide +kernel) n_237) [[T, T, F, F, E, E, T, T, F, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_914 trivial)
    trivial

theorem n_239 : UpperZero (tf [T, T, F, F, E, T, F, E, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, E, T, F, T, E, F] (lfZero_of_reply [T, T, F, F, E, T, F, E, T, F, T, E, F] [T, T, F, F, E, T, F, E, T, F, T, F, E] (by decide +kernel) n_198) [[T, T, F, F, E, E, F, T, T, F, T, E, F], [T, T, F, F, E, T, F, E, T, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1359 (And.intro z_562 trivial))
    trivial

theorem n_240 : UpperZero (tf [T, T, F, F, E, T, F, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, F, T, E, E, T, F, F] (lfZero_of_reply [T, T, F, F, E, T, F, T, E, E, T, F, F] [T, T, F, F, E, T, F, T, E, F, T, E, F] (by decide +kernel) n_200) [] [([T, T, F, F, E, T, F, E, T, E, T, F, F], [T, T, F, F, E, T, F, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_239 trivial)

theorem n_241 : UpperZero (tf [T, T, F, F, E, T, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, E, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, F, E, T, E, T, F, T, E, F, F] [T, T, F, F, E, T, F, T, E, T, E, F, F] (by decide +kernel) n_201) [] [([T, T, F, F, E, E, T, T, F, T, E, F, F], [T, T, F, F, E, E, T, T, F, T, F, E, F]), ([T, T, F, F, E, T, E, T, F, E, T, F, F], [T, T, F, F, E, T, F, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_238 (And.intro n_240 trivial))

theorem n_242 : UpperZero (tf [T, F, E, T, F, T, F, T, F, E, T, F, E]) :=
  upperZero_of_pairs [T, F, E, T, F, T, F, T, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1371)) [[E, F, T, T, F, T, F, T, F, E, T, F, E], [T, F, E, T, F, T, F, E, F, T, T, F, E], [T, F, E, T, F, T, F, T, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1383 (And.intro z_1424 (And.intro z_1425 trivial)))
    trivial

theorem n_243 : UpperZero (tf [T, F, E, T, F, T, F, T, F, T, E, E, F]) :=
  upperZero_of_pairs [T, F, E, T, F, T, F, T, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1372)) [[E, F, T, T, F, T, F, T, F, T, E, E, F]] [([T, F, E, T, F, T, F, T, F, E, T, E, F], [T, F, E, T, F, T, F, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1384 trivial)
    (And.intro n_242 trivial)

theorem n_244 : UpperZero (tf [T, F, E, T, F, T, F, T, E, T, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, F, T, F, T, E, T, F, E, F] (lfZero_of_reply [T, F, E, T, F, T, F, T, E, T, F, E, F] [T, F, E, T, F, T, F, T, F, T, E, E, F] (by decide +kernel) n_243) [[E, F, T, T, F, T, F, T, E, T, F, E, F], [T, F, E, T, F, T, F, E, T, T, F, E, F], [T, F, E, T, F, T, F, T, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1428 (And.intro z_1430 (And.intro z_963 trivial)))
    trivial

theorem n_245 : UpperZero (tf [T, F, E, T, F, T, F, E, T, F, E, T, F]) :=
  upperZero_of_pairs [T, F, E, T, F, T, F, E, T, F, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_962)) [[E, F, T, T, F, T, F, E, T, F, E, T, F], [T, F, E, T, F, E, F, T, T, F, E, T, F], [T, F, E, T, F, T, F, E, E, F, T, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1457 (And.intro z_1473 (And.intro z_1474 trivial)))
    trivial

theorem n_246 : UpperZero (tf [T, F, E, T, F, T, F, T, E, E, F, T, F]) :=
  upperZero_of_pairs [T, F, E, T, F, T, F, T, E, E, F, T, F] ((lfZero_tf_iff _).2 (Or.inl z_963)) [[E, F, T, T, F, T, F, T, E, E, F, T, F]] [([T, F, E, T, F, T, F, E, T, E, F, T, F], [T, F, E, T, F, T, F, E, T, F, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1458 trivial)
    (And.intro n_245 trivial)

theorem n_247 : UpperZero (tf [T, F, E, T, F, T, E, T, F, T, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, F, T, E, T, F, T, F, E, F] (lfZero_of_reply [T, F, E, T, F, T, E, T, F, T, F, E, F] [T, F, E, T, F, T, F, T, E, T, F, E, F] (by decide +kernel) n_244) [[E, F, T, T, F, T, E, T, F, T, F, E, F]] [([T, F, E, T, F, E, T, T, F, T, F, E, F], [T, F, E, T, F, E, T, T, F, T, F, F, E]), ([T, F, E, T, F, T, E, T, F, E, F, T, F], [T, F, E, T, F, T, F, T, E, E, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1459 trivial)
    (And.intro n_229 (And.intro n_246 trivial))

theorem n_248 : UpperZero (tf [T, E, F, T, F, T, E, T, F, T, F, E, F]) :=
  upperZero_of_pairs [T, E, F, T, F, T, E, T, F, T, F, E, F] (lfZero_of_reply [T, E, F, T, F, T, E, T, F, T, F, E, F] [T, F, E, T, F, T, E, T, F, T, F, E, F] (by decide +kernel) n_247) [[E, T, F, T, F, T, E, T, F, T, F, E, F], [T, E, F, T, F, T, E, T, F, E, F, T, F]] [([T, E, F, T, F, E, T, T, F, T, F, E, F], [T, F, E, T, F, E, T, T, F, T, F, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1309 (And.intro z_1477 trivial))
    (And.intro n_230 trivial)

theorem n_249 : UpperZero (tf [T, T, F, F, E, T, E, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, E, T, F, E, T, F, F] (lfZero_of_reply [T, T, F, F, E, T, E, T, F, E, T, F, F] [T, T, F, F, E, T, F, T, E, E, T, F, F] (by decide +kernel) n_240) [[T, T, F, F, E, T, E, E, F, T, T, F, F]] [([T, T, F, F, E, E, T, T, F, E, T, F, F], [T, T, F, F, E, E, T, T, F, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_515 trivial)
    (And.intro n_67 trivial)

theorem n_250 : UpperZero (tf [T, T, F, E, F, T, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, F, T, E, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, E, F, T, E, T, F, T, E, F, F] [T, T, F, F, E, T, E, T, F, T, E, F, F] (by decide +kernel) n_241) [[T, T, F, E, F, E, T, T, F, T, E, F, F]] [([T, E, F, T, F, T, E, T, F, T, E, F, F], [T, E, F, T, F, T, E, T, F, T, F, E, F]), ([T, T, F, E, F, T, E, T, F, E, T, F, F], [T, T, F, F, E, T, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1480 trivial)
    (And.intro n_248 (And.intro n_249 trivial))

theorem n_251 : UpperZero (tf [T, T, F, E, T, E, F, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, E, F, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, E, T, E, F, T, F, T, E, F, F] [T, T, F, E, T, F, E, T, F, T, E, F, F] (by decide +kernel) n_208) [] [([T, E, F, T, T, E, F, T, F, T, E, F, F], [T, E, F, T, T, F, E, T, F, T, E, F, F]), ([T, T, F, E, E, T, F, T, F, T, E, F, F], [T, T, F, E, F, T, E, T, F, T, E, F, F]), ([T, T, F, E, T, E, F, T, F, E, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_235 (And.intro n_250 (And.intro n_81 trivial)))

theorem n_252 : UpperZero (tf [T, T, F, E, T, T, F, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, F, E, E, T, F, F, F] (lfZero_of_reply [T, T, F, E, T, T, F, E, E, T, F, F, F] [T, T, F, E, T, T, F, E, F, T, E, F, F] (by decide +kernel) n_209) [] [([T, E, F, T, T, T, F, E, E, T, F, F, F], [T, E, F, T, T, T, F, E, F, T, E, F, F]), ([T, T, F, E, T, E, F, T, E, T, F, F, F], [T, T, F, E, T, E, F, T, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_236 (And.intro n_251 trivial))

theorem n_253 : UpperZero (tf [T, E, T, F, T, F, E, T, F, T, F, E, F]) :=
  upperZero_of_pairs [T, E, T, F, T, F, E, T, F, T, F, E, F] (lfZero_of_mirror_dec [T, E, T, F, T, F, E, T, F, T, F, E, F] (by decide +kernel)) [[E, T, T, F, T, F, E, T, F, T, F, E, F], [T, E, T, F, E, F, T, T, F, T, F, E, F], [T, E, T, F, T, F, E, T, F, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1486 (And.intro z_1493 (And.intro z_1495 trivial)))
    trivial

theorem n_254 : UpperZero (tf [T, T, F, F, E, E, T, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, E, T, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, F, E, E, T, T, F, T, E, F, F] [T, T, F, F, E, E, T, T, F, T, F, E, F] (by decide +kernel) n_238) [] [([T, T, F, F, E, E, T, T, F, E, T, F, F], [T, T, F, F, E, E, T, T, F, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_67 trivial)

theorem n_255 : UpperZero (tf [T, T, F, E, F, E, T, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, F, E, T, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, E, F, E, T, T, F, T, E, F, F] [T, T, F, F, E, E, T, T, F, T, E, F, F] (by decide +kernel) n_254) [] [([T, E, F, T, F, E, T, T, F, T, E, F, F], [T, F, E, T, F, E, T, T, F, T, E, F, F]), ([T, T, F, E, F, E, T, T, F, E, T, F, F], [T, T, F, F, E, E, T, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_231 (And.intro n_68 trivial))

theorem n_256 : UpperZero (tf [T, T, F, E, E, F, T, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, E, F, T, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, E, E, F, T, T, F, T, E, F, F] [T, T, F, E, F, E, T, T, F, T, E, F, F] (by decide +kernel) n_255) [] [([T, E, F, T, E, F, T, T, F, T, E, F, F], [T, F, E, T, E, F, T, T, F, T, E, F, F]), ([T, T, F, E, E, F, T, T, F, E, T, F, F], [T, T, F, E, F, E, T, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_234 (And.intro n_79 trivial))

theorem n_257 : UpperZero (tf [T, T, E, F, T, F, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, E, F, T, F, E, T, F, T, E, F, F] (lfZero_of_mirror_dec [T, T, E, F, T, F, E, T, F, T, E, F, F] (by decide +kernel)) [] [([T, E, T, F, T, F, E, T, F, T, E, F, F], [T, E, T, F, T, F, E, T, F, T, F, E, F]), ([T, T, E, F, E, F, T, T, F, T, E, F, F], [T, T, F, E, E, F, T, T, F, T, E, F, F]), ([T, T, E, F, T, F, E, T, F, E, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_253 (And.intro n_256 (And.intro n_81 trivial)))

theorem n_258 : UpperZero (tf [T, T, T, F, F, E, E, E, T, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, E, T, T, F, F, F] (lfZero_of_mirror_dec [T, T, T, F, F, E, E, E, T, T, F, F, F] (by decide +kernel)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_259 : UpperZero (tf [T, T, T, F, E, F, E, T, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, F, E, T, E, T, F, F, F] (lfZero_of_mirror_dec [T, T, T, F, E, F, E, T, E, T, F, F, F] (by decide +kernel)) [] [([T, T, E, F, T, F, E, T, E, T, F, F, F], [T, T, E, F, T, F, E, T, F, T, E, F, F]), ([T, T, T, F, E, F, E, E, T, T, F, F, F], [T, T, T, F, F, E, E, E, T, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_257 (And.intro n_258 trivial))

theorem n_260 : UpperZero (tf [T, T, T, F, E, T, F, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, F, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, E, T, F, E, E, T, F, F, F] [T, T, T, F, F, T, E, E, E, T, F, F, F] (by decide +kernel) n_176) [] [([T, T, E, F, T, T, F, E, E, T, F, F, F], [T, T, F, E, T, T, F, E, E, T, F, F, F]), ([T, T, T, F, E, E, F, T, E, T, F, F, F], [T, T, T, F, E, F, E, T, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_252 (And.intro n_259 trivial))

theorem n_261 : UpperZero (tf [T, T, T, F, T, E, E, F, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, E, E, F, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, T, E, E, F, E, T, F, F, F] [T, T, T, F, T, E, F, E, E, T, F, F, F] (by decide +kernel) n_177) [] [([T, T, T, F, E, T, E, F, E, T, F, F, F], [T, T, T, F, E, T, F, E, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_260 trivial)

theorem n_262 : UpperZero (tf [T, T, T, F, T, E, E, T, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, T, E, E, T, F, E, F, F, F] (lfZero_of_reply [T, T, T, F, T, E, E, T, F, E, F, F, F] [T, T, T, F, T, E, F, T, E, E, F, F, F] (by decide +kernel) n_135) [] [([T, T, T, F, E, T, E, T, F, E, F, F, F], [T, T, T, F, E, T, F, T, E, E, F, F, F]), ([T, T, T, F, T, E, E, E, F, T, F, F, F], [T, T, T, F, T, E, E, F, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_160 (And.intro n_261 trivial))

theorem n_263 : UpperZero (tf [T, T, T, E, T, F, T, E, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, T, F, T, E, F, E, F, F, F] (lfZero_of_reply [T, T, T, E, T, F, T, E, F, E, F, F, F] [T, T, T, F, T, E, T, E, F, E, F, F, F] (by decide +kernel) n_124) [[T, T, E, T, T, F, T, E, F, E, F, F, F]] [([T, T, T, E, T, F, E, T, F, E, F, F, F], [T, T, T, F, T, E, E, T, F, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_42 trivial)
    (And.intro n_262 trivial)

theorem n_264 : UpperZero (tf [T, T, T, E, T, T, E, F, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, T, T, E, F, F, E, F, F, F] (lfZero_of_mirror_dec [T, T, T, E, T, T, E, F, F, E, F, F, F] (by decide +kernel)) [[T, T, E, T, T, T, E, F, F, E, F, F, F]] [([T, T, T, E, T, E, T, F, F, E, F, F, F], [T, T, T, E, T, F, T, E, F, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_43 trivial)
    (And.intro n_263 trivial)

theorem n_265 : UpperZero (tf [T, T, T, T, F, F, T, F, F, F, E, E, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, F, F, F, E, E, E] ((lfZero_tf_iff _).2 (Or.inl z_1496)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_266 : UpperZero (tf [T, T, T, T, F, F, T, F, F, E, F, E, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, F, F, E, F, E, E] (lfZero_of_reply [T, T, T, T, F, F, T, F, F, E, F, E, E] [T, T, T, T, F, F, T, F, F, F, E, E, E] (by decide +kernel) n_265) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_267 : UpperZero (tf [T, T, T, T, F, F, T, F, F, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, F, F, E, E, F, E] (lfZero_of_reply [T, T, T, T, F, F, T, F, F, E, E, F, E] [T, T, T, T, F, F, T, F, F, E, F, E, E] (by decide +kernel) n_266) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_268 : UpperZero (tf [T, T, T, T, F, F, T, F, F, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, F, F, E, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, T, F, F, E, E, E, F] [T, T, T, T, F, F, T, F, F, E, E, F, E] (by decide +kernel) n_267) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_269 : UpperZero (tf [T, T, T, T, F, F, T, F, E, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, F, E, F, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, T, F, E, F, E, E, F] [T, T, T, T, F, F, T, F, F, E, E, E, F] (by decide +kernel) n_268) [[T, T, T, T, F, F, E, F, T, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1499 trivial)
    trivial

theorem n_270 : UpperZero (tf [T, T, T, T, F, F, T, F, E, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, F, E, E, F, E, F] (lfZero_of_reply [T, T, T, T, F, F, T, F, E, E, F, E, F] [T, T, T, T, F, F, T, F, E, F, E, E, F] (by decide +kernel) n_269) [[T, T, T, T, F, F, E, F, T, E, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1502 trivial)
    trivial

theorem n_271 : UpperZero (tf [T, T, T, T, F, F, T, F, E, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, F, E, E, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, T, F, E, E, E, F, F] [T, T, T, T, F, F, T, F, E, E, F, E, F] (by decide +kernel) n_270) [[T, T, T, T, F, F, E, F, T, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1504 trivial)
    trivial

theorem n_272 : UpperZero (tf [T, T, T, T, F, F, T, E, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, E, F, E, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, T, E, F, E, E, F, F] [T, T, T, T, F, F, T, F, E, E, E, F, F] (by decide +kernel) n_271) [[T, T, T, T, F, F, E, T, F, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1507 trivial)
    trivial

theorem n_273 : UpperZero (tf [T, T, T, T, F, F, T, E, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, E, E, F, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, T, E, E, F, E, F, F] [T, T, T, T, F, F, T, E, F, E, E, F, F] (by decide +kernel) n_272) [[T, T, T, T, F, F, E, T, E, F, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1508 trivial)
    trivial

theorem n_274 : UpperZero (tf [T, T, T, T, F, F, T, E, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, T, E, E, E, F, F, F] (lfZero_of_reply [T, T, T, T, F, F, T, E, E, E, F, F, F] [T, T, T, T, F, F, T, E, E, F, E, F, F] (by decide +kernel) n_273) [[T, T, T, T, F, F, E, T, E, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1511 trivial)
    trivial

theorem n_275 : UpperZero (tf [T, T, T, T, F, E, T, F, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, T, F, E, E, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, T, F, E, E, F, F, F] [T, T, T, T, F, F, T, E, E, E, F, F, F] (by decide +kernel) n_274) [[T, T, T, E, F, T, T, F, E, E, F, F, F], [T, T, T, T, F, E, E, F, T, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1539 (And.intro z_1545 trivial))
    trivial

theorem n_276 : UpperZero (tf [T, T, T, F, E, T, T, F, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, F, E, E, F, F, F] (lfZero_of_reply [T, T, T, F, E, T, T, F, E, E, F, F, F] [T, T, T, F, E, T, T, F, E, F, E, F, F] (by decide +kernel) n_112) [[T, T, E, F, T, T, T, F, E, E, F, F, F], [T, T, T, F, E, T, E, F, T, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1559 (And.intro z_1538 trivial))
    trivial

theorem n_277 : UpperZero (tf [T, T, F, E, T, T, T, F, F, F, E, F, E]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, F, F, F, E, F, E] (lfZero_of_reply [T, T, F, E, T, T, T, F, F, F, E, F, E] [T, T, F, E, T, T, T, F, F, F, F, E, E] (by decide +kernel) n_11) [[T, E, F, T, T, T, T, F, F, F, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1561 trivial)
    trivial

theorem n_278 : UpperZero (tf [T, T, F, E, T, T, T, F, F, F, E, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, F, F, F, E, E, F] (lfZero_of_reply [T, T, F, E, T, T, T, F, F, F, E, E, F] [T, T, F, E, T, T, T, F, F, F, E, F, E] (by decide +kernel) n_277) [[T, E, F, T, T, T, T, F, F, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1564 trivial)
    trivial

theorem n_279 : UpperZero (tf [T, T, F, E, T, T, T, F, F, E, F, E, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, F, F, E, F, E, F] (lfZero_of_reply [T, T, F, E, T, T, T, F, F, E, F, E, F] [T, T, F, E, T, T, T, F, F, F, E, E, F] (by decide +kernel) n_278) [[T, E, F, T, T, T, T, F, F, E, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1566 trivial)
    trivial

theorem n_280 : UpperZero (tf [T, T, F, E, T, T, T, F, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, F, F, E, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, T, F, F, E, E, F, F] [T, T, F, E, T, T, T, F, F, E, F, E, F] (by decide +kernel) n_279) [[T, E, F, T, T, T, T, F, F, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1568 trivial)
    trivial

theorem n_281 : UpperZero (tf [T, T, F, E, T, T, T, F, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, F, E, F, E, F, F] (lfZero_of_reply [T, T, F, E, T, T, T, F, E, F, E, F, F] [T, T, F, E, T, T, T, F, F, E, E, F, F] (by decide +kernel) n_280) [[T, E, F, T, T, T, T, F, E, F, E, F, F]] [([T, T, F, E, T, T, E, F, T, F, E, F, F], [T, T, F, E, T, T, F, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1580 trivial)
    (And.intro n_88 trivial)

theorem n_282 : UpperZero (tf [T, T, F, E, T, T, T, F, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, F, E, E, F, F, F] (lfZero_of_reply [T, T, F, E, T, T, T, F, E, E, F, F, F] [T, T, F, E, T, T, T, F, E, F, E, F, F] (by decide +kernel) n_281) [[T, E, F, T, T, T, T, F, E, E, F, F, F], [T, T, F, E, T, T, E, F, T, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1596 (And.intro z_1537 trivial))
    trivial

theorem n_283 : UpperZero (tf [T, F, E, T, T, T, T, F, F, F, E, F, E]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, F, F, F, E, F, E] (lfZero_of_reply [T, F, E, T, T, T, T, F, F, F, E, F, E] [T, F, E, T, T, T, T, F, F, F, F, E, E] (by decide +kernel) n_10) [[E, F, T, T, T, T, T, F, F, F, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1597 trivial)
    trivial

theorem n_284 : UpperZero (tf [T, F, E, T, T, T, T, F, F, F, E, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, F, F, F, E, E, F] (lfZero_of_reply [T, F, E, T, T, T, T, F, F, F, E, E, F] [T, F, E, T, T, T, T, F, F, F, E, F, E] (by decide +kernel) n_283) [[E, F, T, T, T, T, T, F, F, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1598 trivial)
    trivial

theorem n_285 : UpperZero (tf [T, F, E, T, T, T, T, F, F, E, F, E, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, F, F, E, F, E, F] (lfZero_of_reply [T, F, E, T, T, T, T, F, F, E, F, E, F] [T, F, E, T, T, T, T, F, F, F, E, E, F] (by decide +kernel) n_284) [[E, F, T, T, T, T, T, F, F, E, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1599 trivial)
    trivial

theorem n_286 : UpperZero (tf [T, F, E, T, T, T, T, F, F, E, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, F, F, E, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, T, F, F, E, E, F, F] [T, F, E, T, T, T, T, F, F, E, F, E, F] (by decide +kernel) n_285) [[E, F, T, T, T, T, T, F, F, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1600 trivial)
    trivial

theorem n_287 : UpperZero (tf [T, F, E, T, T, T, T, F, E, F, E, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, F, E, F, E, F, F] (lfZero_of_reply [T, F, E, T, T, T, T, F, E, F, E, F, F] [T, F, E, T, T, T, T, F, F, E, E, F, F] (by decide +kernel) n_286) [[E, F, T, T, T, T, T, F, E, F, E, F, F]] [([T, F, E, T, T, T, E, F, T, F, E, F, F], [T, F, E, T, T, T, F, E, T, F, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1601 trivial)
    (And.intro n_60 trivial)

theorem n_288 : UpperZero (tf [T, F, E, T, T, T, T, F, E, E, F, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, F, E, E, F, F, F] (lfZero_of_reply [T, F, E, T, T, T, T, F, E, E, F, F, F] [T, F, E, T, T, T, T, F, E, F, E, F, F] (by decide +kernel) n_287) [[E, F, T, T, T, T, T, F, E, E, F, F, F], [T, F, E, T, T, T, E, F, T, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1602 (And.intro z_1536 trivial))
    trivial

theorem n_289 : UpperZero (tf [T, F, E, T, T, T, T, E, F, E, F, F, F]) :=
  upperZero_of_pairs [T, F, E, T, T, T, T, E, F, E, F, F, F] (lfZero_of_reply [T, F, E, T, T, T, T, E, F, E, F, F, F] [T, F, E, T, T, T, T, F, E, E, F, F, F] (by decide +kernel) n_288) [[E, F, T, T, T, T, T, E, F, E, F, F, F]] [([T, F, E, T, T, T, E, T, F, E, F, F, F], [T, F, E, T, T, T, F, T, E, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1603 trivial)
    (And.intro n_158 trivial)

theorem n_290 : UpperZero (tf [T, T, F, E, T, T, T, E, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, T, E, F, E, F, F, F] (lfZero_of_reply [T, T, F, E, T, T, T, E, F, E, F, F, F] [T, T, F, E, T, T, T, F, E, E, F, F, F] (by decide +kernel) n_282) [] [([T, E, F, T, T, T, T, E, F, E, F, F, F], [T, F, E, T, T, T, T, E, F, E, F, F, F]), ([T, T, F, E, T, T, E, T, F, E, F, F, F], [T, T, F, E, T, T, F, T, E, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_289 (And.intro n_159 trivial))

theorem n_291 : UpperZero (tf [T, T, T, F, E, T, T, E, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, T, E, F, E, F, F, F] (lfZero_of_reply [T, T, T, F, E, T, T, E, F, E, F, F, F] [T, T, T, F, E, T, T, F, E, E, F, F, F] (by decide +kernel) n_276) [] [([T, T, E, F, T, T, T, E, F, E, F, F, F], [T, T, F, E, T, T, T, E, F, E, F, F, F]), ([T, T, T, F, E, T, E, T, F, E, F, F, F], [T, T, T, F, E, T, F, T, E, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_290 (And.intro n_160 trivial))

theorem n_292 : UpperZero (tf [T, T, T, T, F, F, F, T, F, F, E, E, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, T, F, F, E, E, E] ((lfZero_tf_iff _).2 (Or.inl z_1604)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_293 : UpperZero (tf [T, T, T, T, F, F, F, T, F, E, F, E, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, T, F, E, F, E, E] (lfZero_of_reply [T, T, T, T, F, F, F, T, F, E, F, E, E] [T, T, T, T, F, F, F, T, F, F, E, E, E] (by decide +kernel) n_292) [[T, T, T, T, F, F, F, E, F, T, F, E, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1607 trivial)
    trivial

theorem n_294 : UpperZero (tf [T, T, T, T, F, F, F, T, F, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, T, F, E, E, F, E] (lfZero_of_reply [T, T, T, T, F, F, F, T, F, E, E, F, E] [T, T, T, T, F, F, F, T, F, E, F, E, E] (by decide +kernel) n_293) [[T, T, T, T, F, F, F, E, F, T, E, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1610 trivial)
    trivial

theorem n_295 : UpperZero (tf [T, T, T, T, F, F, F, T, F, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, T, F, E, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, T, F, E, E, E, F] [T, T, T, T, F, F, F, T, F, E, E, F, E] (by decide +kernel) n_294) [[T, T, T, T, F, F, F, E, F, T, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1612 trivial)
    trivial

theorem n_296 : UpperZero (tf [T, T, T, T, F, F, F, T, E, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, T, E, F, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, T, E, F, E, E, F] [T, T, T, T, F, F, F, T, F, E, E, E, F] (by decide +kernel) n_295) [[T, T, T, T, F, F, F, E, T, F, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1615 trivial)
    trivial

theorem n_297 : UpperZero (tf [T, T, T, T, F, F, F, T, E, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, T, E, E, F, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, T, E, E, F, E, F] [T, T, T, T, F, F, F, T, E, F, E, E, F] (by decide +kernel) n_296) [[T, T, T, T, F, F, F, E, T, E, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1616 trivial)
    trivial

theorem n_298 : UpperZero (tf [T, T, T, T, F, F, F, T, E, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, T, E, E, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, F, T, E, E, E, F, F] [T, T, T, T, F, F, F, T, E, E, F, E, F] (by decide +kernel) n_297) [[T, T, T, T, F, F, F, E, T, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1617 trivial)
    trivial

theorem n_299 : UpperZero (tf [T, T, T, T, F, F, E, T, F, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, T, F, E, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, T, F, E, E, F, F] [T, T, T, T, F, F, F, T, E, E, E, F, F] (by decide +kernel) n_298) [[T, T, T, T, F, F, E, E, F, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1619 trivial)
    trivial

theorem n_300 : UpperZero (tf [T, T, T, T, F, F, E, T, E, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, T, E, F, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, T, E, F, E, F, F] [T, T, T, T, F, F, E, T, F, E, E, F, F] (by decide +kernel) n_299) [[T, T, T, T, F, F, E, E, T, F, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1510 trivial)
    trivial

theorem n_301 : UpperZero (tf [T, T, T, T, F, F, E, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, T, E, E, F, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, T, E, E, F, F, F] [T, T, T, T, F, F, E, T, E, F, E, F, F] (by decide +kernel) n_300) [[T, T, T, T, F, F, E, E, T, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1620 trivial)
    trivial

theorem n_302 : UpperZero (tf [T, T, T, T, F, F, F, F, E, T, F, E, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, F, E, T, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_1623)) [[T, T, T, T, F, F, F, F, E, E, F, T, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1606 trivial)
    trivial

theorem n_303 : UpperZero (tf [T, T, T, T, F, F, F, F, T, E, E, F, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, F, T, E, E, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1624)) [] [([T, T, T, T, F, F, F, F, E, T, E, F, E], [T, T, T, T, F, F, F, F, E, T, F, E, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_302 trivial)

theorem n_304 : UpperZero (tf [T, T, T, T, F, F, F, F, T, E, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, F, T, E, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, F, T, E, E, E, F] [T, T, T, T, F, F, F, F, T, E, E, F, E] (by decide +kernel) n_303) [[T, T, T, T, F, F, F, F, E, T, E, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1625 trivial)
    trivial

theorem n_305 : UpperZero (tf [T, T, T, T, F, F, F, E, T, F, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, E, T, F, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, E, T, F, E, E, F] [T, T, T, T, F, F, F, F, T, E, E, E, F] (by decide +kernel) n_304) [[T, T, T, T, F, F, F, E, E, F, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1498 trivial)
    trivial

theorem n_306 : UpperZero (tf [T, T, T, T, F, F, F, E, T, E, F, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, E, T, E, F, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, E, T, E, F, E, F] [T, T, T, T, F, F, F, E, T, F, E, E, F] (by decide +kernel) n_305) [[T, T, T, T, F, F, F, E, E, T, F, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1501 trivial)
    trivial

theorem n_307 : UpperZero (tf [T, T, T, T, F, F, F, E, T, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, E, T, E, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, F, E, T, E, E, F, F] [T, T, T, T, F, F, F, E, T, E, F, E, F] (by decide +kernel) n_306) [[T, T, T, T, F, F, F, E, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1503 trivial)
    trivial

theorem n_308 : UpperZero (tf [T, T, T, T, F, F, E, F, T, E, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, F, T, E, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, F, T, E, E, F, F] [T, T, T, T, F, F, F, E, T, E, E, F, F] (by decide +kernel) n_307) [[T, T, T, T, F, F, E, F, E, T, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1506 trivial)
    trivial

theorem n_309 : UpperZero (tf [T, T, T, T, F, F, E, E, T, F, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, E, T, F, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, E, T, F, E, F, F] [T, T, T, T, F, F, E, F, T, E, E, F, F] (by decide +kernel) n_308) [[T, T, T, T, F, F, E, E, E, F, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1626 trivial)
    trivial

theorem n_310 : UpperZero (tf [T, T, T, T, F, F, E, E, T, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, E, T, E, F, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, E, T, E, F, F, F] [T, T, T, T, F, F, E, E, T, F, E, F, F] (by decide +kernel) n_309) [[T, T, T, T, F, F, E, E, E, T, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1627 trivial)
    trivial

theorem n_311 : UpperZero (tf [T, T, T, T, F, E, F, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, F, T, E, E, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, F, T, E, E, F, F, F] [T, T, T, T, F, F, E, T, E, E, F, F, F] (by decide +kernel) n_301) [] [([T, T, T, E, F, T, F, T, E, E, F, F, F], [T, T, T, F, E, T, F, T, E, E, F, F, F]), ([T, T, T, T, F, E, F, E, T, E, F, F, F], [T, T, T, T, F, F, E, E, T, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_160 (And.intro n_310 trivial))

theorem n_312 : UpperZero (tf [T, T, T, T, F, E, T, E, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, T, E, F, E, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, T, E, F, E, F, F, F] [T, T, T, T, F, E, T, F, E, E, F, F, F] (by decide +kernel) n_275) [] [([T, T, T, E, F, T, T, E, F, E, F, F, F], [T, T, T, F, E, T, T, E, F, E, F, F, F]), ([T, T, T, T, F, E, E, T, F, E, F, F, F], [T, T, T, T, F, E, F, T, E, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_291 (And.intro n_311 trivial))

theorem n_313 : UpperZero (tf [T, T, T, E, F, T, F, T, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, F, T, F, T, E, E, F, F, F] (lfZero_of_reply [T, T, T, E, F, T, F, T, E, E, F, F, F] [T, T, T, F, E, T, F, T, E, E, F, F, F] (by decide +kernel) n_160) [[T, T, E, T, F, T, F, T, E, E, F, F, F], [T, T, T, E, F, T, F, E, T, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1647 (And.intro z_1650 trivial))
    trivial

theorem n_314 : UpperZero (tf [T, T, T, E, F, T, T, E, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, F, T, T, E, F, E, F, F, F] (lfZero_of_reply [T, T, T, E, F, T, T, E, F, E, F, F, F] [T, T, T, F, E, T, T, E, F, E, F, F, F] (by decide +kernel) n_291) [[T, T, E, T, F, T, T, E, F, E, F, F, F]] [([T, T, T, E, F, T, E, T, F, E, F, F, F], [T, T, T, E, F, T, F, T, E, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1648 trivial)
    (And.intro n_313 trivial)

theorem n_315 : UpperZero (tf [T, T, T, T, F, E, E, T, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, E, T, F, E, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, E, T, F, E, F, F, F] [T, T, T, T, F, E, F, T, E, E, F, F, F] (by decide +kernel) n_311) [[T, T, T, T, F, E, E, E, F, T, F, F, F]] [([T, T, T, E, F, T, E, T, F, E, F, F, F], [T, T, T, E, F, T, F, T, E, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1655 trivial)
    (And.intro n_313 trivial)

theorem n_316 : UpperZero (tf [T, T, T, T, F, E, T, E, E, F, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, T, E, E, F, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, T, E, E, F, F, F, F] [T, T, T, T, F, E, T, E, F, E, F, F, F] (by decide +kernel) n_312) [] [([T, T, T, E, F, T, T, E, E, F, F, F, F], [T, T, T, E, F, T, T, E, F, E, F, F, F]), ([T, T, T, T, F, E, E, T, E, F, F, F, F], [T, T, T, T, F, E, E, T, F, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_314 (And.intro n_315 trivial))

theorem n_317 : UpperZero (tf [T, T, T, T, F, F, F, F, E, T, E, F, E]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, F, E, T, E, F, E] (lfZero_of_reply [T, T, T, T, F, F, F, F, E, T, E, F, E] [T, T, T, T, F, F, F, F, E, T, F, E, E] (by decide +kernel) n_302) [[T, T, T, T, F, F, F, F, E, E, T, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1609 trivial)
    trivial

theorem n_318 : UpperZero (tf [T, T, T, T, F, F, F, F, E, T, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, F, E, T, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, F, E, T, E, E, F] [T, T, T, T, F, F, F, F, E, T, E, F, E] (by decide +kernel) n_317) [[T, T, T, T, F, F, F, F, E, E, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1611 trivial)
    trivial

theorem n_319 : UpperZero (tf [T, T, T, T, F, F, F, E, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, E, F, T, E, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, E, F, T, E, E, F] [T, T, T, T, F, F, F, F, E, T, E, E, F] (by decide +kernel) n_318) [[T, T, T, T, F, F, F, E, F, E, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1614 trivial)
    trivial

theorem n_320 : UpperZero (tf [T, T, T, T, F, F, F, E, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, E, E, T, F, E, F] (lfZero_of_reply [T, T, T, T, F, F, F, E, E, T, F, E, F] [T, T, T, T, F, F, F, E, F, T, E, E, F] (by decide +kernel) n_319) [[T, T, T, T, F, F, F, E, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1656 trivial)
    trivial

theorem n_321 : UpperZero (tf [T, T, T, T, F, F, F, E, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, F, E, E, T, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, F, E, E, T, E, F, F] [T, T, T, T, F, F, F, E, E, T, F, E, F] (by decide +kernel) n_320) [[T, T, T, T, F, F, F, E, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1505 trivial)
    trivial

theorem n_322 : UpperZero (tf [T, T, T, T, F, F, E, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, F, E, T, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, F, E, T, E, F, F] [T, T, T, T, F, F, F, E, E, T, E, F, F] (by decide +kernel) n_321) [[T, T, T, T, F, F, E, F, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1618 trivial)
    trivial

theorem n_323 : UpperZero (tf [T, T, T, T, F, F, E, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, E, F, T, E, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, E, F, T, E, F, F] [T, T, T, T, F, F, E, F, E, T, E, F, F] (by decide +kernel) n_322) [[T, T, T, T, F, F, E, E, F, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1509 trivial)
    trivial

theorem n_324 : UpperZero (tf [T, T, T, T, F, F, E, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, F, E, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, T, F, F, E, E, E, T, F, F, F] [T, T, T, T, F, F, E, E, F, T, E, F, F] (by decide +kernel) n_323) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_325 : UpperZero (tf [T, T, T, T, F, E, F, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, F, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, F, E, E, T, F, F, F] [T, T, T, T, F, F, E, E, E, T, F, F, F] (by decide +kernel) n_324) [] [([T, T, T, E, F, T, F, E, E, T, F, F, F], [T, T, T, F, E, T, F, E, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_260 trivial)

theorem n_326 : UpperZero (tf [T, T, T, T, F, E, E, F, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, E, F, E, T, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, E, F, E, T, F, F, F] [T, T, T, T, F, E, F, E, E, T, F, F, F] (by decide +kernel) n_325) [[T, T, T, E, F, T, E, F, E, T, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1654 trivial)
    trivial

theorem n_327 : UpperZero (tf [T, F, T, E, T, F, T, F, E, T, F, E, F]) :=
  upperZero_of_pairs [T, F, T, E, T, F, T, F, E, T, F, E, F] ((lfZero_tf_iff _).2 (Or.inl z_185)) [[T, F, E, T, T, F, T, F, E, T, F, E, F], [T, F, T, E, T, F, E, F, T, T, F, E, F], [T, F, T, E, T, F, T, F, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_555 (And.intro z_1713 (And.intro z_1714 trivial)))
    trivial

theorem n_328 : UpperZero (tf [T, F, T, E, T, F, T, E, F, T, F, E, F]) :=
  upperZero_of_pairs [T, F, T, E, T, F, T, E, F, T, F, E, F] (lfZero_of_reply [T, F, T, E, T, F, T, E, F, T, F, E, F] [T, F, T, E, T, F, T, F, E, T, F, E, F] (by decide +kernel) n_327) [[T, F, E, T, T, F, T, E, F, T, F, E, F], [T, F, T, E, T, F, E, T, F, T, F, E, F], [T, F, T, E, T, F, T, E, F, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1718 (And.intro z_1066 (And.intro z_1719 trivial)))
    trivial

theorem n_329 : UpperZero (tf [T, F, T, F, E, T, F, T, E, E, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, E, T, F, T, E, E, F, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1012)) [[T, F, E, F, T, T, F, T, E, E, F, T, F], [T, F, T, F, E, T, F, E, T, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1726 (And.intro z_1710 trivial))
    trivial

theorem n_330 : UpperZero (tf [T, F, T, F, F, E, E, T, F, T, F, T, E]) :=
  upperZero_of_pairs [T, F, T, F, F, E, E, T, F, T, F, T, E] ((lfZero_tf_iff _).2 (Or.inl z_1704)) [[T, F, T, F, F, E, E, T, F, T, F, E, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1733 trivial)
    trivial

theorem n_331 : UpperZero (tf [T, F, T, F, F, E, T, F, E, E, T, T, F]) :=
  upperZero_of_pairs [T, F, T, F, F, E, T, F, E, E, T, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1707)) [[T, F, T, F, F, E, E, F, T, E, T, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_170 trivial)
    trivial

theorem n_332 : UpperZero (tf [T, F, T, F, F, E, T, E, F, T, E, T, F]) :=
  upperZero_of_pairs [T, F, T, F, F, E, T, E, F, T, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1708)) [] [([T, F, T, F, F, E, E, T, F, T, E, T, F], [T, F, T, F, F, E, E, T, F, T, F, T, E]), ([T, F, T, F, F, E, T, E, F, E, T, T, F], [T, F, T, F, F, E, T, F, E, E, T, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_330 (And.intro n_331 trivial))

theorem n_333 : UpperZero (tf [T, F, T, F, T, F, F, E, E, E, T, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, F, F, E, E, E, T, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1734)) [] []
    (by decide +kernel) (by decide +kernel)
    trivial
    trivial

theorem n_334 : UpperZero (tf [T, F, T, F, T, F, E, F, E, E, T, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, F, E, F, E, E, T, T, F] (lfZero_of_reply [T, F, T, F, T, F, E, F, E, E, T, T, F] [T, F, T, F, T, F, F, E, E, E, T, T, F] (by decide +kernel) n_333) [] [([T, F, T, F, E, F, T, F, E, E, T, T, F], [T, F, T, F, F, E, T, F, E, E, T, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_331 trivial)

theorem n_335 : UpperZero (tf [T, F, T, F, T, F, E, E, F, T, E, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, F, E, E, F, T, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1728)) [] [([T, F, T, F, E, F, T, E, F, T, E, T, F], [T, F, T, F, F, E, T, E, F, T, E, T, F]), ([T, F, T, F, T, F, E, E, F, E, T, T, F], [T, F, T, F, T, F, E, F, E, E, T, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_332 (And.intro n_334 trivial))

theorem n_336 : UpperZero (tf [T, F, T, F, F, E, E, T, F, T, E, T, F]) :=
  upperZero_of_pairs [T, F, T, F, F, E, E, T, F, T, E, T, F] (lfZero_of_reply [T, F, T, F, F, E, E, T, F, T, E, T, F] [T, F, T, F, F, E, E, T, F, T, F, T, E] (by decide +kernel) n_330) [[T, F, T, F, F, E, E, T, F, E, T, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1736 trivial)
    trivial

theorem n_337 : UpperZero (tf [T, F, T, F, F, E, T, E, E, T, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, F, E, T, E, E, T, F, T, F] (lfZero_of_reply [T, F, T, F, F, E, T, E, E, T, F, T, F] [T, F, T, F, F, E, T, E, F, T, E, T, F] (by decide +kernel) n_332) [] [([T, F, T, F, F, E, E, T, E, T, F, T, F], [T, F, T, F, F, E, E, T, F, T, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_336 trivial)

theorem n_338 : UpperZero (tf [T, F, T, F, T, F, E, E, E, T, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, F, E, E, E, T, F, T, F] (lfZero_of_reply [T, F, T, F, T, F, E, E, E, T, F, T, F] [T, F, T, F, T, F, E, E, F, T, E, T, F] (by decide +kernel) n_335) [] [([T, F, T, F, E, F, T, E, E, T, F, T, F], [T, F, T, F, F, E, T, E, E, T, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_337 trivial)

theorem n_339 : UpperZero (tf [T, F, T, F, T, E, F, E, E, T, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, E, F, E, E, T, F, T, F] (lfZero_of_reply [T, F, T, F, T, E, F, E, E, T, F, T, F] [T, F, T, F, T, F, E, E, E, T, F, T, F] (by decide +kernel) n_338) [[T, F, T, F, E, T, F, E, E, T, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1063 trivial)
    trivial

theorem n_340 : UpperZero (tf [T, F, T, F, F, T, E, E, E, T, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, F, T, E, E, E, T, F, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1709)) [] [([T, F, T, F, F, E, T, E, E, T, F, T, F], [T, F, T, F, F, E, T, E, F, T, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_332 trivial)

theorem n_341 : UpperZero (tf [T, F, T, F, E, T, F, E, E, T, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, E, T, F, E, E, T, F, T, F] (lfZero_of_reply [T, F, T, F, E, T, F, E, E, T, F, T, F] [T, F, T, F, F, T, E, E, E, T, F, T, F] (by decide +kernel) n_340) [[T, F, E, F, T, T, F, E, E, T, F, T, F], [T, F, T, F, E, E, F, T, E, T, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1744 (And.intro z_1721 trivial))
    trivial

theorem n_342 : UpperZero (tf [T, F, T, F, T, E, E, F, E, T, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, E, E, F, E, T, F, T, F] (lfZero_of_reply [T, F, T, F, T, E, E, F, E, T, F, T, F] [T, F, T, F, T, E, F, E, E, T, F, T, F] (by decide +kernel) n_339) [] [([T, F, T, F, E, T, E, F, E, T, F, T, F], [T, F, T, F, E, T, F, E, E, T, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_341 trivial)

theorem n_343 : UpperZero (tf [T, F, T, F, T, E, E, T, F, E, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, E, E, T, F, E, F, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1065)) [] [([T, F, T, F, E, T, E, T, F, E, F, T, F], [T, F, T, F, E, T, F, T, E, E, F, T, F]), ([T, F, T, F, T, E, E, E, F, T, F, T, F], [T, F, T, F, T, E, E, F, E, T, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_329 (And.intro n_342 trivial))

theorem n_344 : UpperZero (tf [T, F, T, E, T, F, E, T, F, T, F, E, F]) :=
  upperZero_of_pairs [T, F, T, E, T, F, E, T, F, T, F, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1066)) [[T, F, T, E, E, F, T, T, F, T, F, E, F]] [([T, F, E, T, T, F, E, T, F, T, F, E, F], [T, F, E, T, T, F, F, T, E, T, F, E, F]), ([T, F, T, E, T, F, E, T, F, E, F, T, F], [T, F, T, F, T, E, E, T, F, E, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1724 trivial)
    (And.intro n_213 (And.intro n_343 trivial))

theorem n_345 : UpperZero (tf [T, F, T, F, T, E, T, F, F, E, E, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, E, T, F, F, E, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1749)) [[T, F, T, F, E, T, T, F, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1751 trivial)
    trivial

theorem n_346 : UpperZero (tf [T, F, T, F, T, E, T, F, E, F, E, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, E, T, F, E, F, E, T, F] (lfZero_of_reply [T, F, T, F, T, E, T, F, E, F, E, T, F] [T, F, T, F, T, E, T, F, F, E, E, T, F] (by decide +kernel) n_345) [[T, F, T, F, E, T, T, F, E, F, E, T, F], [T, F, T, F, T, E, E, F, T, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_183 (And.intro z_180 trivial))
    trivial

theorem n_347 : UpperZero (tf [T, F, T, F, T, E, T, F, E, E, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, E, T, F, E, E, F, T, F] (lfZero_of_reply [T, F, T, F, T, E, T, F, E, E, F, T, F] [T, F, T, F, T, E, T, F, E, F, E, T, F] (by decide +kernel) n_346) [[T, F, T, F, E, T, T, F, E, E, F, T, F], [T, F, T, F, T, E, E, F, T, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1754 (And.intro z_1712 trivial))
    trivial

theorem n_348 : UpperZero (tf [T, F, T, F, T, E, T, E, F, E, F, T, F]) :=
  upperZero_of_pairs [T, F, T, F, T, E, T, E, F, E, F, T, F] (lfZero_of_reply [T, F, T, F, T, E, T, E, F, E, F, T, F] [T, F, T, F, T, E, T, F, E, E, F, T, F] (by decide +kernel) n_347) [[T, F, T, F, E, T, T, E, F, E, F, T, F], [T, F, T, F, T, E, E, T, F, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1756 (And.intro z_1065 trivial))
    trivial

theorem n_349 : UpperZero (tf [T, F, T, E, T, F, T, E, F, E, F, T, F]) :=
  upperZero_of_pairs [T, F, T, E, T, F, T, E, F, E, F, T, F] (lfZero_of_reply [T, F, T, E, T, F, T, E, F, E, F, T, F] [T, F, T, F, T, E, T, E, F, E, F, T, F] (by decide +kernel) n_348) [[T, F, E, T, T, F, T, E, F, E, F, T, F]] [([T, F, T, E, T, F, E, T, F, E, F, T, F], [T, F, T, F, T, E, E, T, F, E, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1758 trivial)
    (And.intro n_343 trivial)

theorem n_350 : UpperZero (tf [T, E, T, F, T, F, T, E, F, T, F, E, F]) :=
  upperZero_of_pairs [T, E, T, F, T, F, T, E, F, T, F, E, F] (lfZero_of_reply [T, E, T, F, T, F, T, E, F, T, F, E, F] [T, F, T, E, T, F, T, E, F, T, F, E, F] (by decide +kernel) n_328) [[E, T, T, F, T, F, T, E, F, T, F, E, F]] [([T, E, T, F, T, F, E, T, F, T, F, E, F], [T, F, T, E, T, F, E, T, F, T, F, E, F]), ([T, E, T, F, T, F, T, E, F, E, F, T, F], [T, F, T, E, T, F, T, E, F, E, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1663 trivial)
    (And.intro n_344 (And.intro n_349 trivial))

theorem n_351 : UpperZero (tf [T, F, T, E, T, T, E, F, F, E, F, T, F]) :=
  upperZero_of_pairs [T, F, T, E, T, T, E, F, F, E, F, T, F] (lfZero_of_mirror_dec [T, F, T, E, T, T, E, F, F, E, F, T, F] (by decide +kernel)) [[T, F, E, T, T, T, E, F, F, E, F, T, F]] [([T, F, T, E, T, E, T, F, F, E, F, T, F], [T, F, T, E, T, F, T, E, F, E, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1760 trivial)
    (And.intro n_349 trivial)

theorem n_352 : UpperZero (tf [T, E, T, F, T, T, E, F, F, T, F, E, F]) :=
  upperZero_of_pairs [T, E, T, F, T, T, E, F, F, T, F, E, F] (lfZero_of_mirror_dec [T, E, T, F, T, T, E, F, F, T, F, E, F] (by decide +kernel)) [[E, T, T, F, T, T, E, F, F, T, F, E, F]] [([T, E, T, F, T, E, T, F, F, T, F, E, F], [T, E, T, F, T, F, T, E, F, T, F, E, F]), ([T, E, T, F, T, T, E, F, F, E, F, T, F], [T, F, T, E, T, T, E, F, F, E, F, T, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1670 trivial)
    (And.intro n_350 (And.intro n_351 trivial))

theorem n_353 : UpperZero (tf [T, T, F, F, T, F, T, E, E, F, E, T, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, T, E, E, F, E, T, F] ((lfZero_tf_iff _).2 (Or.inl z_1761)) [] [([T, T, F, F, T, F, E, T, E, F, E, T, F], [T, T, F, F, T, F, E, T, F, E, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_188 trivial)

theorem n_354 : UpperZero (tf [T, T, F, F, T, F, T, E, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, T, E, E, T, F, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1762)) [] [([T, T, F, F, T, F, E, T, E, T, F, E, F], [T, T, F, F, T, F, E, T, F, T, E, E, F]), ([T, T, F, F, T, F, T, E, E, E, F, T, F], [T, T, F, F, T, F, T, E, E, F, E, T, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_183 (And.intro n_353 trivial))

theorem n_355 : UpperZero (tf [T, T, F, F, T, F, T, E, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, T, E, E, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, F, T, E, E, T, E, F, F] [T, T, F, F, T, F, T, E, E, T, F, E, F] (by decide +kernel) n_354) [[T, T, F, F, T, F, T, E, E, E, T, F, F]] [([T, T, F, F, T, F, E, T, E, T, E, F, F], [T, T, F, F, T, F, E, T, E, T, F, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_593 trivial)
    (And.intro n_184 trivial)

theorem n_356 : UpperZero (tf [T, T, F, F, T, F, E, E, T, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, E, E, T, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, F, E, E, T, T, E, F, F] [T, T, F, F, T, F, E, E, T, T, F, E, F] (by decide +kernel) n_185) [[T, T, F, F, E, F, T, E, T, T, E, F, F]] [([T, T, F, F, T, F, E, E, T, E, T, F, F], [T, T, F, F, T, F, E, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1768 trivial)
    (And.intro n_202 trivial)

theorem n_357 : UpperZero (tf [T, T, F, F, T, E, F, E, T, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, F, E, T, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, E, F, E, T, T, E, F, F] [T, T, F, F, T, F, E, E, T, T, E, F, F] (by decide +kernel) n_356) [] [([T, T, F, F, E, T, F, E, T, T, E, F, F], [T, T, F, F, E, T, F, E, T, T, F, E, F]), ([T, T, F, F, T, E, F, E, T, E, T, F, F], [T, T, F, F, T, E, F, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_196 (And.intro n_205 trivial))

theorem n_358 : UpperZero (tf [T, T, F, F, T, F, T, E, E, F, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, T, F, T, E, E, F, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1770)) [[T, T, F, F, T, F, T, E, E, F, E, F, T]] [([T, T, F, F, T, F, E, T, E, F, T, F, E], [T, T, F, F, T, F, E, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1771 trivial)
    (And.intro n_182 trivial)

theorem n_359 : UpperZero (tf [T, T, F, F, T, F, T, E, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, T, E, E, F, T, E, F] (lfZero_of_reply [T, T, F, F, T, F, T, E, E, F, T, E, F] [T, T, F, F, T, F, T, E, E, F, T, F, E] (by decide +kernel) n_358) [[T, T, F, F, T, F, T, E, E, F, E, T, F]] [([T, T, F, F, T, F, E, T, E, F, T, E, F], [T, T, F, F, T, F, E, T, F, E, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1761 trivial)
    (And.intro n_186 trivial)

theorem n_360 : UpperZero (tf [T, T, F, F, T, F, T, E, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, F, T, E, E, E, T, F, F] (lfZero_of_reply [T, T, F, F, T, F, T, E, E, E, T, F, F] [T, T, F, F, T, F, T, E, E, F, T, E, F] (by decide +kernel) n_359) [] [([T, T, F, F, T, F, E, T, E, E, T, F, F], [T, T, F, F, T, F, E, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_189 trivial)

theorem n_361 : UpperZero (tf [T, T, F, F, T, E, T, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, T, F, E, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, E, T, F, E, T, E, F, F] [T, T, F, F, T, F, T, E, E, T, E, F, F] (by decide +kernel) n_355) [[T, T, F, F, E, T, T, F, E, T, E, F, F]] [([T, T, F, F, T, E, E, F, T, T, E, F, F], [T, T, F, F, T, E, F, E, T, T, E, F, F]), ([T, T, F, F, T, E, T, F, E, E, T, F, F], [T, T, F, F, T, F, T, E, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1767 trivial)
    (And.intro n_357 (And.intro n_360 trivial))

theorem n_362 : UpperZero (tf [T, T, F, F, T, E, T, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, T, E, F, T, E, F, F] (lfZero_of_reply [T, T, F, F, T, E, T, E, F, T, E, F, F] [T, T, F, F, T, E, T, F, E, T, E, F, F] (by decide +kernel) n_361) [[T, T, F, F, E, T, T, E, F, T, E, F, F], [T, T, F, F, T, E, T, E, F, E, T, F, F]] [([T, T, F, F, T, E, E, T, F, T, E, F, F], [T, T, F, F, T, E, F, T, E, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_738 (And.intro z_772 trivial))
    (And.intro n_191 trivial)

theorem n_363 : UpperZero (tf [T, T, F, F, T, E, E, F, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, E, F, T, F, T, E, F] (lfZero_of_reply [T, T, F, F, T, E, E, F, T, F, T, E, F] [T, T, F, F, T, E, F, E, T, F, T, E, F] (by decide +kernel) n_205) [[T, T, F, F, T, E, E, F, T, F, E, T, F]] [([T, T, F, F, E, T, E, F, T, F, T, E, F], [T, T, F, F, E, T, F, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1802 trivial)
    (And.intro n_239 trivial)

theorem n_364 : UpperZero (tf [T, T, F, F, T, E, T, F, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, T, F, E, E, T, F, F] (lfZero_of_reply [T, T, F, F, T, E, T, F, E, E, T, F, F] [T, T, F, F, T, F, T, E, E, E, T, F, F] (by decide +kernel) n_360) [[T, T, F, F, E, T, T, F, E, E, T, F, F]] [([T, T, F, F, T, E, E, F, T, E, T, F, F], [T, T, F, F, T, E, E, F, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_737 trivial)
    (And.intro n_363 trivial)

theorem n_365 : UpperZero (tf [T, T, F, F, E, T, T, F, F, E, T, F, E]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, F, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1804)) [[T, T, F, F, E, T, T, F, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1805 trivial)
    trivial

theorem n_366 : UpperZero (tf [T, T, F, F, E, T, T, F, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, F, F, E, T, E, F] (lfZero_of_reply [T, T, F, F, E, T, T, F, F, E, T, E, F] [T, T, F, F, E, T, T, F, F, E, T, F, E] (by decide +kernel) n_365) [[T, T, F, F, E, T, T, F, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1765 trivial)
    trivial

theorem n_367 : UpperZero (tf [T, T, F, F, E, T, T, F, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, F, E, F, T, E, F] (lfZero_of_reply [T, T, F, F, E, T, T, F, E, F, T, E, F] [T, T, F, F, E, T, T, F, F, E, T, E, F] (by decide +kernel) n_366) [[T, T, F, F, E, T, T, F, E, F, E, T, F]] [([T, T, F, F, E, T, E, F, T, F, T, E, F], [T, T, F, F, E, T, F, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_564 trivial)
    (And.intro n_239 trivial)

theorem n_368 : UpperZero (tf [T, T, F, F, E, T, T, F, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, F, E, E, T, F, F] (lfZero_of_reply [T, T, F, F, E, T, T, F, E, E, T, F, F] [T, T, F, F, E, T, T, F, E, F, T, E, F] (by decide +kernel) n_367) [[T, T, F, F, E, T, E, F, T, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1807 trivial)
    trivial

theorem n_369 : UpperZero (tf [T, T, F, F, T, E, T, E, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, F, T, E, T, E, F, E, T, F, F] (lfZero_of_reply [T, T, F, F, T, E, T, E, F, E, T, F, F] [T, T, F, F, T, E, T, F, E, E, T, F, F] (by decide +kernel) n_364) [] [([T, T, F, F, E, T, T, E, F, E, T, F, F], [T, T, F, F, E, T, T, F, E, E, T, F, F]), ([T, T, F, F, T, E, E, T, F, E, T, F, F], [T, T, F, F, T, E, F, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_368 (And.intro n_206 trivial))

theorem n_370 : UpperZero (tf [T, T, F, E, T, F, T, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, F, T, E, F, T, E, F, F] (lfZero_of_reply [T, T, F, E, T, F, T, E, F, T, E, F, F] [T, T, F, F, T, E, T, E, F, T, E, F, F] (by decide +kernel) n_362) [[T, E, F, T, T, F, T, E, F, T, E, F, F]] [([T, T, F, E, T, F, E, T, F, T, E, F, F], [T, T, F, F, T, E, E, T, F, T, E, F, F]), ([T, T, F, E, T, F, T, E, F, E, T, F, F], [T, T, F, F, T, E, T, E, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1800 trivial)
    (And.intro n_207 (And.intro n_369 trivial))

theorem n_371 : UpperZero (tf [T, T, F, E, T, F, T, E, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, F, T, E, F, E, T, F, F] (lfZero_of_reply [T, T, F, E, T, F, T, E, F, E, T, F, F] [T, T, F, F, T, E, T, E, F, E, T, F, F] (by decide +kernel) n_369) [[T, E, F, T, T, F, T, E, F, E, T, F, F], [T, T, F, E, T, F, E, T, F, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1810 (And.intro z_724 trivial))
    trivial

theorem n_372 : UpperZero (tf [T, T, E, F, T, F, T, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, E, F, T, F, T, E, F, T, E, F, F] (lfZero_of_reply [T, T, E, F, T, F, T, E, F, T, E, F, F] [T, T, F, E, T, F, T, E, F, T, E, F, F] (by decide +kernel) n_370) [] [([T, E, T, F, T, F, T, E, F, T, E, F, F], [T, E, T, F, T, F, T, E, F, T, F, E, F]), ([T, T, E, F, T, F, E, T, F, T, E, F, F], [T, T, F, E, T, F, E, T, F, T, E, F, F]), ([T, T, E, F, T, F, T, E, F, E, T, F, F], [T, T, F, E, T, F, T, E, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_350 (And.intro n_208 (And.intro n_371 trivial)))

theorem n_373 : UpperZero (tf [T, T, F, E, T, T, E, F, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, E, T, T, E, F, F, E, T, F, F] (lfZero_of_mirror_dec [T, T, F, E, T, T, E, F, F, E, T, F, F] (by decide +kernel)) [[T, E, F, T, T, T, E, F, F, E, T, F, F]] [([T, T, F, E, T, E, T, F, F, E, T, F, F], [T, T, F, E, T, F, T, E, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1811 trivial)
    (And.intro n_371 trivial)

theorem n_374 : UpperZero (tf [T, T, E, F, T, T, E, F, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, E, F, T, T, E, F, F, T, E, F, F] (lfZero_of_mirror_dec [T, T, E, F, T, T, E, F, F, T, E, F, F] (by decide +kernel)) [] [([T, E, T, F, T, T, E, F, F, T, E, F, F], [T, E, T, F, T, T, E, F, F, T, F, E, F]), ([T, T, E, F, T, E, T, F, F, T, E, F, F], [T, T, E, F, T, F, T, E, F, T, E, F, F]), ([T, T, E, F, T, T, E, F, F, E, T, F, F], [T, T, F, E, T, T, E, F, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_352 (And.intro n_372 (And.intro n_373 trivial)))

theorem n_375 : UpperZero (tf [T, T, T, F, F, F, T, E, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, T, E, E, T, F, E, F] ((lfZero_tf_iff _).2 (Or.inl z_74)) [[T, T, T, F, F, F, E, T, E, T, F, E, F], [T, T, T, F, F, F, T, E, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_1812 trivial))
    trivial

theorem n_376 : UpperZero (tf [T, T, T, F, F, F, T, E, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, T, E, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, F, T, E, E, T, E, F, F] [T, T, T, F, F, F, T, E, E, T, F, E, F] (by decide +kernel) n_375) [[T, T, T, F, F, F, E, T, E, T, E, F, F], [T, T, T, F, F, F, T, E, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_210 (And.intro z_94 trivial))
    trivial

theorem n_377 : UpperZero (tf [T, T, T, F, F, E, T, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, T, F, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, E, T, F, E, T, E, F, F] [T, T, T, F, F, F, T, E, E, T, E, F, F] (by decide +kernel) n_376) [[T, T, T, F, F, E, E, F, T, T, E, F, F], [T, T, T, F, F, E, T, F, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1006 (And.intro z_536 trivial))
    trivial

theorem n_378 : UpperZero (tf [T, T, T, F, F, E, T, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, T, E, F, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, E, T, E, F, T, E, F, F] [T, T, T, F, F, E, T, F, E, T, E, F, F] (by decide +kernel) n_377) [[T, T, T, F, F, E, E, T, F, T, E, F, F], [T, T, T, F, F, E, T, E, F, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_743 (And.intro z_104 trivial))
    trivial

theorem n_379 : UpperZero (tf [T, T, T, F, F, F, E, T, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, T, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_69)) [] [([T, T, T, F, F, F, E, T, F, E, T, E, F], [T, T, T, F, F, F, E, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_92 trivial)

theorem n_380 : UpperZero (tf [T, T, T, F, F, F, E, T, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, T, E, T, F, E, F] (lfZero_of_reply [T, T, T, F, F, F, E, T, E, T, F, E, F] [T, T, T, F, F, F, E, T, F, T, E, E, F] (by decide +kernel) n_379) [[T, T, T, F, F, F, E, E, T, T, F, E, F], [T, T, T, F, F, F, E, T, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_209 (And.intro z_1176 trivial))
    trivial

theorem n_381 : UpperZero (tf [T, T, T, F, F, F, E, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, F, E, T, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, F, E, T, E, T, E, F, F] [T, T, T, F, F, F, E, T, E, T, F, E, F] (by decide +kernel) n_380) [[T, T, T, F, F, F, E, E, T, T, E, F, F]] [([T, T, T, F, F, F, E, T, E, E, T, F, F], [T, T, T, F, F, F, E, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_748 trivial)
    (And.intro n_94 trivial)

theorem n_382 : UpperZero (tf [T, T, T, F, F, E, F, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, F, T, E, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, E, F, T, E, T, E, F, F] [T, T, T, F, F, F, E, T, E, T, E, F, F] (by decide +kernel) n_381) [[T, T, T, F, F, E, F, E, T, T, E, F, F]] [([T, T, T, F, F, E, F, T, E, E, T, F, F], [T, T, T, F, F, F, E, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_90 trivial)
    (And.intro n_98 trivial)

theorem n_383 : UpperZero (tf [T, T, T, F, F, E, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, T, F, T, E, F, F] (lfZero_of_reply [T, T, T, F, F, E, E, T, F, T, E, F, F] [T, T, T, F, F, E, F, T, E, T, E, F, F] (by decide +kernel) n_382) [] [([T, T, T, F, F, E, E, T, F, E, T, F, F], [T, T, T, F, F, E, F, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_99 trivial)

theorem n_384 : UpperZero (tf [T, T, T, F, F, E, T, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, T, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, F, E, T, E, E, T, F, F, F] [T, T, T, F, F, E, T, E, F, T, E, F, F] (by decide +kernel) n_378) [] [([T, T, T, F, F, E, E, T, E, T, F, F, F], [T, T, T, F, F, E, E, T, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_383 trivial)

theorem n_385 : UpperZero (tf [T, T, T, F, F, E, E, T, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, F, E, E, T, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, F, E, E, T, E, T, F, F, F] [T, T, T, F, F, E, E, T, F, T, E, F, F] (by decide +kernel) n_383) [[T, T, T, F, F, E, E, E, T, T, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1813 trivial)
    trivial

theorem n_386 : UpperZero (tf [T, T, T, F, E, F, T, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, F, T, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, F, E, F, T, E, E, T, F, F, F] [T, T, T, F, F, E, T, E, E, T, F, F, F] (by decide +kernel) n_384) [] [([T, T, E, F, T, F, T, E, E, T, F, F, F], [T, T, E, F, T, F, T, E, F, T, E, F, F]), ([T, T, T, F, E, F, E, T, E, T, F, F, F], [T, T, T, F, F, E, E, T, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_372 (And.intro n_385 trivial))

theorem n_387 : UpperZero (tf [T, T, T, F, E, T, E, F, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, F, E, T, E, F, E, T, F, F, F] (lfZero_of_mirror_dec [T, T, T, F, E, T, E, F, E, T, F, F, F] (by decide +kernel)) [] [([T, T, E, F, T, T, E, F, E, T, F, F, F], [T, T, E, F, T, T, E, F, F, T, E, F, F]), ([T, T, T, F, E, E, T, F, E, T, F, F, F], [T, T, T, F, E, F, T, E, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_374 (And.intro n_386 trivial))

theorem n_388 : UpperZero (tf [T, T, F, T, F, T, F, F, E, T, F, E, E]) :=
  upperZero_of_pairs [T, T, F, T, F, T, F, F, E, T, F, E, E] ((lfZero_tf_iff _).2 (Or.inl z_1816)) [[T, T, F, T, F, T, F, F, E, E, F, T, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1818 trivial)
    trivial

theorem n_389 : UpperZero (tf [T, T, F, T, F, T, F, F, E, T, E, F, E]) :=
  upperZero_of_pairs [T, T, F, T, F, T, F, F, E, T, E, F, E] (lfZero_of_reply [T, T, F, T, F, T, F, F, E, T, E, F, E] [T, T, F, T, F, T, F, F, E, T, F, E, E] (by decide +kernel) n_388) [[T, T, F, T, F, T, F, F, E, E, T, F, E]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1820 trivial)
    trivial

theorem n_390 : UpperZero (tf [T, T, F, T, F, T, F, F, E, T, E, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, T, F, F, E, T, E, E, F] (lfZero_of_reply [T, T, F, T, F, T, F, F, E, T, E, E, F] [T, T, F, T, F, T, F, F, E, T, E, F, E] (by decide +kernel) n_389) [[T, T, F, T, F, T, F, F, E, E, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1821 trivial)
    trivial

theorem n_391 : UpperZero (tf [T, T, F, T, F, T, F, E, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, T, F, E, F, T, E, E, F] (lfZero_of_reply [T, T, F, T, F, T, F, E, F, T, E, E, F] [T, T, F, T, F, T, F, F, E, T, E, E, F] (by decide +kernel) n_390) [[T, T, F, T, F, E, F, T, F, T, E, E, F], [T, T, F, T, F, T, F, E, F, E, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1829 (And.intro z_1831 trivial))
    trivial

theorem n_392 : UpperZero (tf [T, T, F, T, F, T, F, E, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, T, F, E, E, T, F, E, F] (lfZero_of_reply [T, T, F, T, F, T, F, E, E, T, F, E, F] [T, T, F, T, F, T, F, E, F, T, E, E, F] (by decide +kernel) n_391) [[T, T, F, T, F, E, F, T, E, T, F, E, F], [T, T, F, T, F, T, F, E, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1838 (And.intro z_1839 trivial))
    trivial

theorem n_393 : UpperZero (tf [T, T, F, T, F, T, F, E, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, T, F, E, E, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, T, F, E, E, T, E, F, F] [T, T, F, T, F, T, F, E, E, T, F, E, F] (by decide +kernel) n_392) [[T, T, F, T, F, E, F, T, E, T, E, F, F], [T, T, F, T, F, T, F, E, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1528 (And.intro z_1840 trivial))
    trivial

theorem n_394 : UpperZero (tf [T, T, F, T, F, T, E, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, T, E, F, E, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, T, E, F, E, T, E, F, F] [T, T, F, T, F, T, F, E, E, T, E, F, F] (by decide +kernel) n_393) [[T, T, F, T, F, E, T, F, E, T, E, F, F], [T, T, F, T, F, T, E, F, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1883 (And.intro z_1884 trivial))
    trivial

theorem n_395 : UpperZero (tf [T, T, F, T, F, T, E, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, T, E, E, F, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, T, E, E, F, T, E, F, F] [T, T, F, T, F, T, E, F, E, T, E, F, F] (by decide +kernel) n_394) [[T, T, F, T, F, E, T, E, F, T, E, F, F], [T, T, F, T, F, T, E, E, F, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1531 (And.intro z_1540 trivial))
    trivial

theorem n_396 : UpperZero (tf [T, T, F, T, F, F, T, E, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, T, E, E, T, F, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1892)) [[T, T, F, T, F, F, E, T, E, T, F, E, F], [T, T, F, T, F, F, T, E, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1895 (And.intro z_1896 trivial))
    trivial

theorem n_397 : UpperZero (tf [T, T, F, T, F, F, T, E, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, T, E, E, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, F, T, E, E, T, E, F, F] [T, T, F, T, F, F, T, E, E, T, F, E, F] (by decide +kernel) n_396) [[T, T, F, T, F, F, E, T, E, T, E, F, F], [T, T, F, T, F, F, T, E, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1897 (And.intro z_1882 trivial))
    trivial

theorem n_398 : UpperZero (tf [T, T, F, F, E, T, T, F, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, F, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1898)) [] [([T, T, F, F, E, T, T, F, F, E, T, E, F], [T, T, F, F, E, T, T, F, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_365 trivial)

theorem n_399 : UpperZero (tf [T, T, F, F, E, T, T, F, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, F, E, T, F, E, F] (lfZero_of_reply [T, T, F, F, E, T, T, F, E, T, F, E, F] [T, T, F, F, E, T, T, F, F, T, E, E, F] (by decide +kernel) n_398) [[T, T, F, F, E, T, T, F, E, E, F, T, F]] [([T, T, F, F, E, T, E, F, T, T, F, E, F], [T, T, F, F, E, T, F, E, T, T, F, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1899 trivial)
    (And.intro n_196 trivial)

theorem n_400 : UpperZero (tf [T, T, F, F, E, T, T, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, F, E, T, E, F, F] (lfZero_of_reply [T, T, F, F, E, T, T, F, E, T, E, F, F] [T, T, F, F, E, T, T, F, E, T, F, E, F] (by decide +kernel) n_399) [[T, T, F, F, E, T, E, F, T, T, E, F, F]] [([T, T, F, F, E, T, T, F, E, E, T, F, F], [T, T, F, F, E, T, T, F, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1900 trivial)
    (And.intro n_367 trivial)

theorem n_401 : UpperZero (tf [T, T, F, T, F, E, T, F, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, T, F, E, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, E, T, F, E, T, E, F, F] [T, T, F, T, F, F, T, E, E, T, E, F, F] (by decide +kernel) n_397) [[T, T, F, T, F, E, E, F, T, T, E, F, F], [T, T, F, T, F, E, T, F, E, E, T, F, F]] [([T, T, F, E, F, T, T, F, E, T, E, F, F], [T, T, F, F, E, T, T, F, E, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1901 (And.intro z_1530 trivial))
    (And.intro n_400 trivial)

theorem n_402 : UpperZero (tf [T, T, F, T, F, F, E, T, F, T, E, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, T, F, T, E, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1890)) [[T, T, F, T, F, F, E, T, F, E, T, E, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1828 trivial)
    trivial

theorem n_403 : UpperZero (tf [T, T, F, T, F, F, E, T, E, T, F, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, T, E, T, F, E, F] (lfZero_of_reply [T, T, F, T, F, F, E, T, E, T, F, E, F] [T, T, F, T, F, F, E, T, F, T, E, E, F] (by decide +kernel) n_402) [[T, T, F, T, F, F, E, E, T, T, F, E, F], [T, T, F, T, F, F, E, T, E, E, F, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1836 (And.intro z_1837 trivial))
    trivial

theorem n_404 : UpperZero (tf [T, T, F, T, F, F, E, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, T, E, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, F, E, T, E, T, E, F, F] [T, T, F, T, F, F, E, T, E, T, F, E, F] (by decide +kernel) n_403) [[T, T, F, T, F, F, E, E, T, T, E, F, F], [T, T, F, T, F, F, E, T, E, E, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1526 (And.intro z_1527 trivial))
    trivial

theorem n_405 : UpperZero (tf [T, T, F, T, F, F, E, T, F, E, T, F, E]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, T, F, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1889)) [[T, T, F, T, F, F, E, E, F, T, T, F, E], [T, T, F, T, F, F, E, T, F, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1912 (And.intro z_1913 trivial))
    trivial

theorem n_406 : UpperZero (tf [T, T, F, T, F, F, E, T, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, T, F, E, T, E, F] (lfZero_of_reply [T, T, F, T, F, F, E, T, F, E, T, E, F] [T, T, F, T, F, F, E, T, F, E, T, F, E] (by decide +kernel) n_405) [[T, T, F, T, F, F, E, E, F, T, T, E, F], [T, T, F, T, F, F, E, T, F, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1914 (And.intro z_1880 trivial))
    trivial

theorem n_407 : UpperZero (tf [T, T, F, T, F, F, E, T, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, T, E, F, T, E, F] (lfZero_of_reply [T, T, F, T, F, F, E, T, E, F, T, E, F] [T, T, F, T, F, F, E, T, F, E, T, E, F] (by decide +kernel) n_406) [[T, T, F, T, F, F, E, E, T, F, T, E, F], [T, T, F, T, F, F, E, T, E, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1525 (And.intro z_1894 trivial))
    trivial

theorem n_408 : UpperZero (tf [T, T, F, T, F, F, E, F, T, E, T, F, E]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, F, T, E, T, F, E] ((lfZero_tf_iff _).2 (Or.inl z_1917)) [[T, T, F, T, F, F, E, F, E, T, T, F, E], [T, T, F, T, F, F, E, F, T, E, E, F, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1885 (And.intro z_1876 trivial))
    trivial

theorem n_409 : UpperZero (tf [T, T, F, T, F, F, E, F, T, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, F, T, E, T, E, F] (lfZero_of_reply [T, T, F, T, F, F, E, F, T, E, T, E, F] [T, T, F, T, F, F, E, F, T, E, T, F, E] (by decide +kernel) n_408) [[T, T, F, T, F, F, E, F, E, T, T, E, F], [T, T, F, T, F, F, E, F, T, E, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1822 (And.intro z_1524 trivial))
    trivial

theorem n_410 : UpperZero (tf [T, T, F, T, F, F, E, E, T, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, E, T, F, T, E, F] (lfZero_of_reply [T, T, F, T, F, F, E, E, T, F, T, E, F] [T, T, F, T, F, F, E, F, T, E, T, E, F] (by decide +kernel) n_409) [[T, T, F, T, F, F, E, E, T, F, E, T, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1835 trivial)
    trivial

theorem n_411 : UpperZero (tf [T, T, F, T, F, F, E, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, T, E, E, T, F, F] (lfZero_of_reply [T, T, F, T, F, F, E, T, E, E, T, F, F] [T, T, F, T, F, F, E, T, E, F, T, E, F] (by decide +kernel) n_407) [] [([T, T, F, T, F, F, E, E, T, E, T, F, F], [T, T, F, T, F, F, E, E, T, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_410 trivial)

theorem n_412 : UpperZero (tf [T, T, F, T, F, E, F, T, E, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, F, T, E, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, E, F, T, E, T, E, F, F] [T, T, F, T, F, F, E, T, E, T, E, F, F] (by decide +kernel) n_404) [[T, T, F, T, F, E, F, E, T, T, E, F, F]] [([T, T, F, E, F, T, F, T, E, T, E, F, F], [T, T, F, F, E, T, F, T, E, T, E, F, F]), ([T, T, F, T, F, E, F, T, E, E, T, F, F], [T, T, F, T, F, F, E, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1872 trivial)
    (And.intro n_201 (And.intro n_411 trivial))

theorem n_413 : UpperZero (tf [T, T, F, T, F, F, E, F, T, F, E, T, E]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, F, T, F, E, T, E] ((lfZero_tf_iff _).2 (Or.inl z_1919)) [[T, T, F, T, F, F, E, F, E, F, T, T, E], [T, T, F, T, F, F, E, F, T, F, E, E, T]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1923 (And.intro z_1924 trivial))
    trivial

theorem n_414 : UpperZero (tf [T, T, F, T, F, F, T, F, E, E, F, T, E]) :=
  upperZero_of_pairs [T, T, F, T, F, F, T, F, E, E, F, T, E] ((lfZero_tf_iff _).2 (Or.inl z_1921)) [[T, T, F, T, F, F, T, F, E, E, F, E, T]] [([T, T, F, T, F, F, E, F, T, E, F, T, E], [T, T, F, T, F, F, E, F, T, F, E, T, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1925 trivial)
    (And.intro n_413 trivial)

theorem n_415 : UpperZero (tf [T, T, F, T, F, F, T, F, E, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, T, F, E, E, T, E, F] ((lfZero_tf_iff _).2 (Or.inl z_1922)) [] [([T, T, F, T, F, F, E, F, T, E, T, E, F], [T, T, F, T, F, F, E, F, T, E, T, F, E]), ([T, T, F, T, F, F, T, F, E, E, E, T, F], [T, T, F, T, F, F, T, F, E, E, F, T, E])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_408 (And.intro n_414 trivial))

theorem n_416 : UpperZero (tf [T, T, F, T, F, F, T, E, F, E, T, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, T, E, F, E, T, E, F] (lfZero_of_reply [T, T, F, T, F, F, T, E, F, E, T, E, F] [T, T, F, T, F, F, T, F, E, E, T, E, F] (by decide +kernel) n_415) [[T, T, F, T, F, F, T, E, F, E, E, T, F]] [([T, T, F, T, F, F, E, T, F, E, T, E, F], [T, T, F, T, F, F, E, T, F, E, T, F, E])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1926 trivial)
    (And.intro n_405 trivial)

theorem n_417 : UpperZero (tf [T, T, F, T, F, F, T, E, E, F, T, E, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, T, E, E, F, T, E, F] (lfZero_of_reply [T, T, F, T, F, F, T, E, E, F, T, E, F] [T, T, F, T, F, F, T, E, F, E, T, E, F] (by decide +kernel) n_416) [[T, T, F, T, F, F, T, E, E, F, E, T, F]] [([T, T, F, T, F, F, E, T, E, F, T, E, F], [T, T, F, T, F, F, E, T, F, E, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1891 trivial)
    (And.intro n_406 trivial)

theorem n_418 : UpperZero (tf [T, T, F, T, F, F, T, E, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, T, E, E, E, T, F, F] (lfZero_of_reply [T, T, F, T, F, F, T, E, E, E, T, F, F] [T, T, F, T, F, F, T, E, E, F, T, E, F] (by decide +kernel) n_417) [] [([T, T, F, T, F, F, E, T, E, E, T, F, F], [T, T, F, T, F, F, E, T, E, F, T, E, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_407 trivial)

theorem n_419 : UpperZero (tf [T, T, F, T, F, E, T, F, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, T, F, E, E, T, F, F] (lfZero_of_reply [T, T, F, T, F, E, T, F, E, E, T, F, F] [T, T, F, T, F, F, T, E, E, E, T, F, F] (by decide +kernel) n_418) [[T, T, F, T, F, E, E, F, T, E, T, F, F]] [([T, T, F, E, F, T, T, F, E, E, T, F, F], [T, T, F, F, E, T, T, F, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1928 trivial)
    (And.intro n_368 trivial)

theorem n_420 : UpperZero (tf [T, T, F, T, F, E, T, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, T, E, F, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, E, T, E, F, T, E, F, F] [T, T, F, T, F, E, T, F, E, T, E, F, F] (by decide +kernel) n_401) [[T, T, F, E, F, T, T, E, F, T, E, F, F]] [([T, T, F, T, F, E, E, T, F, T, E, F, F], [T, T, F, T, F, E, F, T, E, T, E, F, F]), ([T, T, F, T, F, E, T, E, F, E, T, F, F], [T, T, F, T, F, E, T, F, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1909 trivial)
    (And.intro n_412 (And.intro n_419 trivial))

theorem n_421 : UpperZero (tf [T, T, F, T, F, T, E, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, T, E, E, E, T, F, F, F] (lfZero_of_reply [T, T, F, T, F, T, E, E, E, T, F, F, F] [T, T, F, T, F, T, E, E, F, T, E, F, F] (by decide +kernel) n_395) [] [([T, T, F, T, F, E, T, E, E, T, F, F, F], [T, T, F, T, F, E, T, E, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_420 trivial)

theorem n_422 : UpperZero (tf [T, T, F, T, F, F, E, E, T, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, F, E, E, T, E, T, F, F] (lfZero_of_reply [T, T, F, T, F, F, E, E, T, E, T, F, F] [T, T, F, T, F, F, E, E, T, F, T, E, F] (by decide +kernel) n_410) [[T, T, F, T, F, F, E, E, E, T, T, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1929 trivial)
    trivial

theorem n_423 : UpperZero (tf [T, T, F, T, F, E, F, T, E, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, F, T, E, E, T, F, F] (lfZero_of_reply [T, T, F, T, F, E, F, T, E, E, T, F, F] [T, T, F, T, F, F, E, T, E, E, T, F, F] (by decide +kernel) n_411) [] [([T, T, F, E, F, T, F, T, E, E, T, F, F], [T, T, F, F, E, T, F, T, E, E, T, F, F]), ([T, T, F, T, F, E, F, E, T, E, T, F, F], [T, T, F, T, F, F, E, E, T, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_240 (And.intro n_422 trivial))

theorem n_424 : UpperZero (tf [T, T, F, T, F, E, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, E, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, T, F, E, E, T, F, T, E, F, F] [T, T, F, T, F, E, F, T, E, T, E, F, F] (by decide +kernel) n_412) [] [([T, T, F, E, F, T, E, T, F, T, E, F, F], [T, T, F, F, E, T, E, T, F, T, E, F, F]), ([T, T, F, T, F, E, E, T, F, E, T, F, F], [T, T, F, T, F, E, F, T, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_241 (And.intro n_423 trivial))

theorem n_425 : UpperZero (tf [T, T, F, T, F, E, E, T, F, E, T, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, E, T, F, E, T, F, F] (lfZero_of_reply [T, T, F, T, F, E, E, T, F, E, T, F, F] [T, T, F, T, F, E, F, T, E, E, T, F, F] (by decide +kernel) n_423) [[T, T, F, T, F, E, E, E, F, T, T, F, F]] [([T, T, F, E, F, T, E, T, F, E, T, F, F], [T, T, F, F, E, T, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1930 trivial)
    (And.intro n_249 trivial)

theorem n_426 : UpperZero (tf [T, T, F, T, E, F, E, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, E, F, E, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, T, E, F, E, T, F, T, E, F, F] [T, T, F, T, F, E, E, T, F, T, E, F, F] (by decide +kernel) n_424) [] [([T, T, F, E, T, F, E, T, F, T, E, F, F], [T, T, F, F, T, E, E, T, F, T, E, F, F]), ([T, T, F, T, E, F, E, T, F, E, T, F, F], [T, T, F, T, F, E, E, T, F, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_207 (And.intro n_425 trivial))

theorem n_427 : UpperZero (tf [T, T, F, T, E, E, F, T, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, T, E, E, F, T, F, T, E, F, F] (lfZero_of_reply [T, T, F, T, E, E, F, T, F, T, E, F, F] [T, T, F, T, E, F, E, T, F, T, E, F, F] (by decide +kernel) n_426) [[T, T, F, T, E, E, F, T, F, E, T, F, F]] [([T, T, F, E, T, E, F, T, F, T, E, F, F], [T, T, F, E, T, F, E, T, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1932 trivial)
    (And.intro n_208 trivial)

theorem n_428 : UpperZero (tf [T, T, F, T, E, T, F, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, F, T, E, T, F, E, E, T, F, F, F] (lfZero_of_reply [T, T, F, T, E, T, F, E, E, T, F, F, F] [T, T, F, T, F, T, E, E, E, T, F, F, F] (by decide +kernel) n_421) [] [([T, T, F, E, T, T, F, E, E, T, F, F, F], [T, T, F, E, T, T, F, E, F, T, E, F, F]), ([T, T, F, T, E, E, F, T, E, T, F, F, F], [T, T, F, T, E, E, F, T, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_209 (And.intro n_427 trivial))

theorem n_429 : UpperZero (tf [T, T, F, F, E, T, T, E, F, T, E, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, E, F, T, E, F, F] (lfZero_of_reply [T, T, F, F, E, T, T, E, F, T, E, F, F] [T, T, F, F, E, T, T, F, E, T, E, F, F] (by decide +kernel) n_400) [] [([T, T, F, F, E, T, E, T, F, T, E, F, F], [T, T, F, F, E, T, F, T, E, T, E, F, F]), ([T, T, F, F, E, T, T, E, F, E, T, F, F], [T, T, F, F, E, T, T, F, E, E, T, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_201 (And.intro n_368 trivial))

theorem n_430 : UpperZero (tf [T, T, F, F, E, T, T, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, F, F, E, T, T, E, E, T, F, F, F] (lfZero_of_reply [T, T, F, F, E, T, T, E, E, T, F, F, F] [T, T, F, F, E, T, T, E, F, T, E, F, F] (by decide +kernel) n_429) [] [([T, T, F, F, E, T, E, T, E, T, F, F, F], [T, T, F, F, E, T, E, T, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_241 trivial)

theorem n_431 : UpperZero (tf [T, T, F, T, F, E, T, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, F, T, F, E, T, E, E, T, F, F, F] (lfZero_of_reply [T, T, F, T, F, E, T, E, E, T, F, F, F] [T, T, F, T, F, E, T, E, F, T, E, F, F] (by decide +kernel) n_420) [] [([T, T, F, E, F, T, T, E, E, T, F, F, F], [T, T, F, F, E, T, T, E, E, T, F, F, F]), ([T, T, F, T, F, E, E, T, E, T, F, F, F], [T, T, F, T, F, E, E, T, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_430 (And.intro n_424 trivial))

theorem n_432 : UpperZero (tf [T, T, F, T, E, F, T, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, F, T, E, F, T, E, E, T, F, F, F] (lfZero_of_reply [T, T, F, T, E, F, T, E, E, T, F, F, F] [T, T, F, T, F, E, T, E, E, T, F, F, F] (by decide +kernel) n_431) [] [([T, T, F, E, T, F, T, E, E, T, F, F, F], [T, T, F, E, T, F, T, E, F, T, E, F, F]), ([T, T, F, T, E, F, E, T, E, T, F, F, F], [T, T, F, T, E, F, E, T, F, T, E, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_370 (And.intro n_426 trivial))

theorem n_433 : UpperZero (tf [T, T, F, T, E, T, E, F, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, F, T, E, T, E, F, E, T, F, F, F] (lfZero_of_reply [T, T, F, T, E, T, E, F, E, T, F, F, F] [T, T, F, T, E, T, F, E, E, T, F, F, F] (by decide +kernel) n_428) [] [([T, T, F, E, T, T, E, F, E, T, F, F, F], [T, T, F, E, T, T, F, E, E, T, F, F, F]), ([T, T, F, T, E, E, T, F, E, T, F, F, F], [T, T, F, T, E, F, T, E, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_252 (And.intro n_432 trivial))

theorem n_434 : UpperZero (tf [T, T, T, E, F, F, T, E, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, F, F, T, E, E, T, F, F, F] (lfZero_of_reply [T, T, T, E, F, F, T, E, E, T, F, F, F] [T, T, T, F, E, F, T, E, E, T, F, F, F] (by decide +kernel) n_386) [] [([T, T, E, T, F, F, T, E, E, T, F, F, F], [T, T, F, T, E, F, T, E, E, T, F, F, F]), ([T, T, T, E, F, F, E, T, E, T, F, F, F], [T, T, T, F, E, F, E, T, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_432 (And.intro n_259 trivial))

theorem n_435 : UpperZero (tf [T, T, T, E, F, T, E, F, E, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, F, T, E, F, E, T, F, F, F] (lfZero_of_reply [T, T, T, E, F, T, E, F, E, T, F, F, F] [T, T, T, F, E, T, E, F, E, T, F, F, F] (by decide +kernel) n_387) [] [([T, T, E, T, F, T, E, F, E, T, F, F, F], [T, T, F, T, E, T, E, F, E, T, F, F, F]), ([T, T, T, E, F, E, T, F, E, T, F, F, F], [T, T, T, E, F, F, T, E, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_433 (And.intro n_434 trivial))

theorem n_436 : UpperZero (tf [T, T, T, T, F, E, E, E, F, T, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, F, E, E, E, F, T, F, F, F] (lfZero_of_reply [T, T, T, T, F, E, E, E, F, T, F, F, F] [T, T, T, T, F, E, E, F, E, T, F, F, F] (by decide +kernel) n_326) [] [([T, T, T, E, F, T, E, E, F, T, F, F, F], [T, T, T, E, F, T, E, F, E, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_435 trivial)

theorem n_437 : UpperZero (tf [T, T, T, T, E, F, E, T, F, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, E, F, E, T, F, E, F, F, F] (lfZero_of_reply [T, T, T, T, E, F, E, T, F, E, F, F, F] [T, T, T, T, F, E, E, T, F, E, F, F, F] (by decide +kernel) n_315) [] [([T, T, T, E, T, F, E, T, F, E, F, F, F], [T, T, T, F, T, E, E, T, F, E, F, F, F]), ([T, T, T, T, E, F, E, E, F, T, F, F, F], [T, T, T, T, F, E, E, E, F, T, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_262 (And.intro n_436 trivial))

theorem n_438 : UpperZero (tf [T, T, T, T, E, F, T, E, E, F, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, E, F, T, E, E, F, F, F, F] (lfZero_of_reply [T, T, T, T, E, F, T, E, E, F, F, F, F] [T, T, T, T, F, E, T, E, E, F, F, F, F] (by decide +kernel) n_316) [] [([T, T, T, E, T, F, T, E, E, F, F, F, F], [T, T, T, E, T, F, T, E, F, E, F, F, F]), ([T, T, T, T, E, F, E, T, E, F, F, F, F], [T, T, T, T, E, F, E, T, F, E, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_263 (And.intro n_437 trivial))

theorem n_439 : UpperZero (tf [T, T, T, T, E, T, E, F, E, F, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, E, T, E, F, E, F, F, F, F] (lfZero_of_mirror_dec [T, T, T, T, E, T, E, F, E, F, F, F, F] (by decide +kernel)) [] [([T, T, T, E, T, T, E, F, E, F, F, F, F], [T, T, T, E, T, T, E, F, F, E, F, F, F]), ([T, T, T, T, E, E, T, F, E, F, F, F, F], [T, T, T, T, E, F, T, E, E, F, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_264 (And.intro n_438 trivial))

theorem n_440 : UpperZero (tf [T, T, T, T, T, E, E, E, F, F, F, F, F]) :=
  upperZero_of_pairs [T, T, T, T, T, E, E, E, F, F, F, F, F] (lfZero_of_mirror_dec [T, T, T, T, T, E, E, E, F, F, F, F, F] (by decide +kernel)) [] [([T, T, T, T, E, T, E, E, F, F, F, F, F], [T, T, T, T, E, T, E, F, E, F, F, F, F])]
    (by decide +kernel) (by decide +kernel)
    trivial
    (And.intro n_439 trivial)

theorem infinitesimal : Infinitesimal (tf (start 5 3)) := by
  rw [infinitesimal_start_iff, show start 5 3 = [T, T, T, T, T, E, E, E, F, F, F, F, F] from by decide]
  exact n_440

end Cgt.Cert_5_3
