import Cgt.Certificate

/-! Machine-generated certificate: `T^3 □^4 F^3` is infinitesimal. -/

namespace Cgt.Cert_3_4
open Cell Game

theorem z_0 : le (tf [F, F, F, E, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1 : le (tf [F, F, E, F, E, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, E, T, E, T, T] [([F, F, E, F, E, E, E, T, T, T], [F, F, F, E, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_0 trivial)

theorem z_2 : le (tf [F, F, E, E, F, T, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, T, E, E, T, T] [([F, F, E, E, F, E, T, E, T, T], [F, F, E, F, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_3 : le (tf [F, F, E, E, E, T, F, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, F, T, E, T] [([F, F, E, E, E, T, F, E, T, T], [F, F, E, E, F, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 trivial)

theorem z_4 : le (tf [F, F, E, E, E, T, T, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, T, E, F, T] [([F, F, E, E, E, T, E, T, F, T], [F, F, E, E, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 trivial)

theorem z_5 : le (tf [F, E, F, E, E, T, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, T, T, F, E] [([F, E, F, E, E, T, T, E, F, T], [F, F, E, E, E, T, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_4 trivial)

theorem z_6 : le (tf [F, F, E, E, T, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, E, T, F, T] [([F, F, E, E, E, T, E, T, F, T], [F, F, E, E, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 trivial)

theorem z_7 : le (tf [F, E, F, E, T, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, T, E, F, T] [([F, E, F, E, E, T, T, E, F, T], [F, F, E, E, E, T, T, E, F, T]), ([F, E, F, E, T, E, E, T, F, T], [F, F, E, E, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_4 (And.intro z_6 trivial))

theorem z_8 : le (tf [F, E, E, F, T, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, T, T, F, E] [([F, E, E, F, E, T, T, T, F, E], [F, E, F, E, E, T, T, T, F, E]), ([F, E, E, F, T, E, T, E, F, T], [F, E, F, E, T, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_5 (And.intro z_7 trivial))

theorem z_9 : le (tf [F, F, E, E, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_10 : le (tf [F, E, F, E, E, T, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, T, F, T] [([F, E, F, E, E, E, T, T, F, T], [F, F, E, E, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_9 trivial)

theorem z_11 : le (tf [F, E, E, F, E, T, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, T, E, F, T] [([F, E, E, F, E, T, E, T, F, T], [F, E, F, E, E, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_10 trivial)

theorem z_12 : le (tf [F, E, F, T, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, E, E, T, F, T] [([F, E, F, E, T, E, E, T, F, T], [F, F, E, E, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_6 trivial)

theorem z_13 : le (tf [F, E, E, T, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, T, E, F, T] [([F, E, E, E, F, T, T, E, F, T], [F, E, E, F, E, T, T, E, F, T]), ([F, E, E, T, F, E, E, T, F, T], [F, E, F, T, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 (And.intro z_12 trivial))

theorem z_14 : le (tf [F, E, E, T, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, T, T, F, E] [([F, E, E, E, T, F, T, T, F, E], [F, E, E, F, T, E, T, T, F, E]), ([F, E, E, T, E, F, T, E, F, T], [F, E, E, T, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_8 (And.intro z_13 trivial))

theorem z_15 : le (tf [F, E, E, T, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, T, F, E, E, F, T] [([F, E, E, T, E, F, T, E, F, T], [F, E, E, T, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 trivial)

theorem z_16 : le (tf [E, F, E, T, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, T, F, E, T, F, E] [([E, F, E, T, E, F, T, T, F, E], [F, E, E, T, E, F, T, T, F, E]), ([E, F, E, T, T, F, E, E, F, T], [F, E, E, T, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_14 (And.intro z_15 trivial))

theorem z_17 : le (tf [E, F, E, T, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, F, T, E, E, F] [([E, F, E, T, T, F, E, T, E, F], [E, F, E, T, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_16 trivial)

theorem z_18 : le (tf [E, F, E, T, T, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, T, E, F, E, F] [([E, F, E, T, T, E, T, F, E, F], [E, F, E, T, T, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_17 trivial)

theorem z_19 : le (tf [F, E, E, E, F, T, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, T, T, F, E] [([F, E, E, E, F, T, T, E, F, T], [F, E, E, F, E, T, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 trivial)

theorem z_20 : le (tf [E, F, E, T, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, T, T, F, E] [([E, F, E, E, F, T, T, T, F, E], [F, E, E, E, F, T, T, T, F, E]), ([E, F, E, T, F, E, T, E, F, T], [F, E, E, T, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_19 (And.intro z_13 trivial))

theorem z_21 : le (tf [F, F, E, E, T, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, F, E, T, T] [([F, F, E, E, E, T, F, E, T, T], [F, F, E, E, F, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 trivial)

theorem z_22 : le (tf [F, E, F, E, T, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, F, T, E, T] [([F, E, F, E, E, T, F, T, E, T], [F, F, E, E, E, T, F, T, E, T]), ([F, E, F, E, T, E, F, E, T, T], [F, F, E, E, T, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 (And.intro z_21 trivial))

theorem z_23 : le (tf [F, F, E, E, F, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_24 : le (tf [F, F, E, E, E, F, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, T, E, T, T] [([F, F, E, E, E, F, E, T, T, T], [F, F, E, E, F, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_23 trivial)

theorem z_25 : le (tf [F, E, F, E, T, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, F, E, E, T, T] [([F, E, F, E, E, F, T, E, T, T], [F, F, E, E, E, F, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 trivial)

theorem z_26 : le (tf [F, E, T, F, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, F, E, E, T, T] [([F, E, E, F, T, F, E, E, T, T], [F, E, F, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 trivial)

theorem z_27 : le (tf [F, E, T, F, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, F, T, E, T] [([F, E, E, F, T, E, F, T, E, T], [F, E, F, E, T, E, F, T, E, T]), ([F, E, T, F, E, E, F, E, T, T], [F, E, T, F, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 (And.intro z_26 trivial))

theorem z_28 : le (tf [F, E, T, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, T, E, F, T] [([F, E, E, F, T, E, T, E, F, T], [F, E, F, E, T, E, T, E, F, T]), ([F, E, T, F, E, E, E, T, F, T], [F, E, T, F, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_7 (And.intro z_27 trivial))

theorem z_29 : le (tf [F, T, E, F, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, E, T, F, T] [([F, E, T, F, E, E, E, T, F, T], [F, E, T, F, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_27 trivial)

theorem z_30 : le (tf [F, T, E, E, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, T, E, F, T] [([F, E, T, E, F, E, T, E, F, T], [F, E, T, F, E, E, T, E, F, T]), ([F, T, E, E, F, E, E, T, F, T], [F, T, E, F, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_28 (And.intro z_29 trivial))

theorem z_31 : le (tf [E, T, F, E, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, T, T, F, E] [([E, E, F, T, F, E, T, T, F, E], [E, F, E, T, F, E, T, T, F, E]), ([E, T, F, E, F, E, T, E, F, T], [F, T, E, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_20 (And.intro z_30 trivial))

theorem z_32 : le (tf [F, F, E, E, E, T, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, E, F, T, T] [([F, F, E, E, E, E, T, F, T, T], [F, F, E, E, E, F, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 trivial)

theorem z_33 : le (tf [F, E, F, E, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, T, F, E, T] [([F, E, F, E, E, T, E, F, T, T], [F, F, E, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 trivial)

theorem z_34 : le (tf [F, E, F, E, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, F, T, T] [([F, E, F, E, E, T, E, F, T, T], [F, F, E, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 trivial)

theorem z_35 : le (tf [F, E, E, F, T, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, T, F, E, T] [([F, E, E, F, E, T, T, F, E, T], [F, E, F, E, E, T, T, F, E, T]), ([F, E, E, F, T, E, E, F, T, T], [F, E, F, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_33 (And.intro z_34 trivial))

theorem z_36 : le (tf [F, E, F, E, E, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_37 : le (tf [F, E, E, F, E, T, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, F, T, T] [([F, E, E, F, E, E, T, F, T, T], [F, E, F, E, E, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_36 trivial)

theorem z_38 : le (tf [F, E, E, T, F, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, F, T, T] [([F, E, E, E, F, T, E, F, T, T], [F, E, E, F, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_37 trivial)

theorem z_39 : le (tf [F, E, E, T, E, F, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, T, F, E, T] [([F, E, E, E, T, F, T, F, E, T], [F, E, E, F, T, E, T, F, E, T]), ([F, E, E, T, E, F, E, F, T, T], [F, E, E, T, F, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_35 (And.intro z_38 trivial))

theorem z_40 : le (tf [E, F, E, T, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, T, F, E, F, E, T] [([E, F, E, T, E, F, T, F, E, T], [F, E, E, T, E, F, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_39 trivial)

theorem z_41 : le (tf [F, E, E, E, F, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, T, F, E, T] [([F, E, E, E, F, T, E, F, T, T], [F, E, E, F, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_37 trivial)

theorem z_42 : le (tf [E, F, E, T, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, T, F, E, T] [([E, F, E, E, F, T, T, F, E, T], [F, E, E, E, F, T, T, F, E, T]), ([E, F, E, T, F, E, E, F, T, T], [F, E, E, T, F, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_41 (And.intro z_38 trivial))

theorem z_43 : le (tf [F, E, T, F, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, F, T, T] [([F, E, E, F, T, E, E, F, T, T], [F, E, F, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_34 trivial)

theorem z_44 : le (tf [F, T, E, E, F, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, F, T, T] [([F, E, T, E, F, E, E, F, T, T], [F, E, T, F, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_43 trivial)

theorem z_45 : le (tf [E, T, F, E, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, T, F, E, T] [([E, E, F, T, F, E, T, F, E, T], [E, F, E, T, F, E, T, F, E, T]), ([E, T, F, E, F, E, E, F, T, T], [F, T, E, E, F, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_42 (And.intro z_44 trivial))

theorem z_46 : le (tf [E, T, F, E, T, F, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, T, F, E, F, E, T] [([E, E, F, T, T, F, E, F, E, T], [E, F, E, T, T, F, E, F, E, T]), ([E, T, F, E, E, F, T, F, E, T], [E, T, F, E, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_40 (And.intro z_45 trivial))

theorem z_47 : le (tf [E, T, F, E, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, T, F, E, T, F, E] [([E, E, F, T, T, F, E, T, F, E], [E, F, E, T, T, F, E, T, F, E]), ([E, T, F, E, E, F, T, T, F, E], [E, T, F, E, F, E, T, T, F, E]), ([E, T, F, E, T, F, E, E, F, T], [E, T, F, E, T, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_16 (And.intro z_31 (And.intro z_46 trivial)))

theorem z_48 : le (tf [E, T, F, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, F, T, E, E, F] [([E, E, F, T, T, F, T, E, E, F], [E, F, E, T, T, F, T, E, E, F]), ([E, T, F, E, T, F, E, T, E, F], [E, T, F, E, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_17 (And.intro z_47 trivial))

theorem z_49 : le (tf [E, T, F, E, T, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, T, E, F, E, F] [([E, E, F, T, T, T, E, F, E, F], [E, F, E, T, T, T, E, F, E, F]), ([E, T, F, E, T, E, T, F, E, F], [E, T, F, E, T, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_18 (And.intro z_48 trivial))

theorem z_50 : le (tf [E, T, T, F, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, F, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_51 : le (tf [E, T, T, F, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, E, F, T, E] [([E, T, T, F, F, E, E, F, E, T], [E, T, T, F, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_50 trivial)

theorem z_52 : le (tf [E, T, T, F, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, F, E, E, T, E, F] [([E, T, T, F, F, E, E, E, T, F], [E, T, T, F, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 trivial)

theorem z_53 : le (tf [E, T, T, F, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, F, T, E, E, F] [([E, T, E, F, T, F, T, E, E, F], [E, T, F, E, T, F, T, E, E, F]), ([E, T, T, F, E, F, E, T, E, F], [E, T, T, F, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_52 trivial))

theorem z_54 : le (tf [E, T, T, F, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, T, E, F, E, F] [([E, T, E, F, T, T, E, F, E, F], [E, T, F, E, T, T, E, F, E, F]), ([E, T, T, F, E, E, T, F, E, F], [E, T, T, F, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_49 (And.intro z_53 trivial))

theorem z_55 : le (tf [E, T, T, F, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, F, T, E, E, E, F, F] [([E, T, T, F, E, T, E, E, F, F], [E, T, T, F, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_54 trivial)

theorem z_56 : le (tf [E, T, T, T, E, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, E, F, E, E, F, F] [([E, T, T, E, T, F, E, E, F, F], [E, T, T, F, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_55 trivial)

theorem z_57 : le (tf [E, E, T, T, T, F, F, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, T, T, F, F, E, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_58 : le (tf [E, T, E, T, T, F, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, T, F, F, E, E, F] [([E, E, T, T, T, F, F, E, E, F], [E, E, T, T, T, F, F, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_57 trivial)

theorem z_59 : le (tf [F, E, E, E, T, F, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, T, F, T, E] [([F, E, E, E, T, F, T, F, E, T], [F, E, E, F, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_35 trivial)

theorem z_60 : le (tf [F, E, F, E, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_61 : le (tf [F, E, E, F, E, T, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, T, T, F] [([F, E, E, F, E, E, T, T, T, F], [F, E, F, E, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_60 trivial)

theorem z_62 : le (tf [F, E, E, T, F, E, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, T, T, F] [([F, E, E, E, F, T, E, T, T, F], [F, E, E, F, E, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_61 trivial)

theorem z_63 : le (tf [F, E, E, T, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, T, E, T, F] [([F, E, E, E, T, F, T, E, T, F], [F, E, E, E, T, F, T, F, T, E]), ([F, E, E, T, E, F, E, T, T, F], [F, E, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_59 (And.intro z_62 trivial))

theorem z_64 : le (tf [E, F, E, T, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, F, E, E, T, F] [([E, F, E, T, E, F, T, E, T, F], [F, E, E, T, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_63 trivial)

theorem z_65 : le (tf [F, E, E, E, F, T, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, T, E, T, F] [([F, E, E, E, F, T, E, T, T, F], [F, E, E, F, E, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_61 trivial)

theorem z_66 : le (tf [E, F, E, T, F, E, T, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, T, E, T, F] [([E, F, E, E, F, T, T, E, T, F], [F, E, E, E, F, T, T, E, T, F]), ([E, F, E, T, F, E, E, T, T, F], [F, E, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_65 (And.intro z_62 trivial))

theorem z_67 : le (tf [E, T, F, F, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_68 : le (tf [E, T, F, E, F, E, T, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, T, E, T, F] [([E, E, F, T, F, E, T, E, T, F], [E, F, E, T, F, E, T, E, T, F]), ([E, T, F, E, F, E, E, T, T, F], [E, T, F, F, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 (And.intro z_67 trivial))

theorem z_69 : le (tf [E, T, F, E, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, F, E, E, T, F] [([E, E, F, T, T, F, E, E, T, F], [E, F, E, T, T, F, E, E, T, F]), ([E, T, F, E, E, F, T, E, T, F], [E, T, F, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_64 (And.intro z_68 trivial))

theorem z_70 : le (tf [E, T, F, T, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, F, E, T, F] [([E, T, F, E, T, E, F, E, T, F], [E, T, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 trivial)

theorem z_71 : le (tf [E, T, F, T, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, T, F, E, F] [([E, T, F, E, T, E, T, F, E, F], [E, T, F, E, T, F, T, E, E, F]), ([E, T, F, T, E, E, E, F, T, F], [E, T, F, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_70 trivial))

theorem z_72 : le (tf [F, E, E, E, F, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_73 : le (tf [F, E, E, E, T, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, T, T, F] [([F, E, E, E, E, F, T, T, T, F], [F, E, E, E, F, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_72 trivial)

theorem z_74 : le (tf [F, E, E, E, T, T, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, F, E, T, F] [([F, E, E, E, T, E, F, T, T, F], [F, E, E, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 trivial)

theorem z_75 : le (tf [F, E, E, E, T, T, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, T, F, E, F] [([F, E, E, E, T, T, E, F, T, F], [F, E, E, E, T, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_74 trivial)

theorem z_76 : le (tf [F, E, E, T, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, F, T, F] [([F, E, E, E, T, T, E, F, T, F], [F, E, E, E, T, T, F, E, T, F]), ([F, E, E, T, E, E, T, F, T, F], [F, E, E, T, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_74 (And.intro z_63 trivial))

theorem z_77 : le (tf [E, F, E, T, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, T, F, E, F] [([E, F, E, E, T, T, T, F, E, F], [F, E, E, E, T, T, T, F, E, F]), ([E, F, E, T, E, T, E, F, T, F], [F, E, E, T, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_75 (And.intro z_76 trivial))

theorem z_78 : le (tf [F, E, E, T, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, T, T, F] [([F, E, E, E, T, E, F, T, T, F], [F, E, E, E, T, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 trivial)

theorem z_79 : le (tf [E, F, E, T, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, F, E, T, F] [([E, F, E, E, T, T, F, E, T, F], [F, E, E, E, T, T, F, E, T, F]), ([E, F, E, T, E, E, F, T, T, F], [F, E, E, T, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_74 (And.intro z_78 trivial))

theorem z_80 : le (tf [F, E, T, E, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, T, T, F] [([F, E, E, T, E, F, E, T, T, F], [F, E, E, T, F, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_62 trivial)

theorem z_81 : le (tf [F, T, E, E, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, T, T, F] [([F, E, T, E, E, E, F, T, T, F], [F, E, T, E, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 trivial)

theorem z_82 : le (tf [E, T, F, E, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, F, E, T, F] [([E, E, F, T, E, T, F, E, T, F], [E, F, E, T, E, T, F, E, T, F]), ([E, T, F, E, E, E, F, T, T, F], [F, T, E, E, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 (And.intro z_81 trivial))

theorem z_83 : le (tf [E, T, F, E, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, T, F, E, F] [([E, E, F, T, E, T, T, F, E, F], [E, F, E, T, E, T, T, F, E, F]), ([E, T, F, E, E, T, E, F, T, F], [E, T, F, E, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 (And.intro z_82 trivial))

theorem z_84 : le (tf [F, E, T, E, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, T, F, T, F] [([F, E, E, T, E, E, T, F, T, F], [F, E, E, T, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_63 trivial)

theorem z_85 : le (tf [T, F, E, E, E, E, T, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, T, F, T, F] [([E, F, T, E, E, E, T, F, T, F], [F, E, T, E, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 trivial)

theorem z_86 : le (tf [T, E, F, E, E, T, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, E, F, T, F] [([E, T, F, E, E, T, E, F, T, F], [E, T, F, E, E, T, F, E, T, F]), ([T, E, F, E, E, E, T, F, T, F], [T, F, E, E, E, E, T, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_85 trivial))

theorem z_87 : le (tf [T, E, E, F, E, T, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, T, F, E, F] [([E, T, E, F, E, T, T, F, E, F], [E, T, F, E, E, T, T, F, E, F]), ([T, E, E, F, E, T, E, F, T, F], [T, E, F, E, E, T, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 (And.intro z_86 trivial))

theorem z_88 : le (tf [T, E, F, E, E, E, F, T, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, F, T, T, F] [([E, T, F, E, E, E, F, T, T, F], [F, T, E, E, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 trivial)

theorem z_89 : le (tf [T, E, E, F, E, T, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, F, E, T, F] [([E, T, E, F, E, T, F, E, T, F], [E, T, F, E, E, T, F, E, T, F]), ([T, E, E, F, E, E, F, T, T, F], [T, E, F, E, E, E, F, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_88 trivial))

theorem z_90 : le (tf [T, E, E, T, F, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, F, E, T, F] [([E, T, E, T, F, E, F, E, T, F], [E, T, F, T, E, E, F, E, T, F]), ([T, E, E, E, F, T, F, E, T, F], [T, E, E, F, E, T, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 (And.intro z_89 trivial))

theorem z_91 : le (tf [T, E, E, T, F, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, T, F, E, F] [([E, T, E, T, F, E, T, F, E, F], [E, T, F, T, E, E, T, F, E, F]), ([T, E, E, E, F, T, T, F, E, F], [T, E, E, F, E, T, T, F, E, F]), ([T, E, E, T, F, E, E, F, T, F], [T, E, E, T, F, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_71 (And.intro z_87 (And.intro z_90 trivial)))

theorem z_92 : le (tf [T, E, E, T, T, F, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, T, F, E, F, E, F] [([E, T, E, T, T, F, E, F, E, F], [E, T, E, T, T, F, F, E, E, F]), ([T, E, E, T, E, F, T, F, E, F], [T, E, E, T, F, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_58 (And.intro z_91 trivial))

theorem z_93 : le (tf [F, E, E, E, T, T, F, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, F, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_94 : le (tf [F, E, E, E, T, T, F, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, F, T, F, E] [([F, E, E, E, T, T, F, E, F, T], [F, E, E, E, T, T, F, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 trivial)

theorem z_95 : le (tf [F, E, E, F, T, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, T, F, T] [([F, E, E, F, E, T, E, T, F, T], [F, E, F, E, E, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_10 trivial)

theorem z_96 : le (tf [F, E, E, T, E, F, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, T, F, T] [([F, E, E, E, T, F, E, T, F, T], [F, E, E, F, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_95 trivial)

theorem z_97 : le (tf [F, E, E, T, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, F, E, F, T] [([F, E, E, E, T, T, F, E, F, T], [F, E, E, E, T, T, F, F, E, T]), ([F, E, E, T, E, E, F, T, F, T], [F, E, E, T, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 (And.intro z_96 trivial))

theorem z_98 : le (tf [E, F, E, T, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, F, T, F, E] [([E, F, E, E, T, T, F, T, F, E], [F, E, E, E, T, T, F, T, F, E]), ([E, F, E, T, E, T, F, E, F, T], [F, E, E, T, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_94 (And.intro z_97 trivial))

theorem z_99 : le (tf [E, F, E, T, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, F, T, E, F] [([E, F, E, T, E, T, F, T, E, F], [E, F, E, T, E, T, F, T, F, E]), ([E, F, E, T, T, E, F, E, T, F], [E, F, E, T, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_98 (And.intro z_64 trivial))

theorem z_100 : le (tf [E, F, E, T, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, T, E, F, F] [([E, F, E, T, E, T, T, E, F, F], [E, F, E, T, E, T, T, F, E, F]), ([E, F, E, T, T, E, E, T, F, F], [E, F, E, T, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 (And.intro z_99 trivial))

theorem z_101 : le (tf [E, F, E, T, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, T, E, E, F, T] [([E, F, E, T, F, E, T, E, F, T], [F, E, E, T, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 trivial)

theorem z_102 : le (tf [E, T, F, E, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, F, T, E, E, F, T] [([E, E, F, T, F, T, E, E, F, T], [E, F, E, T, F, T, E, E, F, T]), ([E, T, F, E, F, E, T, E, F, T], [F, T, E, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_101 (And.intro z_30 trivial))

theorem z_103 : le (tf [E, T, F, E, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, F, T, F, E] [([E, E, F, T, E, T, F, T, F, E], [E, F, E, T, E, T, F, T, F, E]), ([E, T, F, E, E, T, F, E, F, T], [E, T, F, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_98 (And.intro z_102 trivial))

theorem z_104 : le (tf [E, T, F, E, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, F, T, E, F] [([E, E, F, T, T, E, F, T, E, F], [E, F, E, T, T, E, F, T, E, F]), ([E, T, F, E, E, T, F, T, E, F], [E, T, F, E, E, T, F, T, F, E]), ([E, T, F, E, T, E, F, E, T, F], [E, T, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_99 (And.intro z_103 (And.intro z_69 trivial)))

theorem z_105 : le (tf [E, T, F, E, T, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, T, E, F, F] [([E, E, F, T, T, E, T, E, F, F], [E, F, E, T, T, E, T, E, F, F]), ([E, T, F, E, E, T, T, E, F, F], [E, T, F, E, E, T, T, F, E, F]), ([E, T, F, E, T, E, E, T, F, F], [E, T, F, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_100 (And.intro z_83 (And.intro z_104 trivial)))

theorem z_106 : le (tf [E, T, T, F, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, F, E, E, T, F] [([E, T, E, F, T, F, E, E, T, F], [E, T, F, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 trivial)

theorem z_107 : le (tf [E, T, T, F, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, F, T, E, F] [([E, T, E, F, T, E, F, T, E, F], [E, T, F, E, T, E, F, T, E, F]), ([E, T, T, F, E, E, F, E, T, F], [E, T, T, F, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 (And.intro z_106 trivial))

theorem z_108 : le (tf [E, T, T, F, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, T, E, F, F] [([E, T, E, F, T, E, T, E, F, F], [E, T, F, E, T, E, T, E, F, F]), ([E, T, T, F, E, E, E, T, F, F], [E, T, T, F, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_107 trivial))

theorem z_109 : le (tf [F, E, T, E, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, T, F, T] [([F, E, E, T, E, E, F, T, F, T], [F, E, E, T, E, F, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_96 trivial)

theorem z_110 : le (tf [T, F, E, E, E, E, F, T, F, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, T, F, T] [([E, F, T, E, E, E, F, T, F, T], [F, E, T, E, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_109 trivial)

theorem z_111 : le (tf [T, E, F, E, E, T, F, E, F, T]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, F, E, F, T] [([E, T, F, E, E, T, F, E, F, T], [E, T, F, E, F, T, E, E, F, T]), ([T, E, F, E, E, E, F, T, F, T], [T, F, E, E, E, E, F, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_102 (And.intro z_110 trivial))

theorem z_112 : le (tf [T, E, E, F, E, T, F, T, F, E]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, F, T, F, E] [([E, T, E, F, E, T, F, T, F, E], [E, T, F, E, E, T, F, T, F, E]), ([T, E, E, F, E, T, F, E, F, T], [T, E, F, E, E, T, F, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_103 (And.intro z_111 trivial))

theorem z_113 : le (tf [T, F, E, E, E, F, E, T, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, T, T, F] [([E, F, T, E, E, F, E, T, T, F], [F, E, T, E, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 trivial)

theorem z_114 : le (tf [T, E, F, E, E, F, T, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, F, T, E, T, F] [([E, T, F, E, E, F, T, E, T, F], [E, T, F, E, F, E, T, E, T, F]), ([T, E, F, E, E, F, E, T, T, F], [T, F, E, E, E, F, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_68 (And.intro z_113 trivial))

theorem z_115 : le (tf [T, E, E, F, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, F, E, E, T, F] [([E, T, E, F, T, F, E, E, T, F], [E, T, F, E, T, F, E, E, T, F]), ([T, E, E, F, E, F, T, E, T, F], [T, E, F, E, E, F, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 (And.intro z_114 trivial))

theorem z_116 : le (tf [T, E, E, F, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, E, F, T, E, F] [([E, T, E, F, T, E, F, T, E, F], [E, T, F, E, T, E, F, T, E, F]), ([T, E, E, F, E, T, F, T, E, F], [T, E, E, F, E, T, F, T, F, E]), ([T, E, E, F, T, E, F, E, T, F], [T, E, E, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 (And.intro z_112 (And.intro z_115 trivial)))

theorem z_117 : le (tf [T, E, T, F, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, E, E, T, F, F] [([E, T, T, F, E, E, E, T, F, F], [E, T, T, F, E, E, F, T, E, F]), ([T, E, E, F, T, E, E, T, F, F], [T, E, E, F, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_116 trivial))

theorem z_118 : le (tf [T, E, T, E, F, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, F, E, T, E, F, F] [([E, T, T, E, F, E, T, E, F, F], [E, T, T, F, E, E, T, E, F, F]), ([T, E, E, T, F, E, T, E, F, F], [T, E, E, T, F, E, T, F, E, F]), ([T, E, T, E, F, E, E, T, F, F], [T, E, T, F, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_108 (And.intro z_91 (And.intro z_117 trivial)))

theorem z_119 : le (tf [T, E, T, E, T, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, T, F, E, E, F, F] [([E, T, T, E, T, F, E, E, F, F], [E, T, T, F, T, E, E, E, F, F]), ([T, E, E, T, T, F, E, E, F, F], [T, E, E, T, T, F, E, F, E, F]), ([T, E, T, E, E, F, T, E, F, F], [T, E, T, E, F, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_55 (And.intro z_92 (And.intro z_118 trivial)))

theorem z_120 : le (tf [T, E, T, T, E, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, E, E, F, E, F, F] [([E, T, T, T, E, E, F, E, F, F], [E, T, T, T, E, F, E, E, F, F]), ([T, E, T, E, T, E, F, E, F, F], [T, E, T, E, T, F, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 (And.intro z_119 trivial))

theorem z_121 : le (tf [F, E, T, E, F, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, T, F, T] [([F, E, E, T, F, E, E, T, F, T], [F, E, F, T, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 trivial)

theorem z_122 : le (tf [F, E, T, E, E, F, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, T, E, F, T] [([F, E, E, T, E, F, T, E, F, T], [F, E, E, T, F, E, T, E, F, T]), ([F, E, T, E, E, F, E, T, F, T], [F, E, T, E, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_121 trivial))

theorem z_123 : le (tf [T, F, E, E, F, E, E, T, F, T]) zero :=
  le_zero_of_pairs [T, F, E, E, F, E, E, T, F, T] [([E, F, T, E, F, E, E, T, F, T], [F, E, T, E, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_121 trivial)

theorem z_124 : le (tf [T, F, E, E, E, F, T, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, T, E, F, T] [([E, F, T, E, E, F, T, E, F, T], [F, E, T, E, E, F, T, E, F, T]), ([T, F, E, E, E, F, E, T, F, T], [T, F, E, E, F, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_122 (And.intro z_123 trivial))

theorem z_125 : le (tf [T, E, F, E, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [T, E, F, E, E, F, T, T, F, E] [([E, T, F, E, E, F, T, T, F, E], [E, T, F, E, F, E, T, T, F, E]), ([T, E, F, E, E, F, T, E, F, T], [T, F, E, E, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_31 (And.intro z_124 trivial))

theorem z_126 : le (tf [T, E, F, E, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [T, E, F, E, T, F, E, E, F, T] [([E, T, F, E, T, F, E, E, F, T], [E, T, F, E, T, F, E, F, E, T]), ([T, E, F, E, E, F, T, E, F, T], [T, F, E, E, E, F, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 (And.intro z_124 trivial))

theorem z_127 : le (tf [T, E, E, F, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [T, E, E, F, T, F, E, T, F, E] [([E, T, E, F, T, F, E, T, F, E], [E, T, F, E, T, F, E, T, F, E]), ([T, E, E, F, E, F, T, T, F, E], [T, E, F, E, E, F, T, T, F, E]), ([T, E, E, F, T, F, E, E, F, T], [T, E, F, E, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 (And.intro z_125 (And.intro z_126 trivial)))

theorem z_128 : le (tf [T, E, E, F, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, F, T, E, E, F] [([E, T, E, F, T, F, T, E, E, F], [E, T, F, E, T, F, T, E, E, F]), ([T, E, E, F, T, F, E, T, E, F], [T, E, E, F, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_127 trivial))

theorem z_129 : le (tf [T, E, E, F, T, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, T, E, F, E, F] [([E, T, E, F, T, T, E, F, E, F], [E, T, F, E, T, T, E, F, E, F]), ([T, E, E, F, T, E, T, F, E, F], [T, E, E, F, T, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_49 (And.intro z_128 trivial))

theorem z_130 : le (tf [T, E, T, F, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, E, F, E, T, F] [([E, T, T, F, E, E, F, E, T, F], [E, T, T, F, E, F, E, E, T, F]), ([T, E, E, F, T, E, F, E, T, F], [T, E, E, F, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_115 trivial))

theorem z_131 : le (tf [T, E, T, F, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, E, T, F, E, F] [([E, T, T, F, E, E, T, F, E, F], [E, T, T, F, E, F, T, E, E, F]), ([T, E, E, F, T, E, T, F, E, F], [T, E, E, F, T, F, T, E, E, F]), ([T, E, T, F, E, E, E, F, T, F], [T, E, T, F, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_53 (And.intro z_128 (And.intro z_130 trivial)))

theorem z_132 : le (tf [T, E, T, F, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, T, E, E, F, F] [([E, T, T, F, E, T, E, E, F, F], [E, T, T, F, E, T, E, F, E, F]), ([T, E, E, F, T, T, E, E, F, F], [T, E, E, F, T, T, E, F, E, F]), ([T, E, T, F, E, E, T, E, F, F], [T, E, T, F, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_54 (And.intro z_129 (And.intro z_131 trivial)))

theorem z_133 : le (tf [T, E, T, F, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, T, F, F, E, E, E, T, F] [([E, T, T, F, F, E, E, E, T, F], [E, T, T, F, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 trivial)

theorem z_134 : le (tf [T, E, T, F, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, F, E, T, E, F] [([E, T, T, F, E, F, E, T, E, F], [E, T, T, F, F, E, E, T, E, F]), ([T, E, E, F, T, F, E, T, E, F], [T, E, E, F, T, F, E, T, F, E]), ([T, E, T, F, E, F, E, E, T, F], [T, E, T, F, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_52 (And.intro z_127 (And.intro z_133 trivial)))

theorem z_135 : le (tf [T, T, E, F, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, T, E, F, E, F, E, E, T, F] [([T, E, T, F, E, F, E, E, T, F], [T, E, T, F, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_133 trivial)

theorem z_136 : le (tf [T, T, E, F, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, T, E, F, E, E, F, T, E, F] [([T, E, T, F, E, E, F, T, E, F], [T, E, T, F, E, F, E, T, E, F]), ([T, T, E, F, E, E, F, E, T, F], [T, T, E, F, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_134 (And.intro z_135 trivial))

theorem z_137 : le (tf [T, T, E, F, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, F, E, E, T, E, F, F] [([T, E, T, F, E, E, T, E, F, F], [T, E, T, F, E, E, T, F, E, F]), ([T, T, E, F, E, E, E, T, F, F], [T, T, E, F, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 (And.intro z_136 trivial))

theorem z_138 : le (tf [T, T, E, E, F, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, F, T, E, E, F, F] [([T, E, T, E, F, T, E, E, F, F], [T, E, T, F, E, T, E, E, F, F]), ([T, T, E, E, F, E, T, E, F, F], [T, T, E, F, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_132 (And.intro z_137 trivial))

theorem z_139 : le (tf [T, T, E, E, T, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, T, E, F, E, F, F] [([T, E, T, E, T, E, F, E, F, F], [T, E, T, E, T, F, E, E, F, F]), ([T, T, E, E, E, T, F, E, F, F], [T, T, E, E, F, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_119 (And.intro z_138 trivial))

theorem z_140 : le (tf [T, T, E, T, E, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, E, E, E, F, F, F] [([T, E, T, T, E, E, E, F, F, F], [T, E, T, T, E, E, F, E, F, F]), ([T, T, E, E, T, E, E, F, F, F], [T, T, E, E, T, E, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_120 (And.intro z_139 trivial))

theorem n_0 : UpperZero (tf [T, T, T, E, E, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, E, E, E, F, F, F] (lfZero_of_mirror_dec [T, T, T, E, E, E, E, F, F, F] (by decide +kernel)) [[T, T, E, T, E, E, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_140 trivial)
    trivial

theorem infinitesimal : Infinitesimal (tf (start 3 4)) := by
  rw [infinitesimal_start_iff, show start 3 4 = [T, T, T, E, E, E, E, F, F, F] from by decide]
  exact n_0

end Cgt.Cert_3_4
