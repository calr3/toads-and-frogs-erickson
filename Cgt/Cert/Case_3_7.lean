import Cgt.Certificate

/-! Machine-generated certificate: `T^3 □^7 F^3` is infinitesimal. -/

namespace Cgt.Cert_3_7
open Cell Game

theorem z_0 : le (tf [F, F, E, E, E, E, E, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1 : le (tf [F, F, E, E, E, E, E, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, F, E, T, T] [([F, F, E, E, E, E, E, E, E, F, T, T, T], [F, F, E, E, E, E, E, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_0 trivial)

theorem z_2 : le (tf [F, F, E, E, E, E, E, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, T, F, E, T] [([F, F, E, E, E, E, E, E, T, E, F, T, T], [F, F, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_3 : le (tf [F, E, F, E, E, E, E, E, T, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, T, F, T, E] [([F, E, F, E, E, E, E, E, T, T, F, E, T], [F, F, E, E, E, E, E, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 trivial)

theorem z_4 : le (tf [F, E, F, E, E, E, E, E, T, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, T, T, E, F] [([F, E, F, E, E, E, E, E, T, T, E, T, F], [F, E, F, E, E, E, E, E, T, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 trivial)

theorem z_5 : le (tf [F, F, E, E, E, E, E, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, F, T, T] [([F, F, E, E, E, E, E, E, T, E, F, T, T], [F, F, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_6 : le (tf [F, E, F, E, E, E, E, T, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, T, F, E, T] [([F, E, F, E, E, E, E, E, T, T, F, E, T], [F, F, E, E, E, E, E, E, T, T, F, E, T]), ([F, E, F, E, E, E, E, T, E, E, F, T, T], [F, F, E, E, E, E, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 (And.intro z_5 trivial))

theorem z_7 : le (tf [F, E, E, F, E, E, E, T, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, T, F, T, E] [([F, E, E, F, E, E, E, E, T, T, F, T, E], [F, E, F, E, E, E, E, E, T, T, F, T, E]), ([F, E, E, F, E, E, E, T, E, T, F, E, T], [F, E, F, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 (And.intro z_6 trivial))

theorem z_8 : le (tf [F, E, E, F, E, E, E, T, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, T, T, E, F] [([F, E, E, F, E, E, E, E, T, T, T, E, F], [F, E, F, E, E, E, E, E, T, T, T, E, F]), ([F, E, E, F, E, E, E, T, E, T, E, T, F], [F, E, E, F, E, E, E, T, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_4 (And.intro z_7 trivial))

theorem z_9 : le (tf [F, E, E, F, E, E, E, T, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, T, E, E, T, F] [([F, E, E, F, E, E, E, T, E, T, E, T, F], [F, E, E, F, E, E, E, T, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_7 trivial)

theorem z_10 : le (tf [F, E, E, E, F, E, E, T, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, E, T, E, F] [([F, E, E, E, F, E, E, T, E, T, T, E, F], [F, E, E, F, E, E, E, T, E, T, T, E, F]), ([F, E, E, E, F, E, E, T, T, E, E, T, F], [F, E, E, F, E, E, E, T, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_8 (And.intro z_9 trivial))

theorem z_11 : le (tf [F, E, E, E, E, F, E, T, T, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, T, E, E, F] [([F, E, E, E, E, F, E, T, T, E, T, E, F], [F, E, E, E, F, E, E, T, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_10 trivial)

theorem z_12 : le (tf [F, F, E, E, E, E, E, E, T, T, T, F, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, T, T, F, E] [([F, F, E, E, E, E, E, E, T, T, E, F, T], [F, F, E, E, E, E, E, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 trivial)

theorem z_13 : le (tf [F, E, F, E, E, E, E, T, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, T, T, F, E] [([F, E, F, E, E, E, E, E, T, T, T, F, E], [F, F, E, E, E, E, E, E, T, T, T, F, E]), ([F, E, F, E, E, E, E, T, E, T, E, F, T], [F, E, F, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 (And.intro z_6 trivial))

theorem z_14 : le (tf [F, F, E, E, F, E, E, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, E, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_15 : le (tf [F, F, E, E, E, F, E, E, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, E, E, T, E, T, T] [([F, F, E, E, E, F, E, E, E, E, T, T, T], [F, F, E, E, F, E, E, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_14 trivial)

theorem z_16 : le (tf [F, F, E, E, E, E, F, E, E, T, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, T, T, E, T] [([F, F, E, E, E, E, F, E, E, T, E, T, T], [F, F, E, E, E, F, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_15 trivial)

theorem z_17 : le (tf [F, F, E, E, E, E, E, F, E, T, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, T, T, T, E] [([F, F, E, E, E, E, E, F, E, T, T, E, T], [F, F, E, E, E, E, F, E, E, T, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_16 trivial)

theorem z_18 : le (tf [F, F, F, E, E, E, E, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, E, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_19 : le (tf [F, F, E, F, E, E, E, E, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, E, E, E, E, T, E, T, T] [([F, F, E, F, E, E, E, E, E, E, T, T, T], [F, F, F, E, E, E, E, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_18 trivial)

theorem z_20 : le (tf [F, F, E, E, F, E, E, E, E, T, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, E, E, E, T, T, E, T] [([F, F, E, E, F, E, E, E, E, T, E, T, T], [F, F, E, F, E, E, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_19 trivial)

theorem z_21 : le (tf [F, F, E, E, F, E, E, E, T, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, E, E, T, E, E, T, T] [([F, F, E, E, F, E, E, E, E, T, E, T, T], [F, F, E, F, E, E, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_19 trivial)

theorem z_22 : le (tf [F, F, E, E, E, F, E, E, T, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, E, T, E, T, E, T] [([F, F, E, E, E, F, E, E, E, T, T, E, T], [F, F, E, E, F, E, E, E, E, T, T, E, T]), ([F, F, E, E, E, F, E, E, T, E, E, T, T], [F, F, E, E, F, E, E, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_20 (And.intro z_21 trivial))

theorem z_23 : le (tf [F, F, E, E, E, F, E, T, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, T, E, E, E, T, T] [([F, F, E, E, E, F, E, E, T, E, E, T, T], [F, F, E, E, F, E, E, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_21 trivial)

theorem z_24 : le (tf [F, F, E, E, E, E, F, T, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, T, E, E, T, E, T] [([F, F, E, E, E, E, F, E, T, E, T, E, T], [F, F, E, E, E, F, E, E, T, E, T, E, T]), ([F, F, E, E, E, E, F, T, E, E, E, T, T], [F, F, E, E, E, F, E, T, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 (And.intro z_23 trivial))

theorem z_25 : le (tf [F, F, E, E, E, E, E, T, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, F, E, T, T, E] [([F, F, E, E, E, E, E, E, F, T, T, T, E], [F, F, E, E, E, E, E, F, E, T, T, T, E]), ([F, F, E, E, E, E, E, T, F, E, T, E, T], [F, F, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_17 (And.intro z_24 trivial))

theorem z_26 : le (tf [F, F, E, E, E, E, E, T, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, F, T, E, E, T] [([F, F, E, E, E, E, E, T, F, E, T, E, T], [F, F, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 trivial)

theorem z_27 : le (tf [F, E, F, E, E, E, E, T, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, F, T, E, T, E] [([F, E, F, E, E, E, E, T, F, E, T, T, E], [F, F, E, E, E, E, E, T, F, E, T, T, E]), ([F, E, F, E, E, E, E, T, F, T, E, E, T], [F, F, E, E, E, E, E, T, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 (And.intro z_26 trivial))

theorem z_28 : le (tf [F, F, E, E, E, E, E, T, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, T, E, F, E, T] [([F, F, E, E, E, E, E, T, E, T, F, E, T], [F, F, E, E, E, E, E, T, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_26 trivial)

theorem z_29 : le (tf [F, E, F, E, E, E, E, T, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, T, E, F, T, E] [([F, E, F, E, E, E, E, T, E, T, F, T, E], [F, E, F, E, E, E, E, T, F, T, E, T, E]), ([F, E, F, E, E, E, E, T, T, E, F, E, T], [F, F, E, E, E, E, E, T, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_27 (And.intro z_28 trivial))

theorem z_30 : le (tf [F, E, F, E, E, E, E, T, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, T, E, T, E, F] [([F, E, F, E, E, E, E, T, E, T, T, E, F], [F, E, F, E, E, E, E, T, E, T, T, F, E]), ([F, E, F, E, E, E, E, T, T, E, E, T, F], [F, E, F, E, E, E, E, T, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_29 trivial))

theorem z_31 : le (tf [F, F, E, E, E, E, F, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_32 : le (tf [F, F, E, E, E, E, E, F, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, T, E, T, T] [([F, F, E, E, E, E, E, F, E, E, T, T, T], [F, F, E, E, E, E, F, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_31 trivial)

theorem z_33 : le (tf [F, F, E, E, E, E, E, T, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, F, E, E, T, T] [([F, F, E, E, E, E, E, E, F, T, E, T, T], [F, F, E, E, E, E, E, F, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 trivial)

theorem z_34 : le (tf [F, F, E, E, E, E, T, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, F, E, T, T] [([F, F, E, E, E, E, E, T, E, F, E, T, T], [F, F, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_33 trivial)

theorem z_35 : le (tf [F, F, E, E, E, E, T, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, T, F, E, T] [([F, F, E, E, E, E, E, T, E, T, F, E, T], [F, F, E, E, E, E, E, T, F, T, E, E, T]), ([F, F, E, E, E, E, T, E, E, E, F, T, T], [F, F, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_26 (And.intro z_34 trivial))

theorem z_36 : le (tf [F, E, F, E, E, E, T, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, T, F, T, E] [([F, E, F, E, E, E, E, T, E, T, F, T, E], [F, E, F, E, E, E, E, T, F, T, E, T, E]), ([F, E, F, E, E, E, T, E, E, T, F, E, T], [F, F, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_27 (And.intro z_35 trivial))

theorem z_37 : le (tf [F, E, F, E, E, E, T, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, T, T, E, F] [([F, E, F, E, E, E, E, T, E, T, T, E, F], [F, E, F, E, E, E, E, T, E, T, T, F, E]), ([F, E, F, E, E, E, T, E, E, T, E, T, F], [F, E, F, E, E, E, T, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_36 trivial))

theorem z_38 : le (tf [F, E, F, E, E, E, T, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, T, E, E, T, F] [([F, E, F, E, E, E, E, T, T, E, E, T, F], [F, E, F, E, E, E, E, T, T, E, F, T, E]), ([F, E, F, E, E, E, T, E, E, T, E, T, F], [F, E, F, E, E, E, T, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_29 (And.intro z_36 trivial))

theorem z_39 : le (tf [F, E, E, F, E, E, T, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, T, E, T, E, F] [([F, E, E, F, E, E, E, T, T, E, T, E, F], [F, E, F, E, E, E, E, T, T, E, T, E, F]), ([F, E, E, F, E, E, T, E, E, T, T, E, F], [F, E, F, E, E, E, T, E, E, T, T, E, F]), ([F, E, E, F, E, E, T, E, T, E, E, T, F], [F, E, F, E, E, E, T, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_30 (And.intro z_37 (And.intro z_38 trivial)))

theorem z_40 : le (tf [F, F, E, E, E, T, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, E, E, E, E, F, T, T] [([F, F, E, E, E, E, T, E, E, E, F, T, T], [F, F, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_34 trivial)

theorem z_41 : le (tf [F, E, F, E, E, T, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, T, F, E, T] [([F, E, F, E, E, E, T, E, E, T, F, E, T], [F, F, E, E, E, E, T, E, E, T, F, E, T]), ([F, E, F, E, E, T, E, E, E, E, F, T, T], [F, F, E, E, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_35 (And.intro z_40 trivial))

theorem z_42 : le (tf [F, E, E, F, E, T, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, T, F, T, E] [([F, E, E, F, E, E, T, E, E, T, F, T, E], [F, E, F, E, E, E, T, E, E, T, F, T, E]), ([F, E, E, F, E, T, E, E, E, T, F, E, T], [F, E, F, E, E, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_36 (And.intro z_41 trivial))

theorem z_43 : le (tf [F, E, E, F, E, T, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, T, T, E, F] [([F, E, E, F, E, E, T, E, E, T, T, E, F], [F, E, F, E, E, E, T, E, E, T, T, E, F]), ([F, E, E, F, E, T, E, E, E, T, E, T, F], [F, E, E, F, E, T, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_37 (And.intro z_42 trivial))

theorem z_44 : le (tf [F, E, E, F, E, T, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, T, E, E, T, F] [([F, E, E, F, E, E, T, E, T, E, E, T, F], [F, E, F, E, E, E, T, E, T, E, E, T, F]), ([F, E, E, F, E, T, E, E, E, T, E, T, F], [F, E, E, F, E, T, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_38 (And.intro z_42 trivial))

theorem z_45 : le (tf [F, E, E, E, F, T, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, T, E, T, E, F] [([F, E, E, E, F, E, T, E, T, E, T, E, F], [F, E, E, F, E, E, T, E, T, E, T, E, F]), ([F, E, E, E, F, T, E, E, E, T, T, E, F], [F, E, E, F, E, T, E, E, E, T, T, E, F]), ([F, E, E, E, F, T, E, E, T, E, E, T, F], [F, E, E, F, E, T, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_39 (And.intro z_43 (And.intro z_44 trivial)))

theorem z_46 : le (tf [F, E, E, E, E, T, F, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, T, E, E, F] [([F, E, E, E, E, E, F, T, T, T, E, E, F], [F, E, E, E, E, F, E, T, T, T, E, E, F]), ([F, E, E, E, E, T, F, E, T, E, T, E, F], [F, E, E, E, F, T, E, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 (And.intro z_45 trivial))

theorem z_47 : le (tf [F, E, F, E, E, E, E, E, T, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, F, T, E, T] [([F, E, F, E, E, E, E, E, T, F, E, T, T], [F, F, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_48 : le (tf [F, E, F, E, E, E, E, E, T, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, T, E, F, T] [([F, E, F, E, E, E, E, E, T, E, T, F, T], [F, E, F, E, E, E, E, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 trivial)

theorem z_49 : le (tf [F, E, E, F, E, E, E, E, T, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, T, F, E] [([F, E, E, F, E, E, E, E, T, T, E, F, T], [F, E, F, E, E, E, E, E, T, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 trivial)

theorem z_50 : le (tf [F, E, F, E, E, E, E, T, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, T, F, T] [([F, E, F, E, E, E, E, E, T, E, T, F, T], [F, E, F, E, E, E, E, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 trivial)

theorem z_51 : le (tf [F, E, E, F, E, E, E, T, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, T, E, F, T] [([F, E, E, F, E, E, E, E, T, T, E, F, T], [F, E, F, E, E, E, E, E, T, T, E, F, T]), ([F, E, E, F, E, E, E, T, E, E, T, F, T], [F, E, F, E, E, E, E, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_50 trivial))

theorem z_52 : le (tf [F, E, E, E, F, E, E, T, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, T, F, E] [([F, E, E, E, F, E, E, E, T, T, T, F, E], [F, E, E, F, E, E, E, E, T, T, T, F, E]), ([F, E, E, E, F, E, E, T, E, T, E, F, T], [F, E, E, F, E, E, E, T, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_49 (And.intro z_51 trivial))

theorem z_53 : le (tf [F, E, E, E, F, E, E, T, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, E, E, F, T] [([F, E, E, E, F, E, E, T, E, T, E, F, T], [F, E, E, F, E, E, E, T, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 trivial)

theorem z_54 : le (tf [F, E, E, E, E, F, E, T, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, T, F, E] [([F, E, E, E, E, F, E, T, E, T, T, F, E], [F, E, E, E, F, E, E, T, E, T, T, F, E]), ([F, E, E, E, E, F, E, T, T, E, E, F, T], [F, E, E, E, F, E, E, T, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_52 (And.intro z_53 trivial))

theorem z_55 : le (tf [F, F, E, E, E, E, F, E, T, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, T, E, E, T, T] [([F, F, E, E, E, E, F, E, E, T, E, T, T], [F, F, E, E, E, F, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_15 trivial)

theorem z_56 : le (tf [F, F, E, E, E, E, E, F, T, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, T, E, T, E, T] [([F, F, E, E, E, E, E, F, E, T, T, E, T], [F, F, E, E, E, E, F, E, E, T, T, E, T]), ([F, F, E, E, E, E, E, F, T, E, E, T, T], [F, F, E, E, E, E, F, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_16 (And.intro z_55 trivial))

theorem z_57 : le (tf [F, F, E, E, E, E, E, T, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, F, T, E, T] [([F, F, E, E, E, E, E, E, T, F, T, E, T], [F, F, E, E, E, E, E, F, T, E, T, E, T]), ([F, F, E, E, E, E, E, T, E, F, E, T, T], [F, F, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 (And.intro z_33 trivial))

theorem z_58 : le (tf [F, F, E, E, E, E, T, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, E, T, F, T] [([F, F, E, E, E, E, E, T, E, E, T, F, T], [F, F, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_57 trivial)

theorem z_59 : le (tf [F, E, F, E, E, E, T, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, T, E, F, T] [([F, E, F, E, E, E, E, T, E, T, E, F, T], [F, E, F, E, E, E, E, T, E, T, F, E, T]), ([F, E, F, E, E, E, T, E, E, E, T, F, T], [F, F, E, E, E, E, T, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_6 (And.intro z_58 trivial))

theorem z_60 : le (tf [F, E, E, F, E, E, T, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, T, T, F, E] [([F, E, E, F, E, E, E, T, E, T, T, F, E], [F, E, F, E, E, E, E, T, E, T, T, F, E]), ([F, E, E, F, E, E, T, E, E, T, E, F, T], [F, E, F, E, E, E, T, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_59 trivial))

theorem z_61 : le (tf [F, E, F, E, E, T, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, E, T, F, T] [([F, E, F, E, E, E, T, E, E, E, T, F, T], [F, F, E, E, E, E, T, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_58 trivial)

theorem z_62 : le (tf [F, E, E, F, E, T, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, T, E, F, T] [([F, E, E, F, E, E, T, E, E, T, E, F, T], [F, E, F, E, E, E, T, E, E, T, E, F, T]), ([F, E, E, F, E, T, E, E, E, E, T, F, T], [F, E, F, E, E, T, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_59 (And.intro z_61 trivial))

theorem z_63 : le (tf [F, E, E, E, F, T, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, T, T, F, E] [([F, E, E, E, F, E, T, E, E, T, T, F, E], [F, E, E, F, E, E, T, E, E, T, T, F, E]), ([F, E, E, E, F, T, E, E, E, T, E, F, T], [F, E, E, F, E, T, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_60 (And.intro z_62 trivial))

theorem z_64 : le (tf [F, E, F, E, E, E, E, T, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, T, E, E, F, T] [([F, E, F, E, E, E, E, T, E, T, E, F, T], [F, E, F, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_6 trivial)

theorem z_65 : le (tf [F, E, E, F, E, E, T, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, T, E, E, F, T] [([F, E, E, F, E, E, E, T, T, E, E, F, T], [F, E, F, E, E, E, E, T, T, E, E, F, T]), ([F, E, E, F, E, E, T, E, E, T, E, F, T], [F, E, F, E, E, E, T, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_64 (And.intro z_59 trivial))

theorem z_66 : le (tf [F, E, E, E, F, T, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, T, E, E, F, T] [([F, E, E, E, F, E, T, E, T, E, E, F, T], [F, E, E, F, E, E, T, E, T, E, E, F, T]), ([F, E, E, E, F, T, E, E, E, T, E, F, T], [F, E, E, F, E, T, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_65 (And.intro z_62 trivial))

theorem z_67 : le (tf [F, E, E, E, E, T, F, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, T, F, E] [([F, E, E, E, E, E, F, T, T, E, T, F, E], [F, E, E, E, E, F, E, T, T, E, T, F, E]), ([F, E, E, E, E, T, F, E, E, T, T, F, E], [F, E, E, E, F, T, E, E, E, T, T, F, E]), ([F, E, E, E, E, T, F, E, T, E, E, F, T], [F, E, E, E, F, T, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_54 (And.intro z_63 (And.intro z_66 trivial)))

theorem z_68 : le (tf [F, F, E, E, E, E, E, E, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_69 : le (tf [F, E, F, E, E, E, E, E, T, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, F, T, T] [([F, E, F, E, E, E, E, E, E, T, F, T, T], [F, F, E, E, E, E, E, E, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_68 trivial)

theorem z_70 : le (tf [F, E, E, F, E, E, E, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, F, E, T] [([F, E, E, F, E, E, E, E, T, E, F, T, T], [F, E, F, E, E, E, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 trivial)

theorem z_71 : le (tf [F, E, E, F, E, E, E, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, F, T, T] [([F, E, E, F, E, E, E, E, T, E, F, T, T], [F, E, F, E, E, E, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 trivial)

theorem z_72 : le (tf [F, E, E, E, F, E, E, T, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, F, E, T] [([F, E, E, E, F, E, E, E, T, T, F, E, T], [F, E, E, F, E, E, E, E, T, T, F, E, T]), ([F, E, E, E, F, E, E, T, E, E, F, T, T], [F, E, E, F, E, E, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 (And.intro z_71 trivial))

theorem z_73 : le (tf [F, E, E, E, E, F, E, T, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, F, E, T] [([F, E, E, E, E, F, E, T, E, T, F, E, T], [F, E, E, E, F, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_72 trivial)

theorem z_74 : le (tf [F, E, F, E, E, E, T, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, F, T, T] [([F, E, F, E, E, E, E, T, E, E, F, T, T], [F, F, E, E, E, E, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_5 trivial)

theorem z_75 : le (tf [F, E, E, F, E, E, T, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, T, F, E, T] [([F, E, E, F, E, E, E, T, E, T, F, E, T], [F, E, F, E, E, E, E, T, E, T, F, E, T]), ([F, E, E, F, E, E, T, E, E, E, F, T, T], [F, E, F, E, E, E, T, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_6 (And.intro z_74 trivial))

theorem z_76 : le (tf [F, E, E, F, E, T, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, F, T, T] [([F, E, E, F, E, E, T, E, E, E, F, T, T], [F, E, F, E, E, E, T, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_74 trivial)

theorem z_77 : le (tf [F, E, E, E, F, T, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, T, F, E, T] [([F, E, E, E, F, E, T, E, E, T, F, E, T], [F, E, E, F, E, E, T, E, E, T, F, E, T]), ([F, E, E, E, F, T, E, E, E, E, F, T, T], [F, E, E, F, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_75 (And.intro z_76 trivial))

theorem z_78 : le (tf [F, E, E, E, E, T, F, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, F, E, T] [([F, E, E, E, E, E, F, T, T, E, F, E, T], [F, E, E, E, E, F, E, T, T, E, F, E, T]), ([F, E, E, E, E, T, F, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 (And.intro z_77 trivial))

theorem z_79 : le (tf [F, E, E, E, E, T, T, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, F, E, T] [([F, E, E, E, E, T, E, F, T, E, F, E, T], [F, E, E, E, E, T, F, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_78 trivial)

theorem z_80 : le (tf [F, E, E, E, E, T, T, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, T, F, E] [([F, E, E, E, E, T, E, F, T, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, T, F, E]), ([F, E, E, E, E, T, T, F, E, E, E, F, T], [F, E, E, E, E, T, T, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 (And.intro z_79 trivial))

theorem z_81 : le (tf [F, E, E, E, E, T, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, T, E, E, F] [([F, E, E, E, E, T, E, F, T, T, E, E, F], [F, E, E, E, E, T, F, E, T, T, E, E, F]), ([F, E, E, E, E, T, T, F, E, E, T, E, F], [F, E, E, E, E, T, T, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 (And.intro z_80 trivial))

theorem z_82 : le (tf [E, F, E, E, E, T, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, T, E, E, E, F] [([E, F, E, E, E, T, T, F, E, T, E, E, F], [F, E, E, E, E, T, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 trivial)

theorem z_83 : le (tf [E, F, E, E, E, T, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, T, E, F, E, E, F] [([E, F, E, E, E, T, T, E, T, F, E, E, F], [E, F, E, E, E, T, T, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 trivial)

theorem z_84 : le (tf [F, E, E, E, E, E, T, T, T, F, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, T, F, F, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_85 : le (tf [E, F, E, E, E, T, E, T, T, F, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, T, F, F, E, E] [([E, F, E, E, E, E, T, T, T, F, F, E, E], [F, E, E, E, E, E, T, T, T, F, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 trivial)

theorem z_86 : le (tf [F, E, E, E, E, T, F, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, T, E, E, E, F, T] [([F, E, E, E, E, T, F, E, T, E, E, F, T], [F, E, E, E, F, T, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 trivial)

theorem z_87 : le (tf [E, F, E, E, E, T, F, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, E, E, T, F, E] [([E, F, E, E, E, T, F, E, T, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, T, F, E]), ([E, F, E, E, E, T, F, T, E, E, E, F, T], [F, E, E, E, E, T, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 (And.intro z_86 trivial))

theorem z_88 : le (tf [F, E, E, F, E, E, T, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, T, F, T] [([F, E, E, F, E, E, E, T, E, E, T, F, T], [F, E, F, E, E, E, E, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_50 trivial)

theorem z_89 : le (tf [F, E, E, E, F, E, T, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, T, E, F, T] [([F, E, E, E, F, E, E, T, E, T, E, F, T], [F, E, E, F, E, E, E, T, E, T, E, F, T]), ([F, E, E, E, F, E, T, E, E, E, T, F, T], [F, E, E, F, E, E, T, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 (And.intro z_88 trivial))

theorem z_90 : le (tf [F, E, E, E, E, F, T, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, T, F, E] [([F, E, E, E, E, F, E, T, E, T, T, F, E], [F, E, E, E, F, E, E, T, E, T, T, F, E]), ([F, E, E, E, E, F, T, E, E, T, E, F, T], [F, E, E, E, F, E, T, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_52 (And.intro z_89 trivial))

theorem z_91 : le (tf [F, E, F, E, E, E, E, E, E, T, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, T, F, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_92 : le (tf [F, E, E, F, E, E, E, E, T, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, T, F, T] [([F, E, E, F, E, E, E, E, E, T, T, F, T], [F, E, F, E, E, E, E, E, E, T, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_91 trivial)

theorem z_93 : le (tf [F, E, E, E, F, E, E, E, T, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, E, F, T] [([F, E, E, E, F, E, E, E, T, E, T, F, T], [F, E, E, F, E, E, E, E, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 trivial)

theorem z_94 : le (tf [F, E, E, E, F, E, E, T, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, T, F, T] [([F, E, E, E, F, E, E, E, T, E, T, F, T], [F, E, E, F, E, E, E, E, T, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 trivial)

theorem z_95 : le (tf [F, E, E, E, E, F, E, T, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, E, F, T] [([F, E, E, E, E, F, E, E, T, T, E, F, T], [F, E, E, E, F, E, E, E, T, T, E, F, T]), ([F, E, E, E, E, F, E, T, E, E, T, F, T], [F, E, E, E, F, E, E, T, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 (And.intro z_94 trivial))

theorem z_96 : le (tf [F, E, E, E, F, T, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, T, F, T] [([F, E, E, E, F, E, T, E, E, E, T, F, T], [F, E, E, F, E, E, T, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 trivial)

theorem z_97 : le (tf [F, E, E, E, E, T, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, E, F, T] [([F, E, E, E, E, E, F, T, E, T, E, F, T], [F, E, E, E, E, F, E, T, E, T, E, F, T]), ([F, E, E, E, E, T, F, E, E, E, T, F, T], [F, E, E, E, F, T, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_95 (And.intro z_96 trivial))

theorem z_98 : le (tf [F, E, E, E, E, T, E, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, T, F, E] [([F, E, E, E, E, E, T, F, E, T, T, F, E], [F, E, E, E, E, F, T, E, E, T, T, F, E]), ([F, E, E, E, E, T, E, F, E, T, E, F, T], [F, E, E, E, E, T, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_90 (And.intro z_97 trivial))

theorem z_99 : le (tf [F, E, E, E, T, E, F, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, T, F, T] [([F, E, E, E, E, T, F, E, E, E, T, F, T], [F, E, E, E, F, T, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_96 trivial)

theorem z_100 : le (tf [F, E, E, E, T, E, E, F, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, E, F, T] [([F, E, E, E, E, T, E, F, E, T, E, F, T], [F, E, E, E, E, T, F, E, E, T, E, F, T]), ([F, E, E, E, T, E, E, F, E, E, T, F, T], [F, E, E, E, T, E, F, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_97 (And.intro z_99 trivial))

theorem z_101 : le (tf [F, E, E, E, T, E, E, E, F, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, T, T, F, E] [([F, E, E, E, E, T, E, E, F, T, T, F, E], [F, E, E, E, E, T, E, F, E, T, T, F, E]), ([F, E, E, E, T, E, E, E, F, T, E, F, T], [F, E, E, E, T, E, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_98 (And.intro z_100 trivial))

theorem z_102 : le (tf [F, E, E, E, T, E, E, T, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, F, E, E, F, T] [([F, E, E, E, E, T, E, T, F, E, E, F, T], [F, E, E, E, E, T, F, T, E, E, E, F, T]), ([F, E, E, E, T, E, E, E, F, T, E, F, T], [F, E, E, E, T, E, E, F, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_86 (And.intro z_100 trivial))

theorem z_103 : le (tf [E, F, E, E, T, E, E, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, F, E, T, F, E] [([E, F, E, E, E, T, E, T, F, E, T, F, E], [E, F, E, E, E, T, F, T, E, E, T, F, E]), ([E, F, E, E, T, E, E, E, F, T, T, F, E], [F, E, E, E, T, E, E, E, F, T, T, F, E]), ([E, F, E, E, T, E, E, T, F, E, E, F, T], [F, E, E, E, T, E, E, T, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_87 (And.intro z_101 (And.intro z_102 trivial)))

theorem z_104 : le (tf [E, F, E, E, T, E, E, T, T, F, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, T, F, E, F, E] [([E, F, E, E, E, T, E, T, T, F, E, F, E], [E, F, E, E, E, T, E, T, T, F, F, E, E]), ([E, F, E, E, T, E, E, T, E, F, T, F, E], [E, F, E, E, T, E, E, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_85 (And.intro z_103 trivial))

theorem z_105 : le (tf [F, E, E, F, E, E, T, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, T, E, E, E, T, F] [([F, E, E, F, E, E, T, E, T, E, E, T, F], [F, E, F, E, E, E, T, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_38 trivial)

theorem z_106 : le (tf [F, E, E, E, F, T, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, T, E, E, E, T, F] [([F, E, E, E, F, E, T, T, E, E, E, T, F], [F, E, E, F, E, E, T, T, E, E, E, T, F]), ([F, E, E, E, F, T, E, E, T, E, E, T, F], [F, E, E, F, E, T, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_44 trivial))

theorem z_107 : le (tf [F, E, E, E, E, T, F, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, T, E, E, T, E, F] [([F, E, E, E, E, T, F, E, T, E, T, E, F], [F, E, E, E, F, T, E, E, T, E, T, E, F]), ([F, E, E, E, E, T, F, T, E, E, E, T, F], [F, E, E, E, F, T, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_45 (And.intro z_106 trivial))

theorem z_108 : le (tf [F, F, E, E, E, E, E, E, E, T, T, T, F]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_109 : le (tf [F, E, F, E, E, E, E, E, T, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, T, T, F] [([F, E, F, E, E, E, E, E, E, T, T, T, F], [F, F, E, E, E, E, E, E, E, T, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_108 trivial)

theorem z_110 : le (tf [F, E, E, F, E, E, E, E, T, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, E, T, F] [([F, E, E, F, E, E, E, E, T, E, T, T, F], [F, E, F, E, E, E, E, E, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_109 trivial)

theorem z_111 : le (tf [F, E, E, F, E, E, E, T, E, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, T, T, F] [([F, E, E, F, E, E, E, E, T, E, T, T, F], [F, E, F, E, E, E, E, E, T, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_109 trivial)

theorem z_112 : le (tf [F, E, E, E, F, E, E, T, E, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, E, T, F] [([F, E, E, E, F, E, E, E, T, T, E, T, F], [F, E, E, F, E, E, E, E, T, T, E, T, F]), ([F, E, E, E, F, E, E, T, E, E, T, T, F], [F, E, E, F, E, E, E, T, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_110 (And.intro z_111 trivial))

theorem z_113 : le (tf [F, E, E, E, E, F, E, T, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, E, T, F] [([F, E, E, E, E, F, E, T, E, T, E, T, F], [F, E, E, E, F, E, E, T, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_112 trivial)

theorem z_114 : le (tf [F, E, E, E, F, E, E, E, T, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, F, T, E] [([F, E, E, E, F, E, E, E, T, T, F, E, T], [F, E, E, F, E, E, E, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 trivial)

theorem z_115 : le (tf [F, E, E, E, E, F, E, T, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, F, T, E] [([F, E, E, E, E, F, E, E, T, T, F, T, E], [F, E, E, E, F, E, E, E, T, T, F, T, E]), ([F, E, E, E, E, F, E, T, E, T, F, E, T], [F, E, E, E, F, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_114 (And.intro z_72 trivial))

theorem z_116 : le (tf [F, E, E, E, E, T, F, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, F, T, E] [([F, E, E, E, E, E, F, T, E, T, F, T, E], [F, E, E, E, E, F, E, T, E, T, F, T, E]), ([F, E, E, E, E, T, F, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_115 (And.intro z_77 trivial))

theorem z_117 : le (tf [F, E, E, E, E, T, F, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, E, T, F] [([F, E, E, E, E, E, F, T, T, E, E, T, F], [F, E, E, E, E, F, E, T, T, E, E, T, F]), ([F, E, E, E, E, T, F, E, E, T, E, T, F], [F, E, E, E, E, T, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_113 (And.intro z_116 trivial))

theorem z_118 : le (tf [F, E, E, E, E, T, T, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, E, T, F] [([F, E, E, E, E, T, E, F, T, E, E, T, F], [F, E, E, E, E, T, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 trivial)

theorem z_119 : le (tf [F, E, E, E, E, T, T, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, E, F, E, T, E, F] [([F, E, E, E, E, T, E, T, F, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, T, E, F]), ([F, E, E, E, E, T, T, E, F, E, E, T, F], [F, E, E, E, E, T, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_118 trivial))

theorem z_120 : le (tf [F, E, E, E, F, E, T, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, T, F, T, E] [([F, E, E, E, F, E, E, T, E, T, F, T, E], [F, E, E, F, E, E, E, T, E, T, F, T, E]), ([F, E, E, E, F, E, T, E, E, T, F, E, T], [F, E, E, F, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_7 (And.intro z_75 trivial))

theorem z_121 : le (tf [F, E, E, E, F, E, T, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, T, E, E, T, F] [([F, E, E, E, F, E, E, T, T, E, E, T, F], [F, E, E, F, E, E, E, T, T, E, E, T, F]), ([F, E, E, E, F, E, T, E, E, T, E, T, F], [F, E, E, E, F, E, T, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_9 (And.intro z_120 trivial))

theorem z_122 : le (tf [F, E, F, E, T, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, E, E, F, T, T] [([F, E, F, E, E, T, E, E, E, E, F, T, T], [F, F, E, E, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_40 trivial)

theorem z_123 : le (tf [F, E, E, F, T, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, T, F, E, T] [([F, E, E, F, E, T, E, E, E, T, F, E, T], [F, E, F, E, E, T, E, E, E, T, F, E, T]), ([F, E, E, F, T, E, E, E, E, E, F, T, T], [F, E, F, E, T, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_41 (And.intro z_122 trivial))

theorem z_124 : le (tf [F, E, E, E, T, F, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, T, F, T, E] [([F, E, E, E, E, F, T, E, E, T, F, T, E], [F, E, E, E, F, E, T, E, E, T, F, T, E]), ([F, E, E, E, T, F, E, E, E, T, F, E, T], [F, E, E, F, T, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_120 (And.intro z_123 trivial))

theorem z_125 : le (tf [F, E, E, E, T, F, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, T, E, E, T, F] [([F, E, E, E, E, F, T, E, T, E, E, T, F], [F, E, E, E, F, E, T, E, T, E, E, T, F]), ([F, E, E, E, T, F, E, E, E, T, E, T, F], [F, E, E, E, T, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_121 (And.intro z_124 trivial))

theorem z_126 : le (tf [F, E, E, E, T, E, F, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, T, E, E, E, T, F] [([F, E, E, E, E, T, F, T, E, E, E, T, F], [F, E, E, E, F, T, E, T, E, E, E, T, F]), ([F, E, E, E, T, E, F, E, T, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_125 trivial))

theorem z_127 : le (tf [F, E, E, E, T, E, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, F, E, T, E, F] [([F, E, E, E, E, T, E, T, F, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, T, E, F]), ([F, E, E, E, T, E, E, E, F, T, T, E, F], [F, E, E, E, T, E, E, E, F, T, T, F, E]), ([F, E, E, E, T, E, E, T, F, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_101 (And.intro z_126 trivial)))

theorem z_128 : le (tf [F, E, E, E, T, E, T, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, F, E, E, T, F] [([F, E, E, E, E, T, T, E, F, E, E, T, F], [F, E, E, E, E, T, T, F, E, E, E, T, F]), ([F, E, E, E, T, E, E, T, F, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_118 (And.intro z_126 trivial))

theorem z_129 : le (tf [F, E, E, E, T, E, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, E, F, T, E, F] [([F, E, E, E, E, T, T, E, E, F, T, E, F], [F, E, E, E, E, T, T, E, F, E, T, E, F]), ([F, E, E, E, T, E, E, T, E, F, T, E, F], [F, E, E, E, T, E, E, T, F, E, T, E, F]), ([F, E, E, E, T, E, T, E, E, F, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_119 (And.intro z_127 (And.intro z_128 trivial)))

theorem z_130 : le (tf [E, F, E, E, T, E, T, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, T, F, E, E, F] [([E, F, E, E, E, T, T, E, T, F, E, E, F], [E, F, E, E, E, T, T, F, T, E, E, E, F]), ([E, F, E, E, T, E, E, T, T, F, E, E, F], [E, F, E, E, T, E, E, T, T, F, E, F, E]), ([E, F, E, E, T, E, T, E, E, F, T, E, F], [F, E, E, E, T, E, T, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_104 (And.intro z_129 trivial)))

theorem z_131 : le (tf [E, F, E, E, T, E, T, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, T, E, E, F, E, F] [([E, F, E, E, E, T, T, T, E, E, F, E, F], [E, F, E, E, E, T, T, T, E, F, E, E, F]), ([E, F, E, E, T, E, T, E, T, E, F, E, F], [E, F, E, E, T, E, T, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 (And.intro z_130 trivial))

theorem z_132 : le (tf [F, E, E, E, T, F, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, T, T, E, F] [([F, E, E, E, E, F, T, E, E, T, T, E, F], [F, E, E, E, E, F, T, E, E, T, T, F, E]), ([F, E, E, E, T, F, E, E, E, T, E, T, F], [F, E, E, E, T, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_90 (And.intro z_124 trivial))

theorem z_133 : le (tf [F, E, E, E, T, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, E, T, E, F] [([F, E, E, E, E, T, F, E, T, E, T, E, F], [F, E, E, E, F, T, E, E, T, E, T, E, F]), ([F, E, E, E, T, E, F, E, E, T, T, E, F], [F, E, E, E, T, F, E, E, E, T, T, E, F]), ([F, E, E, E, T, E, F, E, T, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_45 (And.intro z_132 (And.intro z_125 trivial)))

theorem z_134 : le (tf [F, E, E, E, T, E, E, F, T, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, T, E, E, F] [([F, E, E, E, E, T, E, F, T, T, E, E, F], [F, E, E, E, E, T, F, E, T, T, E, E, F]), ([F, E, E, E, T, E, E, F, T, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 (And.intro z_133 trivial))

theorem z_135 : le (tf [F, E, F, E, E, E, T, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, T, E, F, E, T] [([F, E, F, E, E, E, E, T, T, E, F, E, T], [F, F, E, E, E, E, E, T, T, E, F, E, T]), ([F, E, F, E, E, E, T, E, E, T, F, E, T], [F, F, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_28 (And.intro z_35 trivial))

theorem z_136 : le (tf [F, E, E, F, E, E, T, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, T, E, F, T, E] [([F, E, E, F, E, E, E, T, T, E, F, T, E], [F, E, F, E, E, E, E, T, T, E, F, T, E]), ([F, E, E, F, E, E, T, E, E, T, F, T, E], [F, E, F, E, E, E, T, E, E, T, F, T, E]), ([F, E, E, F, E, E, T, E, T, E, F, E, T], [F, E, F, E, E, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_29 (And.intro z_36 (And.intro z_135 trivial)))

theorem z_137 : le (tf [F, E, E, F, E, E, T, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, T, E, E, F, E, T] [([F, E, E, F, E, E, T, E, T, E, F, E, T], [F, E, F, E, E, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_135 trivial)

theorem z_138 : le (tf [F, E, E, E, F, E, T, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, T, E, E, F, T, E] [([F, E, E, E, F, E, T, E, T, E, F, T, E], [F, E, E, F, E, E, T, E, T, E, F, T, E]), ([F, E, E, E, F, E, T, T, E, E, F, E, T], [F, E, E, F, E, E, T, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_136 (And.intro z_137 trivial))

theorem z_139 : le (tf [F, F, E, E, E, E, E, E, T, F, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, F, T, T, E] [([F, F, E, E, E, E, E, E, T, F, T, E, T], [F, F, E, E, E, E, E, F, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 trivial)

theorem z_140 : le (tf [F, E, F, E, E, E, E, T, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, F, T, T, E] [([F, E, F, E, E, E, E, E, T, F, T, T, E], [F, F, E, E, E, E, E, E, T, F, T, T, E]), ([F, E, F, E, E, E, E, T, E, F, T, E, T], [F, F, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_139 (And.intro z_57 trivial))

theorem z_141 : le (tf [F, E, F, E, E, E, E, T, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, T, F, E, E, T] [([F, E, F, E, E, E, E, T, E, F, T, E, T], [F, F, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_57 trivial)

theorem z_142 : le (tf [F, E, E, F, E, E, E, T, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, T, F, E, T, E] [([F, E, E, F, E, E, E, T, E, F, T, T, E], [F, E, F, E, E, E, E, T, E, F, T, T, E]), ([F, E, E, F, E, E, E, T, T, F, E, E, T], [F, E, F, E, E, E, E, T, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_140 (And.intro z_141 trivial))

theorem z_143 : le (tf [F, E, F, E, E, E, T, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, F, T, E, T] [([F, E, F, E, E, E, E, T, E, F, T, E, T], [F, F, E, E, E, E, E, T, E, F, T, E, T]), ([F, E, F, E, E, E, T, E, E, F, E, T, T], [F, F, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_57 (And.intro z_34 trivial))

theorem z_144 : le (tf [F, E, E, F, E, E, T, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, F, T, T, E] [([F, E, E, F, E, E, E, T, E, F, T, T, E], [F, E, F, E, E, E, E, T, E, F, T, T, E]), ([F, E, E, F, E, E, T, E, E, F, T, E, T], [F, E, F, E, E, E, T, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_140 (And.intro z_143 trivial))

theorem z_145 : le (tf [F, E, E, F, E, E, T, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, T, F, E, E, T] [([F, E, E, F, E, E, E, T, T, F, E, E, T], [F, E, F, E, E, E, E, T, T, F, E, E, T]), ([F, E, E, F, E, E, T, E, E, F, T, E, T], [F, E, F, E, E, E, T, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_141 (And.intro z_143 trivial))

theorem z_146 : le (tf [F, E, E, E, F, E, T, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, T, F, E, T, E] [([F, E, E, E, F, E, E, T, T, F, E, T, E], [F, E, E, F, E, E, E, T, T, F, E, T, E]), ([F, E, E, E, F, E, T, E, E, F, T, T, E], [F, E, E, F, E, E, T, E, E, F, T, T, E]), ([F, E, E, E, F, E, T, E, T, F, E, E, T], [F, E, E, F, E, E, T, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_142 (And.intro z_144 (And.intro z_145 trivial)))

theorem z_147 : le (tf [F, F, E, E, E, E, T, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, F, E, E, E, T, T] [([F, F, E, E, E, E, E, F, T, E, E, T, T], [F, F, E, E, E, E, F, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_55 trivial)

theorem z_148 : le (tf [F, F, E, E, E, E, T, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, F, E, T, E, T] [([F, F, E, E, E, E, E, T, F, E, T, E, T], [F, F, E, E, E, E, F, T, E, E, T, E, T]), ([F, F, E, E, E, E, T, E, F, E, E, T, T], [F, F, E, E, E, E, T, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 (And.intro z_147 trivial))

theorem z_149 : le (tf [F, F, E, E, E, E, T, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, F, T, T, E] [([F, F, E, E, E, E, E, T, E, F, T, T, E], [F, F, E, E, E, E, E, T, F, E, T, T, E]), ([F, F, E, E, E, E, T, E, E, F, T, E, T], [F, F, E, E, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 (And.intro z_148 trivial))

theorem z_150 : le (tf [F, F, E, E, E, T, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, E, E, F, E, E, T, T] [([F, F, E, E, E, E, T, E, F, E, E, T, T], [F, F, E, E, E, E, T, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_147 trivial)

theorem z_151 : le (tf [F, F, E, E, E, T, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, E, E, E, F, T, E, T] [([F, F, E, E, E, E, T, E, E, F, T, E, T], [F, F, E, E, E, E, T, E, F, E, T, E, T]), ([F, F, E, E, E, T, E, E, E, F, E, T, T], [F, F, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_148 (And.intro z_150 trivial))

theorem z_152 : le (tf [F, E, F, E, E, T, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, F, T, T, E] [([F, E, F, E, E, E, T, E, E, F, T, T, E], [F, F, E, E, E, E, T, E, E, F, T, T, E]), ([F, E, F, E, E, T, E, E, E, F, T, E, T], [F, F, E, E, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_149 (And.intro z_151 trivial))

theorem z_153 : le (tf [F, F, E, E, T, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, E, E, E, F, E, T, T] [([F, F, E, E, E, T, E, E, E, F, E, T, T], [F, F, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_150 trivial)

theorem z_154 : le (tf [F, E, F, E, T, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, E, F, T, E, T] [([F, E, F, E, E, T, E, E, E, F, T, E, T], [F, F, E, E, E, T, E, E, E, F, T, E, T]), ([F, E, F, E, T, E, E, E, E, F, E, T, T], [F, F, E, E, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_151 (And.intro z_153 trivial))

theorem z_155 : le (tf [F, E, E, F, T, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, F, T, T, E] [([F, E, E, F, E, T, E, E, E, F, T, T, E], [F, E, F, E, E, T, E, E, E, F, T, T, E]), ([F, E, E, F, T, E, E, E, E, F, T, E, T], [F, E, F, E, T, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_152 (And.intro z_154 trivial))

theorem z_156 : le (tf [F, E, F, E, E, E, E, F, T, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, F, T, T, E, E, T] [([F, E, F, E, E, E, E, F, T, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 trivial)

theorem z_157 : le (tf [F, E, F, E, E, E, T, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, F, E, E, T, E, T] [([F, E, F, E, E, E, E, F, T, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, T, E, T]), ([F, E, F, E, E, E, T, F, E, E, E, T, T], [F, F, E, E, E, E, T, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 (And.intro z_147 trivial))

theorem z_158 : le (tf [F, E, E, F, E, E, T, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, F, E, T, E, E, T] [([F, E, E, F, E, E, E, F, T, T, E, E, T], [F, E, F, E, E, E, E, F, T, T, E, E, T]), ([F, E, E, F, E, E, T, F, E, E, T, E, T], [F, E, F, E, E, E, T, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_156 (And.intro z_157 trivial))

theorem z_159 : le (tf [F, E, E, E, F, E, T, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, F, T, E, E, E, T] [([F, E, E, E, F, E, T, F, E, T, E, E, T], [F, E, E, F, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 trivial)

theorem z_160 : le (tf [F, F, E, E, E, E, F, E, T, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, T, T, E, E, T] [([F, F, E, E, E, E, F, E, T, E, T, E, T], [F, F, E, E, E, F, E, E, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 trivial)

theorem z_161 : le (tf [F, E, F, E, E, E, F, T, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, F, T, E, T, E, E, T] [([F, E, F, E, E, E, F, E, T, T, E, E, T], [F, F, E, E, E, E, F, E, T, T, E, E, T]), ([F, E, F, E, E, E, F, T, E, E, T, E, T], [F, F, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_160 (And.intro z_24 trivial))

theorem z_162 : le (tf [F, F, E, E, E, T, F, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, F, E, E, E, E, T, T] [([F, F, E, E, E, E, F, T, E, E, E, T, T], [F, F, E, E, E, F, E, T, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_23 trivial)

theorem z_163 : le (tf [F, E, F, E, E, T, F, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, F, E, E, E, T, E, T] [([F, E, F, E, E, E, F, T, E, E, T, E, T], [F, F, E, E, E, E, F, T, E, E, T, E, T]), ([F, E, F, E, E, T, F, E, E, E, E, T, T], [F, F, E, E, E, T, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 (And.intro z_162 trivial))

theorem z_164 : le (tf [F, E, E, F, E, T, F, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, F, E, E, T, E, E, T] [([F, E, E, F, E, E, F, T, E, T, E, E, T], [F, E, F, E, E, E, F, T, E, T, E, E, T]), ([F, E, E, F, E, T, F, E, E, E, T, E, T], [F, E, F, E, E, T, F, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_161 (And.intro z_163 trivial))

theorem z_165 : le (tf [F, F, E, E, T, E, E, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, E, F, E, E, E, T, T] [([F, F, E, E, E, T, E, F, E, E, E, T, T], [F, F, E, E, E, T, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_162 trivial)

theorem z_166 : le (tf [F, E, F, E, T, E, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, F, E, E, T, E, T] [([F, E, F, E, E, T, E, F, E, E, T, E, T], [F, E, F, E, E, T, F, E, E, E, T, E, T]), ([F, E, F, E, T, E, E, F, E, E, E, T, T], [F, F, E, E, T, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_163 (And.intro z_165 trivial))

theorem z_167 : le (tf [F, E, E, F, T, E, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, F, E, T, E, E, T] [([F, E, E, F, E, T, E, F, E, T, E, E, T], [F, E, E, F, E, T, F, E, E, T, E, E, T]), ([F, E, E, F, T, E, E, F, E, E, T, E, T], [F, E, F, E, T, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_164 (And.intro z_166 trivial))

theorem z_168 : le (tf [F, E, E, E, T, F, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, F, T, E, E, E, T] [([F, E, E, E, E, F, T, F, T, E, E, E, T], [F, E, E, E, F, E, T, F, T, E, E, E, T]), ([F, E, E, E, T, F, E, F, E, T, E, E, T], [F, E, E, F, T, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_159 (And.intro z_167 trivial))

theorem z_169 : le (tf [F, E, E, E, T, F, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, T, F, E, T, E] [([F, E, E, E, E, F, T, E, T, F, E, T, E], [F, E, E, E, F, E, T, E, T, F, E, T, E]), ([F, E, E, E, T, F, E, E, E, F, T, T, E], [F, E, E, F, T, E, E, E, E, F, T, T, E]), ([F, E, E, E, T, F, E, E, T, F, E, E, T], [F, E, E, E, T, F, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_146 (And.intro z_155 (And.intro z_168 trivial)))

theorem z_170 : le (tf [F, E, E, E, F, E, T, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, T, E, F, E, E, T] [([F, E, E, E, F, E, T, E, T, F, E, E, T], [F, E, E, F, E, E, T, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_145 trivial)

theorem z_171 : le (tf [F, E, E, E, T, F, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, T, E, F, E, E, T] [([F, E, E, E, E, F, T, T, E, F, E, E, T], [F, E, E, E, F, E, T, T, E, F, E, E, T]), ([F, E, E, E, T, F, E, E, T, F, E, E, T], [F, E, E, E, T, F, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_170 (And.intro z_168 trivial))

theorem z_172 : le (tf [F, E, E, E, T, F, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, T, E, E, F, T, E] [([F, E, E, E, E, F, T, T, E, E, F, T, E], [F, E, E, E, F, E, T, T, E, E, F, T, E]), ([F, E, E, E, T, F, E, E, T, E, F, T, E], [F, E, E, E, T, F, E, E, T, F, E, T, E]), ([F, E, E, E, T, F, E, T, E, E, F, E, T], [F, E, E, E, T, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_138 (And.intro z_169 (And.intro z_171 trivial)))

theorem z_173 : le (tf [F, E, E, E, T, F, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, T, E, E, E, E, T, F] [([F, E, E, E, T, F, E, T, E, E, E, T, F], [F, E, E, E, T, F, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_172 trivial)

theorem z_174 : le (tf [F, E, E, E, T, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, E, T, E, F] [([F, E, E, E, E, T, T, F, E, E, T, E, F], [F, E, E, E, E, T, T, F, E, E, T, F, E]), ([F, E, E, E, T, E, E, F, T, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, T, E, F]), ([F, E, E, E, T, E, T, F, E, E, E, T, F], [F, E, E, E, T, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 (And.intro z_133 (And.intro z_173 trivial)))

theorem z_175 : le (tf [E, F, E, E, T, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, T, E, E, F] [([E, F, E, E, E, T, T, F, E, T, E, E, F], [F, E, E, E, E, T, T, F, E, T, E, E, F]), ([E, F, E, E, T, E, E, F, T, T, E, E, F], [F, E, E, E, T, E, E, F, T, T, E, E, F]), ([E, F, E, E, T, E, T, F, E, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 (And.intro z_134 (And.intro z_174 trivial)))

theorem z_176 : le (tf [F, E, E, E, T, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, F, E, E, E, T, F] [([F, E, E, E, T, E, T, F, E, E, E, T, F], [F, E, E, E, T, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_173 trivial)

theorem z_177 : le (tf [F, E, E, E, T, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, F, E, T, E, F] [([F, E, E, E, T, E, T, E, F, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, T, E, F]), ([F, E, E, E, T, T, E, E, F, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_174 (And.intro z_176 trivial))

theorem z_178 : le (tf [E, F, E, E, T, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, F, T, E, E, F] [([E, F, E, E, T, E, T, E, F, T, E, E, F], [E, F, E, E, T, E, T, F, E, T, E, E, F]), ([E, F, E, E, T, T, E, E, F, E, T, E, F], [F, E, E, E, T, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_175 (And.intro z_177 trivial))

theorem z_179 : le (tf [E, F, E, E, T, T, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, T, E, F, E, F] [([E, F, E, E, T, E, T, E, T, E, F, E, F], [E, F, E, E, T, E, T, E, T, F, E, E, F]), ([E, F, E, E, T, T, E, E, E, T, F, E, F], [E, F, E, E, T, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_130 (And.intro z_178 trivial))

theorem z_180 : le (tf [E, F, E, E, T, T, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, T, E, E, E, F, F] [([E, F, E, E, T, E, T, T, E, E, E, F, F], [E, F, E, E, T, E, T, T, E, E, F, E, F]), ([E, F, E, E, T, T, E, E, T, E, E, F, F], [E, F, E, E, T, T, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 (And.intro z_179 trivial))

theorem z_181 : le (tf [E, E, F, E, T, T, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, T, E, E, E, E, F, F] [([E, E, F, E, T, T, E, T, E, E, E, F, F], [E, F, E, E, T, T, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_180 trivial)

theorem z_182 : le (tf [E, E, F, E, T, T, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, T, E, E, F, E, F] [([E, E, F, E, T, E, T, T, E, E, F, E, F], [E, F, E, E, T, E, T, T, E, E, F, E, F]), ([E, E, F, E, T, T, E, E, T, E, F, E, F], [E, F, E, E, T, T, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 (And.intro z_179 trivial))

theorem z_183 : le (tf [E, E, F, E, T, E, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, T, E, F, E, E, F] [([E, E, F, E, E, T, T, T, E, F, E, E, F], [E, F, E, E, E, T, T, T, E, F, E, E, F]), ([E, E, F, E, T, E, T, E, T, F, E, E, F], [E, F, E, E, T, E, T, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 (And.intro z_130 trivial))

theorem z_184 : le (tf [E, E, F, E, T, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, T, E, E, E, F] [([E, E, F, E, E, T, T, F, T, E, E, E, F], [E, F, E, E, E, T, T, F, T, E, E, E, F]), ([E, E, F, E, T, E, T, F, E, T, E, E, F], [E, F, E, E, T, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_175 trivial))

theorem z_185 : le (tf [F, E, E, F, E, E, E, T, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, T, E, T, F, E] [([F, E, E, F, E, E, E, T, E, T, T, F, E], [F, E, F, E, E, E, E, T, E, T, T, F, E]), ([F, E, E, F, E, E, E, T, T, E, E, F, T], [F, E, F, E, E, E, E, T, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_64 trivial))

theorem z_186 : le (tf [F, E, E, E, F, E, E, T, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, T, E, F, E] [([F, E, E, E, F, E, E, T, T, E, T, F, E], [F, E, E, F, E, E, E, T, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_185 trivial)

theorem z_187 : le (tf [F, E, E, E, F, E, T, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, T, E, T, F, E] [([F, E, E, E, F, E, E, T, T, E, T, F, E], [F, E, E, F, E, E, E, T, T, E, T, F, E]), ([F, E, E, E, F, E, T, E, E, T, T, F, E], [F, E, E, F, E, E, T, E, E, T, T, F, E]), ([F, E, E, E, F, E, T, E, T, E, E, F, T], [F, E, E, F, E, E, T, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_185 (And.intro z_60 (And.intro z_65 trivial)))

theorem z_188 : le (tf [F, E, E, E, E, F, T, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, T, E, F, E] [([F, E, E, E, E, F, E, T, T, T, E, F, E], [F, E, E, E, F, E, E, T, T, T, E, F, E]), ([F, E, E, E, E, F, T, E, T, E, T, F, E], [F, E, E, E, F, E, T, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_186 (And.intro z_187 trivial))

theorem z_189 : le (tf [F, E, E, E, E, T, E, F, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, T, E, F, E] [([F, E, E, E, E, E, T, F, T, T, E, F, E], [F, E, E, E, E, F, T, E, T, T, E, F, E]), ([F, E, E, E, E, T, E, F, T, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_188 (And.intro z_67 trivial))

theorem z_190 : le (tf [E, F, E, E, E, T, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, T, E, F, E] [([E, F, E, E, E, T, E, F, T, T, E, F, E], [F, E, E, E, E, T, E, F, T, T, E, F, E]), ([E, F, E, E, E, T, T, F, E, E, T, F, E], [F, E, E, E, E, T, T, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_189 (And.intro z_80 trivial))

theorem z_191 : le (tf [F, E, E, F, T, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, E, T, F, T] [([F, E, E, F, E, T, E, E, E, E, T, F, T], [F, E, F, E, E, T, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_61 trivial)

theorem z_192 : le (tf [F, E, E, E, T, F, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, T, E, F, T] [([F, E, E, E, E, F, T, E, E, T, E, F, T], [F, E, E, E, F, E, T, E, E, T, E, F, T]), ([F, E, E, E, T, F, E, E, E, E, T, F, T], [F, E, E, F, T, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_89 (And.intro z_191 trivial))

theorem z_193 : le (tf [F, E, E, E, T, E, F, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, T, F, E] [([F, E, E, E, E, T, F, E, E, T, T, F, E], [F, E, E, E, F, T, E, E, E, T, T, F, E]), ([F, E, E, E, T, E, F, E, E, T, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_63 (And.intro z_192 trivial))

theorem z_194 : le (tf [F, E, E, E, T, E, F, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, E, E, F, T] [([F, E, E, E, E, T, F, E, T, E, E, F, T], [F, E, E, E, F, T, E, E, T, E, E, F, T]), ([F, E, E, E, T, E, F, E, E, T, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 (And.intro z_192 trivial))

theorem z_195 : le (tf [F, E, E, E, T, E, E, F, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, T, F, E] [([F, E, E, E, E, T, E, F, T, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, T, F, E]), ([F, E, E, E, T, E, E, F, E, T, T, F, E], [F, E, E, E, T, E, F, E, E, T, T, F, E]), ([F, E, E, E, T, E, E, F, T, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 (And.intro z_193 (And.intro z_194 trivial)))

theorem z_196 : le (tf [E, F, E, E, T, E, E, F, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, T, E, F, E] [([E, F, E, E, E, T, E, F, T, T, E, F, E], [F, E, E, E, E, T, E, F, T, T, E, F, E]), ([E, F, E, E, T, E, E, F, T, E, T, F, E], [F, E, E, E, T, E, E, F, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_189 (And.intro z_195 trivial))

theorem z_197 : le (tf [F, E, E, E, T, E, T, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, E, E, F, T] [([F, E, E, E, E, T, T, F, E, E, E, F, T], [F, E, E, E, E, T, T, F, E, E, F, E, T]), ([F, E, E, E, T, E, E, F, T, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 (And.intro z_194 trivial))

theorem z_198 : le (tf [E, F, E, E, T, E, T, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, T, F, E] [([E, F, E, E, E, T, T, F, E, E, T, F, E], [F, E, E, E, E, T, T, F, E, E, T, F, E]), ([E, F, E, E, T, E, E, F, T, E, T, F, E], [F, E, E, E, T, E, E, F, T, E, T, F, E]), ([E, F, E, E, T, E, T, F, E, E, E, F, T], [F, E, E, E, T, E, T, F, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 (And.intro z_195 (And.intro z_197 trivial)))

theorem z_199 : le (tf [E, E, F, E, T, E, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, T, E, F, E] [([E, E, F, E, E, T, T, F, E, T, E, F, E], [E, F, E, E, E, T, T, F, E, T, E, F, E]), ([E, E, F, E, T, E, E, F, T, T, E, F, E], [E, F, E, E, T, E, E, F, T, T, E, F, E]), ([E, E, F, E, T, E, T, F, E, E, T, F, E], [E, F, E, E, T, E, T, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_190 (And.intro z_196 (And.intro z_198 trivial)))

theorem z_200 : le (tf [F, E, E, E, F, E, E, T, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, F, T, E, E] [([F, E, E, E, F, E, E, T, T, F, E, T, E], [F, E, E, F, E, E, E, T, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_142 trivial)

theorem z_201 : le (tf [F, E, E, E, E, F, T, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, F, T, E, E] [([F, E, E, E, E, F, E, T, T, F, T, E, E], [F, E, E, E, F, E, E, T, T, F, T, E, E]), ([F, E, E, E, E, F, T, E, T, F, E, T, E], [F, E, E, E, F, E, T, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_200 (And.intro z_146 trivial))

theorem z_202 : le (tf [E, F, E, E, T, F, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, T, F, T, E, E] [([E, F, E, E, E, F, T, E, T, F, T, E, E], [F, E, E, E, E, F, T, E, T, F, T, E, E]), ([E, F, E, E, T, F, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_201 (And.intro z_169 trivial))

theorem z_203 : le (tf [E, F, E, E, T, F, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, T, T, E, F, E] [([E, F, E, E, E, F, T, E, T, T, E, F, E], [F, E, E, E, E, F, T, E, T, T, E, F, E]), ([E, F, E, E, T, F, E, E, T, E, T, F, E], [E, F, E, E, T, F, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_188 (And.intro z_202 trivial))

theorem z_204 : le (tf [F, E, F, T, E, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, E, E, E, E, E, T, F, T] [([F, E, F, E, T, E, E, E, E, E, T, F, T], [F, E, F, E, T, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_154 trivial)

theorem z_205 : le (tf [F, E, E, T, F, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, T, E, F, T] [([F, E, E, E, F, T, E, E, E, T, E, F, T], [F, E, E, F, E, T, E, E, E, T, E, F, T]), ([F, E, E, T, F, E, E, E, E, E, T, F, T], [F, E, F, T, E, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_62 (And.intro z_204 trivial))

theorem z_206 : le (tf [E, F, E, T, F, E, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, E, T, T, F, E] [([E, F, E, E, F, T, E, E, E, T, T, F, E], [F, E, E, E, F, T, E, E, E, T, T, F, E]), ([E, F, E, T, F, E, E, E, E, T, E, F, T], [F, E, E, T, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_63 (And.intro z_205 trivial))

theorem z_207 : le (tf [F, E, F, E, E, T, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, T, E, E, F, T] [([F, E, F, E, E, E, T, E, T, E, E, F, T], [F, E, F, E, E, E, T, E, T, E, F, E, T]), ([F, E, F, E, E, T, E, E, E, T, E, F, T], [F, E, F, E, E, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_135 (And.intro z_41 trivial))

theorem z_208 : le (tf [F, E, E, F, T, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, T, E, E, F, T] [([F, E, E, F, E, T, E, E, T, E, E, F, T], [F, E, F, E, E, T, E, E, T, E, E, F, T]), ([F, E, E, F, T, E, E, E, E, T, E, F, T], [F, E, E, F, T, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_207 (And.intro z_123 trivial))

theorem z_209 : le (tf [F, E, E, T, E, F, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, T, E, E, F, T] [([F, E, E, E, T, F, E, E, T, E, E, F, T], [F, E, E, F, T, E, E, E, T, E, E, F, T]), ([F, E, E, T, E, F, E, E, E, T, E, F, T], [F, E, E, T, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_208 (And.intro z_205 trivial))

theorem z_210 : le (tf [E, F, E, T, E, F, E, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, E, T, E, T, F, E] [([E, F, E, E, T, F, E, E, T, E, T, F, E], [E, F, E, E, T, F, E, E, T, F, T, E, E]), ([E, F, E, T, E, F, E, E, E, T, T, F, E], [E, F, E, T, F, E, E, E, E, T, T, F, E]), ([E, F, E, T, E, F, E, E, T, E, E, F, T], [F, E, E, T, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_202 (And.intro z_206 (And.intro z_209 trivial)))

theorem z_211 : le (tf [E, F, E, T, E, E, F, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, T, T, E, F, E] [([E, F, E, E, T, E, F, E, T, T, E, F, E], [E, F, E, E, T, F, E, E, T, T, E, F, E]), ([E, F, E, T, E, E, F, E, T, E, T, F, E], [E, F, E, T, E, F, E, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_203 (And.intro z_210 trivial))

theorem z_212 : le (tf [F, E, T, E, F, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, E, T, F, T] [([F, E, E, T, F, E, E, E, E, E, T, F, T], [F, E, F, T, E, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_204 trivial)

theorem z_213 : le (tf [F, E, T, E, E, F, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, T, E, F, T] [([F, E, E, T, E, F, E, E, E, T, E, F, T], [F, E, E, T, F, E, E, E, E, T, E, F, T]), ([F, E, T, E, E, F, E, E, E, E, T, F, T], [F, E, T, E, F, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_205 (And.intro z_212 trivial))

theorem z_214 : le (tf [E, F, T, E, E, F, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, E, T, T, F, E] [([E, F, E, T, E, F, E, E, E, T, T, F, E], [E, F, E, T, F, E, E, E, E, T, T, F, E]), ([E, F, T, E, E, F, E, E, E, T, E, F, T], [F, E, T, E, E, F, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_206 (And.intro z_213 trivial))

theorem z_215 : le (tf [F, E, T, E, E, E, F, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, T, E, E, F, T] [([F, E, E, T, E, E, F, E, T, E, E, F, T], [F, E, E, T, E, F, E, E, T, E, E, F, T]), ([F, E, T, E, E, E, F, E, E, T, E, F, T], [F, E, T, E, E, F, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_209 (And.intro z_213 trivial))

theorem z_216 : le (tf [E, F, T, E, E, E, F, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, F, E, T, E, T, F, E] [([E, F, E, T, E, E, F, E, T, E, T, F, E], [E, F, E, T, E, F, E, E, T, E, T, F, E]), ([E, F, T, E, E, E, F, E, E, T, T, F, E], [E, F, T, E, E, F, E, E, E, T, T, F, E]), ([E, F, T, E, E, E, F, E, T, E, E, F, T], [F, E, T, E, E, E, F, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_210 (And.intro z_214 (And.intro z_215 trivial)))

theorem z_217 : le (tf [E, F, T, E, E, E, E, F, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, T, T, E, F, E] [([E, F, E, T, E, E, E, F, T, T, E, F, E], [E, F, E, T, E, E, F, E, T, T, E, F, E]), ([E, F, T, E, E, E, E, F, T, E, T, F, E], [E, F, T, E, E, E, F, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_211 (And.intro z_216 trivial))

theorem z_218 : le (tf [F, E, E, F, E, E, E, E, T, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, F, T, T, E] [([F, E, E, F, E, E, E, E, T, F, T, E, T], [F, E, F, E, E, E, E, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 trivial)

theorem z_219 : le (tf [F, E, F, E, E, E, E, T, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, F, E, T, T] [([F, E, F, E, E, E, E, E, T, F, E, T, T], [F, F, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_220 : le (tf [F, E, E, F, E, E, E, T, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, F, T, E, T] [([F, E, E, F, E, E, E, E, T, F, T, E, T], [F, E, F, E, E, E, E, E, T, F, T, E, T]), ([F, E, E, F, E, E, E, T, E, F, E, T, T], [F, E, F, E, E, E, E, T, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 (And.intro z_219 trivial))

theorem z_221 : le (tf [F, E, E, E, F, E, E, T, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, F, T, T, E] [([F, E, E, E, F, E, E, E, T, F, T, T, E], [F, E, E, F, E, E, E, E, T, F, T, T, E]), ([F, E, E, E, F, E, E, T, E, F, T, E, T], [F, E, E, F, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_218 (And.intro z_220 trivial))

theorem z_222 : le (tf [F, E, E, E, F, E, E, T, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, F, E, E, T] [([F, E, E, E, F, E, E, T, E, F, T, E, T], [F, E, E, F, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_220 trivial)

theorem z_223 : le (tf [F, E, E, E, E, F, E, T, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, F, E, T, E] [([F, E, E, E, E, F, E, T, E, F, T, T, E], [F, E, E, E, F, E, E, T, E, F, T, T, E]), ([F, E, E, E, E, F, E, T, T, F, E, E, T], [F, E, E, E, F, E, E, T, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_221 (And.intro z_222 trivial))

theorem z_224 : le (tf [F, E, F, E, E, T, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, F, E, T, T] [([F, E, F, E, E, E, T, E, E, F, E, T, T], [F, F, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_34 trivial)

theorem z_225 : le (tf [F, E, E, F, E, T, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, F, T, E, T] [([F, E, E, F, E, E, T, E, E, F, T, E, T], [F, E, F, E, E, E, T, E, E, F, T, E, T]), ([F, E, E, F, E, T, E, E, E, F, E, T, T], [F, E, F, E, E, T, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_143 (And.intro z_224 trivial))

theorem z_226 : le (tf [F, E, E, E, F, T, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, F, T, T, E] [([F, E, E, E, F, E, T, E, E, F, T, T, E], [F, E, E, F, E, E, T, E, E, F, T, T, E]), ([F, E, E, E, F, T, E, E, E, F, T, E, T], [F, E, E, F, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_144 (And.intro z_225 trivial))

theorem z_227 : le (tf [F, E, E, E, F, T, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, T, F, E, E, T] [([F, E, E, E, F, E, T, E, T, F, E, E, T], [F, E, E, F, E, E, T, E, T, F, E, E, T]), ([F, E, E, E, F, T, E, E, E, F, T, E, T], [F, E, E, F, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_145 (And.intro z_225 trivial))

theorem z_228 : le (tf [F, E, E, E, E, T, F, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, F, E, T, E] [([F, E, E, E, E, E, F, T, T, F, E, T, E], [F, E, E, E, E, F, E, T, T, F, E, T, E]), ([F, E, E, E, E, T, F, E, E, F, T, T, E], [F, E, E, E, F, T, E, E, E, F, T, T, E]), ([F, E, E, E, E, T, F, E, T, F, E, E, T], [F, E, E, E, F, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 (And.intro z_226 (And.intro z_227 trivial)))

theorem z_229 : le (tf [F, E, E, E, E, T, E, F, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, F, T, E, E] [([F, E, E, E, E, E, T, F, T, F, T, E, E], [F, E, E, E, E, F, T, E, T, F, T, E, E]), ([F, E, E, E, E, T, E, F, T, F, E, T, E], [F, E, E, E, E, T, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_201 (And.intro z_228 trivial))

theorem z_230 : le (tf [F, E, E, E, E, T, T, F, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_231 : le (tf [F, E, E, E, E, T, T, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, F, E, T, E] [([F, E, E, E, E, T, E, F, T, F, E, T, E], [F, E, E, E, E, T, F, E, T, F, E, T, E]), ([F, E, E, E, E, T, T, F, E, F, E, E, T], [F, E, E, E, E, T, T, F, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_228 (And.intro z_230 trivial))

theorem z_232 : le (tf [E, F, E, E, E, T, T, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, F, T, E, E] [([E, F, E, E, E, T, E, F, T, F, T, E, E], [F, E, E, E, E, T, E, F, T, F, T, E, E]), ([E, F, E, E, E, T, T, F, E, F, E, T, E], [F, E, E, E, E, T, T, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_229 (And.intro z_231 trivial))

theorem z_233 : le (tf [F, E, E, F, E, E, T, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, F, E, T, T] [([F, E, E, F, E, E, E, T, E, F, E, T, T], [F, E, F, E, E, E, E, T, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_219 trivial)

theorem z_234 : le (tf [F, E, E, E, F, E, T, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, F, T, E, T] [([F, E, E, E, F, E, E, T, E, F, T, E, T], [F, E, E, F, E, E, E, T, E, F, T, E, T]), ([F, E, E, E, F, E, T, E, E, F, E, T, T], [F, E, E, F, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_220 (And.intro z_233 trivial))

theorem z_235 : le (tf [F, E, E, F, T, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, F, E, T, T] [([F, E, E, F, E, T, E, E, E, F, E, T, T], [F, E, F, E, E, T, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_224 trivial)

theorem z_236 : le (tf [F, E, E, E, T, F, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, F, T, E, T] [([F, E, E, E, E, F, T, E, E, F, T, E, T], [F, E, E, E, F, E, T, E, E, F, T, E, T]), ([F, E, E, E, T, F, E, E, E, F, E, T, T], [F, E, E, F, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_234 (And.intro z_235 trivial))

theorem z_237 : le (tf [F, E, E, E, T, E, F, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, F, T, T, E] [([F, E, E, E, E, T, F, E, E, F, T, T, E], [F, E, E, E, F, T, E, E, E, F, T, T, E]), ([F, E, E, E, T, E, F, E, E, F, T, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_226 (And.intro z_236 trivial))

theorem z_238 : le (tf [F, E, E, E, T, E, F, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, F, E, E, T] [([F, E, E, E, E, T, F, E, T, F, E, E, T], [F, E, E, E, F, T, E, E, T, F, E, E, T]), ([F, E, E, E, T, E, F, E, E, F, T, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_227 (And.intro z_236 trivial))

theorem z_239 : le (tf [F, E, E, E, T, E, E, F, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, F, E, T, E] [([F, E, E, E, E, T, E, F, T, F, E, T, E], [F, E, E, E, E, T, F, E, T, F, E, T, E]), ([F, E, E, E, T, E, E, F, E, F, T, T, E], [F, E, E, E, T, E, F, E, E, F, T, T, E]), ([F, E, E, E, T, E, E, F, T, F, E, E, T], [F, E, E, E, T, E, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_228 (And.intro z_237 (And.intro z_238 trivial)))

theorem z_240 : le (tf [E, F, E, E, T, E, E, F, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, F, T, E, E] [([E, F, E, E, E, T, E, F, T, F, T, E, E], [F, E, E, E, E, T, E, F, T, F, T, E, E]), ([E, F, E, E, T, E, E, F, T, F, E, T, E], [F, E, E, E, T, E, E, F, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_229 (And.intro z_239 trivial))

theorem z_241 : le (tf [F, E, E, E, T, E, T, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, F, E, E, T] [([F, E, E, E, E, T, T, F, E, F, E, E, T], [F, E, E, E, E, T, T, F, F, E, E, E, T]), ([F, E, E, E, T, E, E, F, T, F, E, E, T], [F, E, E, E, T, E, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_230 (And.intro z_238 trivial))

theorem z_242 : le (tf [E, F, E, E, T, E, T, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, F, E, T, E] [([E, F, E, E, E, T, T, F, E, F, E, T, E], [F, E, E, E, E, T, T, F, E, F, E, T, E]), ([E, F, E, E, T, E, E, F, T, F, E, T, E], [F, E, E, E, T, E, E, F, T, F, E, T, E]), ([E, F, E, E, T, E, T, F, E, F, E, E, T], [F, E, E, E, T, E, T, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 (And.intro z_239 (And.intro z_241 trivial)))

theorem z_243 : le (tf [E, E, F, E, T, E, T, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, F, T, E, E] [([E, E, F, E, E, T, T, F, E, F, T, E, E], [E, F, E, E, E, T, T, F, E, F, T, E, E]), ([E, E, F, E, T, E, E, F, T, F, T, E, E], [E, F, E, E, T, E, E, F, T, F, T, E, E]), ([E, E, F, E, T, E, T, F, E, F, E, T, E], [E, F, E, E, T, E, T, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_232 (And.intro z_240 (And.intro z_242 trivial)))

theorem z_244 : le (tf [F, E, F, T, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, E, E, E, E, F, E, T, T] [([F, E, F, E, T, E, E, E, E, F, E, T, T], [F, F, E, E, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_153 trivial)

theorem z_245 : le (tf [F, E, E, T, F, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, F, T, E, T] [([F, E, E, E, F, T, E, E, E, F, T, E, T], [F, E, E, F, E, T, E, E, E, F, T, E, T]), ([F, E, E, T, F, E, E, E, E, F, E, T, T], [F, E, F, T, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_225 (And.intro z_244 trivial))

theorem z_246 : le (tf [F, E, E, T, E, F, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, F, T, T, E] [([F, E, E, E, T, F, E, E, E, F, T, T, E], [F, E, E, F, T, E, E, E, E, F, T, T, E]), ([F, E, E, T, E, F, E, E, E, F, T, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_155 (And.intro z_245 trivial))

theorem z_247 : le (tf [F, E, E, T, E, F, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, T, F, E, E, T] [([F, E, E, E, T, F, E, E, T, F, E, E, T], [F, E, E, E, T, F, E, F, T, E, E, E, T]), ([F, E, E, T, E, F, E, E, E, F, T, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_168 (And.intro z_245 trivial))

theorem z_248 : le (tf [F, E, E, T, E, E, F, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, T, F, E, T, E] [([F, E, E, E, T, E, F, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, T, F, E, T, E]), ([F, E, E, T, E, E, F, E, E, F, T, T, E], [F, E, E, T, E, F, E, E, E, F, T, T, E]), ([F, E, E, T, E, E, F, E, T, F, E, E, T], [F, E, E, T, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_169 (And.intro z_246 (And.intro z_247 trivial)))

theorem z_249 : le (tf [E, F, E, T, E, E, F, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, T, F, T, E, E] [([E, F, E, E, T, E, F, E, T, F, T, E, E], [E, F, E, E, T, F, E, E, T, F, T, E, E]), ([E, F, E, T, E, E, F, E, T, F, E, T, E], [F, E, E, T, E, E, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_202 (And.intro z_248 trivial))

theorem z_250 : le (tf [F, E, T, E, F, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, F, E, T, T] [([F, E, E, T, F, E, E, E, E, F, E, T, T], [F, E, F, T, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_244 trivial)

theorem z_251 : le (tf [F, E, T, E, E, F, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, F, T, E, T] [([F, E, E, T, E, F, E, E, E, F, T, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, T]), ([F, E, T, E, E, F, E, E, E, F, E, T, T], [F, E, T, E, F, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_245 (And.intro z_250 trivial))

theorem z_252 : le (tf [F, E, T, E, E, E, F, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, F, T, T, E] [([F, E, E, T, E, E, F, E, E, F, T, T, E], [F, E, E, T, E, F, E, E, E, F, T, T, E]), ([F, E, T, E, E, E, F, E, E, F, T, E, T], [F, E, T, E, E, F, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_246 (And.intro z_251 trivial))

theorem z_253 : le (tf [F, E, T, E, E, E, F, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, T, F, E, E, T] [([F, E, E, T, E, E, F, E, T, F, E, E, T], [F, E, E, T, E, F, E, E, T, F, E, E, T]), ([F, E, T, E, E, E, F, E, E, F, T, E, T], [F, E, T, E, E, F, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_247 (And.intro z_251 trivial))

theorem z_254 : le (tf [F, E, T, E, E, E, E, F, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, T, F, E, T, E] [([F, E, E, T, E, E, E, F, T, F, E, T, E], [F, E, E, T, E, E, F, E, T, F, E, T, E]), ([F, E, T, E, E, E, E, F, E, F, T, T, E], [F, E, T, E, E, E, F, E, E, F, T, T, E]), ([F, E, T, E, E, E, E, F, T, F, E, E, T], [F, E, T, E, E, E, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 (And.intro z_252 (And.intro z_253 trivial)))

theorem z_255 : le (tf [E, F, T, E, E, E, E, F, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, T, F, T, E, E] [([E, F, E, T, E, E, E, F, T, F, T, E, E], [E, F, E, T, E, E, F, E, T, F, T, E, E]), ([E, F, T, E, E, E, E, F, T, F, E, T, E], [F, E, T, E, E, E, E, F, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 (And.intro z_254 trivial))

theorem z_256 : le (tf [F, E, E, E, E, F, T, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, T, E, F, E, T, E] [([F, E, E, E, E, F, T, E, T, F, E, T, E], [F, E, E, E, F, E, T, E, T, F, E, T, E]), ([F, E, E, E, E, F, T, T, E, F, E, E, T], [F, E, E, E, F, E, T, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_146 (And.intro z_170 trivial))

theorem z_257 : le (tf [E, F, E, E, T, F, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, T, E, F, E, T, E] [([E, F, E, E, E, F, T, T, E, F, E, T, E], [F, E, E, E, E, F, T, T, E, F, E, T, E]), ([E, F, E, E, T, F, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, T, F, E, T, E]), ([E, F, E, E, T, F, E, T, E, F, E, E, T], [F, E, E, E, T, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_256 (And.intro z_169 (And.intro z_171 trivial)))

theorem z_258 : le (tf [E, F, E, E, T, F, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, T, E, E, F, E, E, T] [([E, F, E, E, T, F, E, T, E, F, E, E, T], [F, E, E, E, T, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_171 trivial)

theorem z_259 : le (tf [E, E, F, E, T, F, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, T, E, E, F, E, T, E] [([E, E, F, E, T, F, E, T, E, F, E, T, E], [E, F, E, E, T, F, E, T, E, F, E, T, E]), ([E, E, F, E, T, F, T, E, E, F, E, E, T], [E, F, E, E, T, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_257 (And.intro z_258 trivial))

theorem z_260 : le (tf [F, F, E, E, E, E, E, E, F, T, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, T, T, E, T] [([F, F, E, E, E, E, E, E, F, T, E, T, T], [F, F, E, E, E, E, E, F, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 trivial)

theorem z_261 : le (tf [F, E, F, E, E, E, E, E, F, T, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, F, T, T, T, E] [([F, E, F, E, E, E, E, E, F, T, T, E, T], [F, F, E, E, E, E, E, E, F, T, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 trivial)

theorem z_262 : le (tf [F, E, F, E, E, E, E, T, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, F, E, T, E, T] [([F, E, F, E, E, E, E, E, F, T, T, E, T], [F, F, E, E, E, E, E, E, F, T, T, E, T]), ([F, E, F, E, E, E, E, T, F, E, E, T, T], [F, F, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 (And.intro z_33 trivial))

theorem z_263 : le (tf [F, E, E, F, E, E, E, T, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, F, E, T, T, E] [([F, E, E, F, E, E, E, E, F, T, T, T, E], [F, E, F, E, E, E, E, E, F, T, T, T, E]), ([F, E, E, F, E, E, E, T, F, E, T, E, T], [F, E, F, E, E, E, E, T, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_261 (And.intro z_262 trivial))

theorem z_264 : le (tf [F, E, E, F, E, E, E, T, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, F, T, E, E, T] [([F, E, E, F, E, E, E, T, F, E, T, E, T], [F, E, F, E, E, E, E, T, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_262 trivial)

theorem z_265 : le (tf [F, E, E, E, F, E, E, T, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, F, T, E, T, E] [([F, E, E, E, F, E, E, T, F, E, T, T, E], [F, E, E, F, E, E, E, T, F, E, T, T, E]), ([F, E, E, E, F, E, E, T, F, T, E, E, T], [F, E, E, F, E, E, E, T, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_263 (And.intro z_264 trivial))

theorem z_266 : le (tf [F, E, F, E, E, E, T, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, F, E, E, T, T] [([F, E, F, E, E, E, E, T, F, E, E, T, T], [F, F, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_33 trivial)

theorem z_267 : le (tf [F, E, E, F, E, E, T, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, F, E, T, E, T] [([F, E, E, F, E, E, E, T, F, E, T, E, T], [F, E, F, E, E, E, E, T, F, E, T, E, T]), ([F, E, E, F, E, E, T, E, F, E, E, T, T], [F, E, F, E, E, E, T, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_262 (And.intro z_266 trivial))

theorem z_268 : le (tf [F, E, E, E, F, E, T, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, F, E, T, T, E] [([F, E, E, E, F, E, E, T, F, E, T, T, E], [F, E, E, F, E, E, E, T, F, E, T, T, E]), ([F, E, E, E, F, E, T, E, F, E, T, E, T], [F, E, E, F, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_263 (And.intro z_267 trivial))

theorem z_269 : le (tf [F, E, E, E, F, E, T, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, F, T, E, E, T] [([F, E, E, E, F, E, E, T, F, T, E, E, T], [F, E, E, F, E, E, E, T, F, T, E, E, T]), ([F, E, E, E, F, E, T, E, F, E, T, E, T], [F, E, E, F, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_264 (And.intro z_267 trivial))

theorem z_270 : le (tf [F, E, E, E, E, F, T, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, F, T, E, T, E] [([F, E, E, E, E, F, E, T, F, T, E, T, E], [F, E, E, E, F, E, E, T, F, T, E, T, E]), ([F, E, E, E, E, F, T, E, F, E, T, T, E], [F, E, E, E, F, E, T, E, F, E, T, T, E]), ([F, E, E, E, E, F, T, E, F, T, E, E, T], [F, E, E, E, F, E, T, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_265 (And.intro z_268 (And.intro z_269 trivial)))

theorem z_271 : le (tf [F, E, E, E, E, F, T, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, T, F, E, E, E, T] [([F, E, E, E, E, F, T, E, F, T, E, E, T], [F, E, E, E, F, E, T, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 trivial)

theorem z_272 : le (tf [E, F, E, E, E, F, T, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, T, F, E, E, T, E] [([E, F, E, E, E, F, T, E, F, T, E, T, E], [F, E, E, E, E, F, T, E, F, T, E, T, E]), ([E, F, E, E, E, F, T, T, F, E, E, E, T], [F, E, E, E, E, F, T, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 (And.intro z_271 trivial))

theorem z_273 : le (tf [F, E, F, E, E, T, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, F, E, T, E, T] [([F, E, F, E, E, E, T, E, F, E, T, E, T], [F, F, E, E, E, E, T, E, F, E, T, E, T]), ([F, E, F, E, E, T, E, E, F, E, E, T, T], [F, F, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_148 (And.intro z_150 trivial))

theorem z_274 : le (tf [F, E, F, E, T, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, F, E, E, T, T] [([F, E, F, E, E, T, E, E, F, E, E, T, T], [F, F, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_150 trivial)

theorem z_275 : le (tf [F, E, E, F, T, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, F, E, T, E, T] [([F, E, E, F, E, T, E, E, F, E, T, E, T], [F, E, F, E, E, T, E, E, F, E, T, E, T]), ([F, E, E, F, T, E, E, E, F, E, E, T, T], [F, E, F, E, T, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_273 (And.intro z_274 trivial))

theorem z_276 : le (tf [F, E, E, E, T, F, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, F, E, T, T, E] [([F, E, E, E, E, F, T, E, F, E, T, T, E], [F, E, E, E, F, E, T, E, F, E, T, T, E]), ([F, E, E, E, T, F, E, E, F, E, T, E, T], [F, E, E, F, T, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_268 (And.intro z_275 trivial))

theorem z_277 : le (tf [F, E, E, E, T, F, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, F, T, E, E, T] [([F, E, E, E, E, F, T, E, F, T, E, E, T], [F, E, E, E, F, E, T, E, F, T, E, E, T]), ([F, E, E, E, T, F, E, E, F, E, T, E, T], [F, E, E, F, T, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 (And.intro z_275 trivial))

theorem z_278 : le (tf [E, F, E, E, T, F, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, F, T, E, T, E] [([E, F, E, E, E, F, T, E, F, T, E, T, E], [F, E, E, E, E, F, T, E, F, T, E, T, E]), ([E, F, E, E, T, F, E, E, F, E, T, T, E], [F, E, E, E, T, F, E, E, F, E, T, T, E]), ([E, F, E, E, T, F, E, E, F, T, E, E, T], [F, E, E, E, T, F, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 (And.intro z_276 (And.intro z_277 trivial)))

theorem z_279 : le (tf [E, F, E, E, T, F, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, T, F, E, E, E, T] [([E, F, E, E, E, F, T, T, F, E, E, E, T], [F, E, E, E, E, F, T, T, F, E, E, E, T]), ([E, F, E, E, T, F, E, E, F, T, E, E, T], [F, E, E, E, T, F, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_271 (And.intro z_277 trivial))

theorem z_280 : le (tf [E, E, F, E, T, F, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, T, F, E, E, T, E] [([E, E, F, E, E, F, T, T, F, E, E, T, E], [E, F, E, E, E, F, T, T, F, E, E, T, E]), ([E, E, F, E, T, F, E, E, F, T, E, T, E], [E, F, E, E, T, F, E, E, F, T, E, T, E]), ([E, E, F, E, T, F, E, T, F, E, E, E, T], [E, F, E, E, T, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_272 (And.intro z_278 (And.intro z_279 trivial)))

theorem z_281 : le (tf [F, E, F, E, E, E, E, F, T, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, F, T, E, T, T, E] [([F, E, F, E, E, E, E, F, E, T, T, T, E], [F, F, E, E, E, E, E, F, E, T, T, T, E]), ([F, E, F, E, E, E, E, F, T, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_17 (And.intro z_56 trivial))

theorem z_282 : le (tf [F, E, E, F, E, E, E, F, T, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, F, T, T, E, T, E] [([F, E, E, F, E, E, E, F, T, E, T, T, E], [F, E, F, E, E, E, E, F, T, E, T, T, E]), ([F, E, E, F, E, E, E, F, T, T, E, E, T], [F, E, F, E, E, E, E, F, T, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_281 (And.intro z_156 trivial))

theorem z_283 : le (tf [F, E, E, F, E, E, T, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, F, E, E, T, T, E] [([F, E, E, F, E, E, E, F, T, E, T, T, E], [F, E, F, E, E, E, E, F, T, E, T, T, E]), ([F, E, E, F, E, E, T, F, E, E, T, E, T], [F, E, F, E, E, E, T, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_281 (And.intro z_157 trivial))

theorem z_284 : le (tf [F, E, E, E, F, E, T, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, F, E, T, E, T, E] [([F, E, E, E, F, E, E, F, T, T, E, T, E], [F, E, E, F, E, E, E, F, T, T, E, T, E]), ([F, E, E, E, F, E, T, F, E, E, T, T, E], [F, E, E, F, E, E, T, F, E, E, T, T, E]), ([F, E, E, E, F, E, T, F, E, T, E, E, T], [F, E, E, F, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_282 (And.intro z_283 (And.intro z_158 trivial)))

theorem z_285 : le (tf [F, F, E, E, E, F, E, E, E, T, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, E, E, T, T, T, E] [([F, F, E, E, E, F, E, E, E, T, T, E, T], [F, F, E, E, F, E, E, E, E, T, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_20 trivial)

theorem z_286 : le (tf [F, F, E, E, E, E, F, E, T, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, T, E, T, T, E] [([F, F, E, E, E, E, F, E, E, T, T, T, E], [F, F, E, E, E, F, E, E, E, T, T, T, E]), ([F, F, E, E, E, E, F, E, T, E, T, E, T], [F, F, E, E, E, F, E, E, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_285 (And.intro z_22 trivial))

theorem z_287 : le (tf [F, E, F, E, E, E, F, T, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, F, T, E, E, T, T, E] [([F, E, F, E, E, E, F, E, T, E, T, T, E], [F, F, E, E, E, E, F, E, T, E, T, T, E]), ([F, E, F, E, E, E, F, T, E, E, T, E, T], [F, F, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_286 (And.intro z_24 trivial))

theorem z_288 : le (tf [F, E, E, F, E, T, F, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, F, E, E, E, T, T, E] [([F, E, E, F, E, E, F, T, E, E, T, T, E], [F, E, F, E, E, E, F, T, E, E, T, T, E]), ([F, E, E, F, E, T, F, E, E, E, T, E, T], [F, E, F, E, E, T, F, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_287 (And.intro z_163 trivial))

theorem z_289 : le (tf [F, E, E, F, T, E, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, F, E, E, T, T, E] [([F, E, E, F, E, T, E, F, E, E, T, T, E], [F, E, E, F, E, T, F, E, E, E, T, T, E]), ([F, E, E, F, T, E, E, F, E, E, T, E, T], [F, E, F, E, T, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_288 (And.intro z_166 trivial))

theorem z_290 : le (tf [F, E, E, E, T, F, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, F, E, T, E, T, E] [([F, E, E, E, E, F, T, F, E, T, E, T, E], [F, E, E, E, F, E, T, F, E, T, E, T, E]), ([F, E, E, E, T, F, E, F, E, E, T, T, E], [F, E, E, F, T, E, E, F, E, E, T, T, E]), ([F, E, E, E, T, F, E, F, E, T, E, E, T], [F, E, E, F, T, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_284 (And.intro z_289 (And.intro z_167 trivial)))

theorem z_291 : le (tf [F, E, E, F, E, T, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, F, E, T, T, E] [([F, E, E, F, E, E, T, E, F, E, T, T, E], [F, E, E, F, E, E, T, F, E, E, T, T, E]), ([F, E, E, F, E, T, E, E, F, E, T, E, T], [F, E, F, E, E, T, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_283 (And.intro z_273 trivial))

theorem z_292 : le (tf [F, F, E, T, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, E, E, E, E, F, E, E, T, T] [([F, F, E, E, T, E, E, E, F, E, E, T, T], [F, F, E, E, T, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_165 trivial)

theorem z_293 : le (tf [F, E, F, T, E, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, E, E, E, F, E, T, E, T] [([F, E, F, E, T, E, E, E, F, E, T, E, T], [F, E, F, E, T, E, E, F, E, E, T, E, T]), ([F, E, F, T, E, E, E, E, F, E, E, T, T], [F, F, E, T, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_166 (And.intro z_292 trivial))

theorem z_294 : le (tf [F, E, E, T, F, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, F, E, T, T, E] [([F, E, E, E, F, T, E, E, F, E, T, T, E], [F, E, E, F, E, T, E, E, F, E, T, T, E]), ([F, E, E, T, F, E, E, E, F, E, T, E, T], [F, E, F, T, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_291 (And.intro z_293 trivial))

theorem z_295 : le (tf [F, E, E, F, E, T, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, F, T, E, E, T] [([F, E, E, F, E, E, T, E, F, T, E, E, T], [F, E, E, F, E, E, T, F, E, T, E, E, T]), ([F, E, E, F, E, T, E, E, F, E, T, E, T], [F, E, F, E, E, T, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 (And.intro z_273 trivial))

theorem z_296 : le (tf [F, E, E, T, F, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, F, T, E, E, T] [([F, E, E, E, F, T, E, E, F, T, E, E, T], [F, E, E, F, E, T, E, E, F, T, E, E, T]), ([F, E, E, T, F, E, E, E, F, E, T, E, T], [F, E, F, T, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_295 (And.intro z_293 trivial))

theorem z_297 : le (tf [F, E, E, T, E, F, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, F, T, E, T, E] [([F, E, E, E, T, F, E, E, F, T, E, T, E], [F, E, E, E, T, F, E, F, E, T, E, T, E]), ([F, E, E, T, E, F, E, E, F, E, T, T, E], [F, E, E, T, F, E, E, E, F, E, T, T, E]), ([F, E, E, T, E, F, E, E, F, T, E, E, T], [F, E, E, T, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_290 (And.intro z_294 (And.intro z_296 trivial)))

theorem z_298 : le (tf [F, E, T, F, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, F, E, E, T, T] [([F, E, E, F, T, E, E, E, F, E, E, T, T], [F, E, F, E, T, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_274 trivial)

theorem z_299 : le (tf [F, E, T, E, F, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, F, E, T, E, T] [([F, E, E, T, F, E, E, E, F, E, T, E, T], [F, E, F, T, E, E, E, E, F, E, T, E, T]), ([F, E, T, E, F, E, E, E, F, E, E, T, T], [F, E, T, F, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_293 (And.intro z_298 trivial))

theorem z_300 : le (tf [F, E, T, E, E, F, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, F, E, T, T, E] [([F, E, E, T, E, F, E, E, F, E, T, T, E], [F, E, E, T, F, E, E, E, F, E, T, T, E]), ([F, E, T, E, E, F, E, E, F, E, T, E, T], [F, E, T, E, F, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_294 (And.intro z_299 trivial))

theorem z_301 : le (tf [F, E, T, E, E, F, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, F, T, E, E, T] [([F, E, E, T, E, F, E, E, F, T, E, E, T], [F, E, E, T, F, E, E, E, F, T, E, E, T]), ([F, E, T, E, E, F, E, E, F, E, T, E, T], [F, E, T, E, F, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_296 (And.intro z_299 trivial))

theorem z_302 : le (tf [E, F, T, E, E, F, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, F, T, E, T, E] [([E, F, E, T, E, F, E, E, F, T, E, T, E], [F, E, E, T, E, F, E, E, F, T, E, T, E]), ([E, F, T, E, E, F, E, E, F, E, T, T, E], [F, E, T, E, E, F, E, E, F, E, T, T, E]), ([E, F, T, E, E, F, E, E, F, T, E, E, T], [F, E, T, E, E, F, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_297 (And.intro z_300 (And.intro z_301 trivial)))

theorem z_303 : le (tf [F, E, E, F, E, E, T, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, T, F, E, E, E, T] [([F, E, E, F, E, E, T, E, F, T, E, E, T], [F, E, E, F, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 trivial)

theorem z_304 : le (tf [F, E, E, E, F, T, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, T, F, E, E, E, T] [([F, E, E, E, F, E, T, T, F, E, E, E, T], [F, E, E, F, E, E, T, T, F, E, E, E, T]), ([F, E, E, E, F, T, E, E, F, T, E, E, T], [F, E, E, F, E, T, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_303 (And.intro z_295 trivial))

theorem z_305 : le (tf [E, F, E, T, F, E, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, T, F, E, E, E, T] [([E, F, E, E, F, T, E, T, F, E, E, E, T], [F, E, E, E, F, T, E, T, F, E, E, E, T]), ([E, F, E, T, F, E, E, E, F, T, E, E, T], [F, E, E, T, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_304 (And.intro z_296 trivial))

theorem z_306 : le (tf [E, F, T, E, E, F, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, T, F, E, E, E, T] [([E, F, E, T, E, F, E, T, F, E, E, E, T], [E, F, E, T, F, E, E, T, F, E, E, E, T]), ([E, F, T, E, E, F, E, E, F, T, E, E, T], [F, E, T, E, E, F, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_305 (And.intro z_301 trivial))

theorem z_307 : le (tf [E, E, T, F, E, F, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, T, F, E, E, T, E] [([E, E, E, F, T, F, E, T, F, E, E, T, E], [E, E, F, E, T, F, E, T, F, E, E, T, E]), ([E, E, T, F, E, F, E, E, F, T, E, T, E], [E, F, T, E, E, F, E, E, F, T, E, T, E]), ([E, E, T, F, E, F, E, T, F, E, E, E, T], [E, F, T, E, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_280 (And.intro z_302 (And.intro z_306 trivial)))

theorem z_308 : le (tf [F, E, E, E, F, T, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, T, E, E, F, E, E, T] [([F, E, E, E, F, T, E, T, E, F, E, E, T], [F, E, E, E, F, T, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_304 trivial)

theorem z_309 : le (tf [E, F, E, T, F, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, T, E, E, F, E, E, T] [([E, F, E, E, F, T, T, E, E, F, E, E, T], [F, E, E, E, F, T, T, E, E, F, E, E, T]), ([E, F, E, T, F, E, E, T, E, F, E, E, T], [E, F, E, T, F, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_308 (And.intro z_305 trivial))

theorem z_310 : le (tf [E, F, T, E, E, F, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, T, E, E, F, E, E, T] [([E, F, E, T, E, F, T, E, E, F, E, E, T], [E, F, E, T, F, E, T, E, E, F, E, E, T]), ([E, F, T, E, E, F, E, T, E, F, E, E, T], [E, F, T, E, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_309 (And.intro z_306 trivial))

theorem z_311 : le (tf [E, E, T, F, E, F, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, T, E, E, F, E, T, E] [([E, E, E, F, T, F, T, E, E, F, E, T, E], [E, E, F, E, T, F, T, E, E, F, E, T, E]), ([E, E, T, F, E, F, E, T, E, F, E, T, E], [E, E, T, F, E, F, E, T, F, E, E, T, E]), ([E, E, T, F, E, F, T, E, E, F, E, E, T], [E, F, T, E, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_259 (And.intro z_307 (And.intro z_310 trivial)))

theorem z_312 : le (tf [E, E, T, F, E, E, T, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, F, T, E, E] [([E, E, E, F, T, E, T, F, E, F, T, E, E], [E, E, F, E, T, E, T, F, E, F, T, E, E]), ([E, E, T, F, E, E, E, F, T, F, T, E, E], [E, F, T, E, E, E, E, F, T, F, T, E, E]), ([E, E, T, F, E, E, T, F, E, F, E, T, E], [E, E, T, F, E, F, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_243 (And.intro z_255 (And.intro z_311 trivial)))

theorem z_313 : le (tf [E, E, T, F, E, E, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, T, E, F, E] [([E, E, E, F, T, E, T, F, E, T, E, F, E], [E, E, F, E, T, E, T, F, E, T, E, F, E]), ([E, E, T, F, E, E, E, F, T, T, E, F, E], [E, F, T, E, E, E, E, F, T, T, E, F, E]), ([E, E, T, F, E, E, T, F, E, E, T, F, E], [E, E, T, F, E, E, T, F, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_199 (And.intro z_217 (And.intro z_312 trivial)))

theorem z_314 : le (tf [E, E, T, F, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, T, E, E, E, F] [([E, E, E, F, T, E, T, F, T, E, E, E, F], [E, E, F, E, T, E, T, F, T, E, E, E, F]), ([E, E, T, F, E, E, T, F, E, T, E, E, F], [E, E, T, F, E, E, T, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_184 (And.intro z_313 trivial))

theorem z_315 : le (tf [E, E, T, F, E, E, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, T, E, F, E, E, F] [([E, E, E, F, T, E, T, T, E, F, E, E, F], [E, E, F, E, T, E, T, T, E, F, E, E, F]), ([E, E, T, F, E, E, T, E, T, F, E, E, F], [E, E, T, F, E, E, T, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_183 (And.intro z_314 trivial))

theorem z_316 : le (tf [F, E, E, E, T, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, E, F, E, T, F] [([F, E, E, E, T, E, T, E, E, F, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 trivial)

theorem z_317 : le (tf [E, F, E, E, T, T, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, E, F, T, E, F] [([E, F, E, E, T, E, T, E, E, F, T, E, F], [F, E, E, E, T, E, T, E, E, F, T, E, F]), ([E, F, E, E, T, T, E, E, E, F, E, T, F], [F, E, E, E, T, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_129 (And.intro z_316 trivial))

theorem z_318 : le (tf [E, E, F, E, T, T, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, T, F, E, E, F] [([E, E, F, E, T, E, T, E, T, F, E, E, F], [E, F, E, E, T, E, T, E, T, F, E, E, F]), ([E, E, F, E, T, T, E, E, E, F, T, E, F], [E, F, E, E, T, T, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_130 (And.intro z_317 trivial))

theorem z_319 : le (tf [F, E, E, T, F, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, F, T, T] [([F, E, E, E, F, T, E, E, E, E, F, T, T], [F, E, E, F, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_76 trivial)

theorem z_320 : le (tf [F, E, E, T, E, F, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, T, F, E, T] [([F, E, E, E, T, F, E, E, E, T, F, E, T], [F, E, E, F, T, E, E, E, E, T, F, E, T]), ([F, E, E, T, E, F, E, E, E, E, F, T, T], [F, E, E, T, F, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_123 (And.intro z_319 trivial))

theorem z_321 : le (tf [F, E, E, T, E, E, F, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, T, F, T, E] [([F, E, E, E, T, E, F, E, E, T, F, T, E], [F, E, E, E, T, F, E, E, E, T, F, T, E]), ([F, E, E, T, E, E, F, E, E, T, F, E, T], [F, E, E, T, E, F, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_124 (And.intro z_320 trivial))

theorem z_322 : le (tf [F, E, E, T, E, E, F, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, T, T, E, F] [([F, E, E, E, T, E, F, E, E, T, T, E, F], [F, E, E, E, T, F, E, E, E, T, T, E, F]), ([F, E, E, T, E, E, F, E, E, T, E, T, F], [F, E, E, T, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_132 (And.intro z_321 trivial))

theorem z_323 : le (tf [F, E, E, T, E, E, F, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, T, E, E, T, F] [([F, E, E, E, T, E, F, E, T, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, T, F]), ([F, E, E, T, E, E, F, E, E, T, E, T, F], [F, E, E, T, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_125 (And.intro z_321 trivial))

theorem z_324 : le (tf [F, E, E, T, E, E, E, F, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, T, E, T, E, F] [([F, E, E, E, T, E, E, F, T, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, T, E, F]), ([F, E, E, T, E, E, E, F, E, T, T, E, F], [F, E, E, T, E, E, F, E, E, T, T, E, F]), ([F, E, E, T, E, E, E, F, T, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_133 (And.intro z_322 (And.intro z_323 trivial)))

theorem z_325 : le (tf [F, E, E, T, E, E, T, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, F, E, E, E, T, F] [([F, E, E, E, T, E, T, F, E, E, E, T, F], [F, E, E, E, T, F, T, E, E, E, E, T, F]), ([F, E, E, T, E, E, E, F, T, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_173 (And.intro z_323 trivial))

theorem z_326 : le (tf [E, F, E, T, E, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, E, T, E, F] [([E, F, E, E, T, E, T, F, E, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, T, E, F]), ([E, F, E, T, E, E, E, F, T, E, T, E, F], [F, E, E, T, E, E, E, F, T, E, T, E, F]), ([E, F, E, T, E, E, T, F, E, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_174 (And.intro z_324 (And.intro z_325 trivial)))

theorem z_327 : le (tf [F, E, E, T, E, T, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, E, F, E, E, T, F] [([F, E, E, E, T, T, E, E, F, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, T, F]), ([F, E, E, T, E, E, T, E, F, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_176 (And.intro z_325 trivial))

theorem z_328 : le (tf [E, F, E, T, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, F, E, T, E, F] [([E, F, E, E, T, T, E, E, F, E, T, E, F], [F, E, E, E, T, T, E, E, F, E, T, E, F]), ([E, F, E, T, E, E, T, E, F, E, T, E, F], [E, F, E, T, E, E, T, F, E, E, T, E, F]), ([E, F, E, T, E, T, E, E, F, E, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_177 (And.intro z_326 (And.intro z_327 trivial)))

theorem z_329 : le (tf [F, E, E, E, F, E, T, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, T, E, E, E, F, T] [([F, E, E, E, F, E, T, E, T, E, E, F, T], [F, E, E, F, E, E, T, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_65 trivial)

theorem z_330 : le (tf [F, E, E, E, E, F, T, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, T, E, E, T, F, E] [([F, E, E, E, E, F, T, E, T, E, T, F, E], [F, E, E, E, F, E, T, E, T, E, T, F, E]), ([F, E, E, E, E, F, T, T, E, E, E, F, T], [F, E, E, E, F, E, T, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_187 (And.intro z_329 trivial))

theorem z_331 : le (tf [F, E, E, E, T, F, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, T, E, E, E, F, T] [([F, E, E, E, E, F, T, T, E, E, E, F, T], [F, E, E, E, F, E, T, T, E, E, E, F, T]), ([F, E, E, E, T, F, E, E, T, E, E, F, T], [F, E, E, F, T, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_329 (And.intro z_208 trivial))

theorem z_332 : le (tf [E, F, E, E, T, F, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, T, E, E, T, F, E] [([E, F, E, E, E, F, T, T, E, E, T, F, E], [F, E, E, E, E, F, T, T, E, E, T, F, E]), ([E, F, E, E, T, F, E, E, T, E, T, F, E], [E, F, E, E, T, F, E, E, T, F, T, E, E]), ([E, F, E, E, T, F, E, T, E, E, E, F, T], [F, E, E, E, T, F, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_330 (And.intro z_202 (And.intro z_331 trivial)))

theorem z_333 : le (tf [F, E, E, T, F, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, T, F, T, E] [([F, E, E, E, F, T, E, E, E, T, F, T, E], [F, E, E, F, E, T, E, E, E, T, F, T, E]), ([F, E, E, T, F, E, E, E, E, T, F, E, T], [F, E, E, T, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_42 (And.intro z_296 trivial))

theorem z_334 : le (tf [F, E, E, T, F, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, T, E, E, T, F] [([F, E, E, E, F, T, E, E, T, E, E, T, F], [F, E, E, F, E, T, E, E, T, E, E, T, F]), ([F, E, E, T, F, E, E, E, E, T, E, T, F], [F, E, E, T, F, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_44 (And.intro z_333 trivial))

theorem z_335 : le (tf [F, E, E, T, E, F, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, T, E, E, E, T, F] [([F, E, E, E, T, F, E, T, E, E, E, T, F], [F, E, E, E, T, F, E, T, E, E, F, T, E]), ([F, E, E, T, E, F, E, E, T, E, E, T, F], [F, E, E, T, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_172 (And.intro z_334 trivial))

theorem z_336 : le (tf [E, F, E, T, E, F, E, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, T, E, E, T, E, F] [([E, F, E, E, T, F, E, T, E, E, T, E, F], [E, F, E, E, T, F, E, T, E, E, T, F, E]), ([E, F, E, T, E, F, E, E, T, E, T, E, F], [E, F, E, T, E, F, E, E, T, E, T, F, E]), ([E, F, E, T, E, F, E, T, E, E, E, T, F], [F, E, E, T, E, F, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_332 (And.intro z_210 (And.intro z_335 trivial)))

theorem z_337 : le (tf [F, E, T, E, E, F, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, T, F, T, E] [([F, E, E, T, E, F, E, E, E, T, F, T, E], [F, E, E, T, F, E, E, E, E, T, F, T, E]), ([F, E, T, E, E, F, E, E, E, T, F, E, T], [F, E, T, E, E, F, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_333 (And.intro z_301 trivial))

theorem z_338 : le (tf [F, E, T, E, E, F, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, T, E, E, T, F] [([F, E, E, T, E, F, E, E, T, E, E, T, F], [F, E, E, T, F, E, E, E, T, E, E, T, F]), ([F, E, T, E, E, F, E, E, E, T, E, T, F], [F, E, T, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 (And.intro z_337 trivial))

theorem z_339 : le (tf [F, E, T, E, E, E, F, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, T, E, E, E, T, F] [([F, E, E, T, E, E, F, T, E, E, E, T, F], [F, E, E, T, E, F, E, T, E, E, E, T, F]), ([F, E, T, E, E, E, F, E, T, E, E, T, F], [F, E, T, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_335 (And.intro z_338 trivial))

theorem z_340 : le (tf [E, F, T, E, E, E, F, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, F, T, E, E, T, E, F] [([E, F, E, T, E, E, F, T, E, E, T, E, F], [E, F, E, T, E, F, E, T, E, E, T, E, F]), ([E, F, T, E, E, E, F, E, T, E, T, E, F], [E, F, T, E, E, E, F, E, T, E, T, F, E]), ([E, F, T, E, E, E, F, T, E, E, E, T, F], [F, E, T, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_336 (And.intro z_216 (And.intro z_339 trivial)))

theorem z_341 : le (tf [F, E, T, E, E, E, T, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, T, E, F, E, E, T, F] [([F, E, E, T, E, E, T, E, F, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, T, F]), ([F, E, T, E, E, E, E, T, F, E, E, T, F], [F, E, T, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_325 (And.intro z_339 trivial))

theorem z_342 : le (tf [E, F, T, E, E, E, T, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, E, F, E, T, E, F] [([E, F, E, T, E, E, T, E, F, E, T, E, F], [E, F, E, T, E, E, T, F, E, E, T, E, F]), ([E, F, T, E, E, E, E, T, F, E, T, E, F], [E, F, T, E, E, E, F, T, E, E, T, E, F]), ([E, F, T, E, E, E, T, E, F, E, E, T, F], [F, E, T, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_326 (And.intro z_340 (And.intro z_341 trivial)))

theorem z_343 : le (tf [F, E, T, E, E, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, T, E, E, E, F, E, T, F] [([F, E, E, T, E, T, E, E, E, F, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, T, F]), ([F, E, T, E, E, E, T, E, E, F, E, T, F], [F, E, T, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 (And.intro z_341 trivial))

theorem z_344 : le (tf [E, F, T, E, E, T, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, E, E, E, F, T, E, F] [([E, F, E, T, E, T, E, E, E, F, T, E, F], [E, F, E, T, E, T, E, E, F, E, T, E, F]), ([E, F, T, E, E, E, T, E, E, F, T, E, F], [E, F, T, E, E, E, T, E, F, E, T, E, F]), ([E, F, T, E, E, T, E, E, E, F, E, T, F], [F, E, T, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_328 (And.intro z_342 (And.intro z_343 trivial)))

theorem z_345 : le (tf [E, E, T, F, E, T, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, T, F, E, E, F] [([E, E, E, F, T, T, E, E, T, F, E, E, F], [E, E, F, E, T, T, E, E, T, F, E, E, F]), ([E, E, T, F, E, E, T, E, T, F, E, E, F], [E, E, T, F, E, E, T, F, T, E, E, E, F]), ([E, E, T, F, E, T, E, E, E, F, T, E, F], [E, F, T, E, E, T, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_318 (And.intro z_314 (And.intro z_344 trivial)))

theorem z_346 : le (tf [E, E, T, F, E, T, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, T, E, E, F, E, F] [([E, E, E, F, T, T, E, T, E, E, F, E, F], [E, E, F, E, T, T, E, T, E, E, F, E, F]), ([E, E, T, F, E, E, T, T, E, E, F, E, F], [E, E, T, F, E, E, T, T, E, F, E, E, F]), ([E, E, T, F, E, T, E, E, T, E, F, E, F], [E, E, T, F, E, T, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_182 (And.intro z_315 (And.intro z_345 trivial)))

theorem z_347 : le (tf [E, E, T, F, E, T, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, T, E, E, E, E, F, F] [([E, E, E, F, T, T, T, E, E, E, E, F, F], [E, E, F, E, T, T, T, E, E, E, E, F, F]), ([E, E, T, F, E, T, E, T, E, E, E, F, F], [E, E, T, F, E, T, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_181 (And.intro z_346 trivial))

theorem z_348 : le (tf [E, F, E, E, T, E, T, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, F, E, T, E, F] [([E, F, E, E, E, T, T, E, F, E, T, E, F], [F, E, E, E, E, T, T, E, F, E, T, E, F]), ([E, F, E, E, T, E, E, T, F, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, T, E, F]), ([E, F, E, E, T, E, T, E, F, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_119 (And.intro z_127 (And.intro z_128 trivial)))

theorem z_349 : le (tf [E, F, E, E, T, T, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, F, E, E, T, F] [([E, F, E, E, T, E, T, E, F, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 trivial)

theorem z_350 : le (tf [E, E, F, E, T, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, F, E, T, E, F] [([E, E, F, E, T, E, T, E, F, E, T, E, F], [E, F, E, E, T, E, T, E, F, E, T, E, F]), ([E, E, F, E, T, T, E, E, F, E, E, T, F], [E, F, E, E, T, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_348 (And.intro z_349 trivial))

theorem z_351 : le (tf [E, F, T, E, E, T, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, E, E, F, E, E, T, F] [([E, F, E, T, E, T, E, E, F, E, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, T, F]), ([E, F, T, E, E, E, T, E, F, E, E, T, F], [F, E, T, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 (And.intro z_341 trivial))

theorem z_352 : le (tf [E, E, T, F, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, F, E, T, E, F] [([E, E, E, F, T, T, E, E, F, E, T, E, F], [E, E, F, E, T, T, E, E, F, E, T, E, F]), ([E, E, T, F, E, E, T, E, F, E, T, E, F], [E, F, T, E, E, E, T, E, F, E, T, E, F]), ([E, E, T, F, E, T, E, E, F, E, E, T, F], [E, F, T, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_350 (And.intro z_342 (And.intro z_351 trivial)))

theorem z_353 : le (tf [F, E, E, E, F, E, T, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, T, T, F] [([F, E, E, E, F, E, E, T, E, E, T, T, F], [F, E, E, F, E, E, E, T, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 trivial)

theorem z_354 : le (tf [F, E, E, E, T, F, E, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, T, T, F] [([F, E, E, E, E, F, T, E, E, E, T, T, F], [F, E, E, E, F, E, T, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_353 trivial)

theorem z_355 : le (tf [F, E, E, E, T, E, F, E, E, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, E, T, F] [([F, E, E, E, E, T, F, E, E, T, E, T, F], [F, E, E, E, E, T, F, E, E, T, F, T, E]), ([F, E, E, E, T, E, F, E, E, E, T, T, F], [F, E, E, E, T, F, E, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_116 (And.intro z_354 trivial))

theorem z_356 : le (tf [F, E, E, E, T, E, E, F, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, E, T, F] [([F, E, E, E, E, T, E, F, T, E, E, T, F], [F, E, E, E, E, T, F, E, T, E, E, T, F]), ([F, E, E, E, T, E, E, F, E, T, E, T, F], [F, E, E, E, T, E, F, E, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 (And.intro z_355 trivial))

theorem z_357 : le (tf [E, F, E, E, T, E, T, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, E, T, F] [([E, F, E, E, E, T, T, F, E, E, E, T, F], [F, E, E, E, E, T, T, F, E, E, E, T, F]), ([E, F, E, E, T, E, E, F, T, E, E, T, F], [F, E, E, E, T, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_118 (And.intro z_356 trivial))

theorem z_358 : le (tf [E, E, F, E, T, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, F, E, E, E, T, F] [([E, E, F, E, T, E, T, F, E, E, E, T, F], [E, F, E, E, T, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_357 trivial)

theorem z_359 : le (tf [F, E, T, E, E, F, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, E, F, T, T] [([F, E, E, T, E, F, E, E, E, E, F, T, T], [F, E, E, T, F, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_319 trivial)

theorem z_360 : le (tf [F, E, T, E, E, E, F, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, T, F, E, T] [([F, E, E, T, E, E, F, E, E, T, F, E, T], [F, E, E, T, E, F, E, E, E, T, F, E, T]), ([F, E, T, E, E, E, F, E, E, E, F, T, T], [F, E, T, E, E, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_320 (And.intro z_359 trivial))

theorem z_361 : le (tf [F, E, T, E, E, E, E, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, T, F, T, E] [([F, E, E, T, E, E, E, F, E, T, F, T, E], [F, E, E, T, E, E, F, E, E, T, F, T, E]), ([F, E, T, E, E, E, E, F, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_321 (And.intro z_360 trivial))

theorem z_362 : le (tf [F, E, T, E, E, E, E, F, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, T, E, E, T, F] [([F, E, E, T, E, E, E, F, T, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, T, F]), ([F, E, T, E, E, E, E, F, E, T, E, T, F], [F, E, T, E, E, E, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_323 (And.intro z_361 trivial))

theorem z_363 : le (tf [E, F, T, E, E, E, T, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, F, E, E, E, T, F] [([E, F, E, T, E, E, T, F, E, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, T, F]), ([E, F, T, E, E, E, E, F, T, E, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_325 (And.intro z_362 trivial))

theorem z_364 : le (tf [E, E, T, F, E, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, F, E, E, E, T, F] [([E, E, E, F, T, T, E, F, E, E, E, T, F], [E, E, F, E, T, T, E, F, E, E, E, T, F]), ([E, E, T, F, E, E, T, F, E, E, E, T, F], [E, F, T, E, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_358 (And.intro z_363 trivial))

theorem z_365 : le (tf [E, E, T, T, F, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, F, E, E, E, T, F] [([E, E, T, E, F, T, E, F, E, E, E, T, F], [E, E, T, F, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_364 trivial)

theorem z_366 : le (tf [E, E, T, T, F, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, F, E, T, E, F] [([E, E, T, E, F, T, E, E, F, E, T, E, F], [E, E, T, F, E, T, E, E, F, E, T, E, F]), ([E, E, T, T, F, E, E, E, F, E, E, T, F], [E, E, T, T, F, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_352 (And.intro z_365 trivial))

theorem z_367 : le (tf [E, E, T, T, F, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, T, F, E, E, F] [([E, E, T, E, F, T, E, E, T, F, E, E, F], [E, E, T, F, E, T, E, E, T, F, E, E, F]), ([E, E, T, T, F, E, E, E, E, F, T, E, F], [E, E, T, T, F, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_345 (And.intro z_366 trivial))

theorem z_368 : le (tf [E, E, T, T, F, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, T, E, E, F, E, F] [([E, E, T, E, F, T, E, T, E, E, F, E, F], [E, E, T, F, E, T, E, T, E, E, F, E, F]), ([E, E, T, T, F, E, E, E, T, E, F, E, F], [E, E, T, T, F, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_346 (And.intro z_367 trivial))

theorem z_369 : le (tf [E, E, T, T, F, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, T, E, E, E, E, F, F] [([E, E, T, E, F, T, T, E, E, E, E, F, F], [E, E, T, F, E, T, T, E, E, E, E, F, F]), ([E, E, T, T, F, E, E, T, E, E, E, F, F], [E, E, T, T, F, E, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_347 (And.intro z_368 trivial))

theorem z_370 : le (tf [E, E, T, T, T, F, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, T, T, F, E, E, E, E, E, F, F] [([E, E, T, T, E, F, T, E, E, E, E, F, F], [E, E, T, T, F, E, T, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_369 trivial)

theorem z_371 : le (tf [F, E, E, E, E, T, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, T, F, E, E, E, F] [([F, E, E, E, E, T, T, E, F, T, E, E, F], [F, E, E, E, E, T, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 trivial)

theorem z_372 : le (tf [E, F, E, E, T, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, T, F, E, E, E, F] [([E, F, E, E, E, T, T, T, F, E, E, E, F], [F, E, E, E, E, T, T, T, F, E, E, E, F]), ([E, F, E, E, T, E, T, E, F, T, E, E, F], [E, F, E, E, T, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_371 (And.intro z_175 trivial))

theorem z_373 : le (tf [F, E, E, E, E, F, E, T, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, T, F, E, E] [([F, E, E, E, E, F, E, T, T, E, F, T, E], [F, E, E, E, E, F, E, T, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 trivial)

theorem z_374 : le (tf [F, E, E, E, E, T, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, T, F, E, E] [([F, E, E, E, E, E, F, T, T, T, F, E, E], [F, E, E, E, E, F, E, T, T, T, F, E, E]), ([F, E, E, E, E, T, F, E, T, E, F, T, E], [F, E, E, E, E, T, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_373 (And.intro z_228 trivial))

theorem z_375 : le (tf [F, E, E, E, E, T, T, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, T, F, E, E] [([F, E, E, E, E, T, E, F, T, T, F, E, E], [F, E, E, E, E, T, F, E, T, T, F, E, E]), ([F, E, E, E, E, T, T, F, E, E, F, T, E], [F, E, E, E, E, T, T, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_374 (And.intro z_231 trivial))

theorem z_376 : le (tf [F, E, E, E, E, T, T, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, T, E, E, F, E] [([F, E, E, E, E, T, T, F, E, T, E, F, E], [F, E, E, E, E, T, T, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_375 trivial)

theorem z_377 : le (tf [F, E, E, E, T, E, E, F, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, T, F, E, E] [([F, E, E, E, E, T, E, F, T, T, F, E, E], [F, E, E, E, E, T, F, E, T, T, F, E, E]), ([F, E, E, E, T, E, E, F, T, E, F, T, E], [F, E, E, E, T, E, E, F, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_374 (And.intro z_239 trivial))

theorem z_378 : le (tf [E, F, E, E, T, E, T, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, T, F, E, E] [([E, F, E, E, E, T, T, F, E, T, F, E, E], [F, E, E, E, E, T, T, F, E, T, F, E, E]), ([E, F, E, E, T, E, E, F, T, T, F, E, E], [F, E, E, E, T, E, E, F, T, T, F, E, E]), ([E, F, E, E, T, E, T, F, E, E, F, T, E], [E, F, E, E, T, E, T, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_375 (And.intro z_377 (And.intro z_242 trivial)))

theorem z_379 : le (tf [E, F, E, E, T, E, T, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, T, E, E, F, E] [([E, F, E, E, E, T, T, F, T, E, E, F, E], [F, E, E, E, E, T, T, F, T, E, E, F, E]), ([E, F, E, E, T, E, T, F, E, T, E, F, E], [E, F, E, E, T, E, T, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_376 (And.intro z_378 trivial))

theorem z_380 : le (tf [F, E, E, E, E, F, T, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, T, E, T, E, E, F] [([F, E, E, E, E, F, T, E, T, T, E, E, F], [F, E, E, E, E, F, T, E, T, T, E, F, E]), ([F, E, E, E, E, F, T, T, E, E, T, E, F], [F, E, E, E, E, F, T, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_188 (And.intro z_330 trivial))

theorem z_381 : le (tf [E, F, E, E, T, F, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, T, E, T, E, E, F] [([E, F, E, E, E, F, T, T, E, T, E, E, F], [F, E, E, E, E, F, T, T, E, T, E, E, F]), ([E, F, E, E, T, F, E, E, T, T, E, E, F], [E, F, E, E, T, F, E, E, T, T, E, F, E]), ([E, F, E, E, T, F, E, T, E, E, T, E, F], [E, F, E, E, T, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_380 (And.intro z_203 (And.intro z_332 trivial)))

theorem z_382 : le (tf [F, E, E, E, T, T, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, F, E, E, E, E, F, T] [([F, E, E, E, T, E, F, T, E, E, E, F, T], [F, E, E, E, T, F, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_331 trivial)

theorem z_383 : le (tf [E, F, E, E, T, T, F, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, E, T, F, E] [([E, F, E, E, T, E, F, T, E, E, T, F, E], [E, F, E, E, T, F, E, T, E, E, T, F, E]), ([E, F, E, E, T, T, F, E, E, E, E, F, T], [F, E, E, E, T, T, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_332 (And.intro z_382 trivial))

theorem z_384 : le (tf [E, F, E, E, T, T, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, T, E, E, F] [([E, F, E, E, T, E, F, T, E, T, E, E, F], [E, F, E, E, T, F, E, T, E, T, E, E, F]), ([E, F, E, E, T, T, F, E, E, E, T, E, F], [E, F, E, E, T, T, F, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_381 (And.intro z_383 trivial))

theorem z_385 : le (tf [E, F, E, E, T, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, F, T, E, E, E, F] [([E, F, E, E, T, E, T, F, T, E, E, E, F], [E, F, E, E, T, E, T, F, T, E, E, F, E]), ([E, F, E, E, T, T, E, F, E, T, E, E, F], [E, F, E, E, T, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_379 (And.intro z_384 trivial))

theorem z_386 : le (tf [E, F, E, E, T, T, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, T, E, F, E, E, F] [([E, F, E, E, T, E, T, T, E, F, E, E, F], [E, F, E, E, T, E, T, T, F, E, E, E, F]), ([E, F, E, E, T, T, E, E, T, F, E, E, F], [E, F, E, E, T, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_372 (And.intro z_385 trivial))

theorem z_387 : le (tf [E, E, F, E, T, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, T, E, E, F, E, E, F] [([E, E, F, E, T, T, E, T, E, F, E, E, F], [E, F, E, E, T, T, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_386 trivial)

theorem z_388 : le (tf [E, E, F, E, T, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, T, F, E, E, E, F] [([E, E, F, E, T, E, T, T, F, E, E, E, F], [E, F, E, E, T, E, T, T, F, E, E, E, F]), ([E, E, F, E, T, T, E, E, F, T, E, E, F], [E, F, E, E, T, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_372 (And.intro z_178 trivial))

theorem z_389 : le (tf [E, F, E, E, E, T, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, T, F, E, E, F, E] [([E, F, E, E, E, T, T, E, F, T, E, F, E], [E, F, E, E, E, T, T, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_190 trivial)

theorem z_390 : le (tf [E, E, F, E, T, E, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, T, F, E, E, F, E] [([E, E, F, E, E, T, T, T, F, E, E, F, E], [E, F, E, E, E, T, T, T, F, E, E, F, E]), ([E, E, F, E, T, E, T, E, F, T, E, F, E], [E, E, F, E, T, E, T, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_389 (And.intro z_199 trivial))

theorem z_391 : le (tf [E, E, T, F, E, E, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, T, F, E, E, F, E] [([E, E, E, F, T, E, T, T, F, E, E, F, E], [E, E, F, E, T, E, T, T, F, E, E, F, E]), ([E, E, T, F, E, E, T, E, F, T, E, F, E], [E, E, T, F, E, E, T, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_390 (And.intro z_313 trivial))

theorem z_392 : le (tf [E, F, E, E, T, T, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, F, E, E, T, E, F] [([E, F, E, E, T, E, T, F, E, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, T, E, F]), ([E, F, E, E, T, T, E, F, E, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_174 (And.intro z_176 trivial))

theorem z_393 : le (tf [E, E, F, E, T, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, F, E, T, E, E, F] [([E, E, F, E, T, E, T, F, E, T, E, E, F], [E, F, E, E, T, E, T, F, E, T, E, E, F]), ([E, E, F, E, T, T, E, F, E, E, T, E, F], [E, F, E, E, T, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_175 (And.intro z_392 trivial))

theorem z_394 : le (tf [E, F, E, E, T, E, F, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, E, T, E, F] [([E, F, E, E, E, T, F, T, E, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, T, E, F]), ([E, F, E, E, T, E, F, E, T, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, T, E, F]), ([E, F, E, E, T, E, F, T, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_133 (And.intro z_126 trivial)))

theorem z_395 : le (tf [E, F, E, E, T, T, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, E, E, T, F] [([E, F, E, E, T, E, F, T, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_126 trivial)

theorem z_396 : le (tf [E, E, F, E, T, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, E, T, E, F] [([E, E, F, E, T, E, F, T, E, E, T, E, F], [E, F, E, E, T, E, F, T, E, E, T, E, F]), ([E, E, F, E, T, T, F, E, E, E, E, T, F], [E, F, E, E, T, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_394 (And.intro z_395 trivial))

theorem z_397 : le (tf [F, E, E, E, T, T, F, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, F, E, E, F, E, E, T] [([F, E, E, E, T, E, F, T, E, F, E, E, T], [F, E, E, E, T, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_171 trivial)

theorem z_398 : le (tf [F, E, E, E, T, T, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, F, E, E, E, F, T, E] [([F, E, E, E, T, E, F, T, E, E, F, T, E], [F, E, E, E, T, F, E, T, E, E, F, T, E]), ([F, E, E, E, T, T, F, E, E, E, F, E, T], [F, E, E, E, T, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_172 (And.intro z_397 trivial))

theorem z_399 : le (tf [F, E, E, T, E, T, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, F, E, E, E, E, T, F] [([F, E, E, E, T, T, F, E, E, E, E, T, F], [F, E, E, E, T, T, F, E, E, E, F, T, E]), ([F, E, E, T, E, E, F, T, E, E, E, T, F], [F, E, E, T, E, F, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_398 (And.intro z_335 trivial))

theorem z_400 : le (tf [E, F, T, E, E, T, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, F, E, E, E, E, T, F] [([E, F, E, T, E, T, F, E, E, E, E, T, F], [F, E, E, T, E, T, F, E, E, E, E, T, F]), ([E, F, T, E, E, E, F, T, E, E, E, T, F], [F, E, T, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 (And.intro z_339 trivial))

theorem z_401 : le (tf [E, E, T, F, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, E, T, E, F] [([E, E, E, F, T, T, F, E, E, E, T, E, F], [E, E, F, E, T, T, F, E, E, E, T, E, F]), ([E, E, T, F, E, E, F, T, E, E, T, E, F], [E, F, T, E, E, E, F, T, E, E, T, E, F]), ([E, E, T, F, E, T, F, E, E, E, E, T, F], [E, F, T, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_396 (And.intro z_340 (And.intro z_400 trivial)))

theorem z_402 : le (tf [E, E, T, F, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, F, E, T, E, E, F] [([E, E, E, F, T, T, E, F, E, T, E, E, F], [E, E, F, E, T, T, E, F, E, T, E, E, F]), ([E, E, T, F, E, E, T, F, E, T, E, E, F], [E, E, T, F, E, E, T, F, E, T, E, F, E]), ([E, E, T, F, E, T, E, F, E, E, T, E, F], [E, E, T, F, E, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_393 (And.intro z_313 (And.intro z_401 trivial)))

theorem z_403 : le (tf [E, E, T, F, E, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, T, F, E, E, E, F] [([E, E, E, F, T, T, E, T, F, E, E, E, F], [E, E, F, E, T, T, E, T, F, E, E, E, F]), ([E, E, T, F, E, E, T, T, F, E, E, E, F], [E, E, T, F, E, E, T, T, F, E, E, F, E]), ([E, E, T, F, E, T, E, E, F, T, E, E, F], [E, E, T, F, E, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_388 (And.intro z_391 (And.intro z_402 trivial)))

theorem z_404 : le (tf [E, E, T, F, E, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, T, E, E, F, E, E, F] [([E, E, E, F, T, T, T, E, E, F, E, E, F], [E, E, F, E, T, T, T, E, E, F, E, E, F]), ([E, E, T, F, E, T, E, T, E, F, E, E, F], [E, E, T, F, E, T, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_387 (And.intro z_403 trivial))

theorem z_405 : le (tf [E, E, T, T, F, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, F, E, E, E, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_406 : le (tf [E, E, T, T, F, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, F, E, E, E, T, E, F] [([E, E, T, E, F, T, F, E, E, E, T, E, F], [E, E, T, F, E, T, F, E, E, E, T, E, F]), ([E, E, T, T, F, E, F, E, E, E, E, T, F], [E, E, T, T, F, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 (And.intro z_405 trivial))

theorem z_407 : le (tf [E, E, T, T, F, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, F, E, T, E, E, F] [([E, E, T, E, F, T, E, F, E, T, E, E, F], [E, E, T, F, E, T, E, F, E, T, E, E, F]), ([E, E, T, T, F, E, E, F, E, E, T, E, F], [E, E, T, T, F, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_406 trivial))

theorem z_408 : le (tf [E, E, T, T, F, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, T, F, E, E, E, F] [([E, E, T, E, F, T, E, T, F, E, E, E, F], [E, E, T, F, E, T, E, T, F, E, E, E, F]), ([E, E, T, T, F, E, E, E, F, T, E, E, F], [E, E, T, T, F, E, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_407 trivial))

theorem z_409 : le (tf [E, E, T, T, F, E, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, T, E, E, F, E, E, F] [([E, E, T, E, F, T, T, E, E, F, E, E, F], [E, E, T, F, E, T, T, E, E, F, E, E, F]), ([E, E, T, T, F, E, E, T, E, F, E, E, F], [E, E, T, T, F, E, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_404 (And.intro z_408 trivial))

theorem z_410 : le (tf [E, E, T, T, F, T, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, T, E, E, E, E, F, E, F] [([E, E, T, T, F, E, T, E, E, E, F, E, F], [E, E, T, T, F, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_409 trivial)

theorem z_411 : le (tf [E, F, E, T, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, T, E, T, E, E, F] [([E, F, E, E, T, E, F, T, E, T, E, E, F], [E, F, E, E, T, F, E, T, E, T, E, E, F]), ([E, F, E, T, E, E, F, E, T, T, E, E, F], [E, F, E, T, E, E, F, E, T, T, E, F, E]), ([E, F, E, T, E, E, F, T, E, E, T, E, F], [E, F, E, T, E, F, E, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_381 (And.intro z_211 (And.intro z_336 trivial)))

theorem z_412 : le (tf [E, F, E, T, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, F, T, E, E, F] [([E, F, E, E, T, E, T, E, F, T, E, E, F], [E, F, E, E, T, E, T, F, E, T, E, E, F]), ([E, F, E, T, E, E, E, T, F, T, E, E, F], [E, F, E, T, E, E, F, T, E, T, E, E, F]), ([E, F, E, T, E, E, T, E, F, E, T, E, F], [E, F, E, T, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_175 (And.intro z_411 (And.intro z_326 trivial)))

theorem z_413 : le (tf [E, F, E, T, E, F, E, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, E, T, T, E, E, F] [([E, F, E, E, T, F, E, E, T, T, E, E, F], [E, F, E, E, T, F, E, E, T, T, E, F, E]), ([E, F, E, T, E, F, E, E, T, E, T, E, F], [E, F, E, T, E, F, E, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_203 (And.intro z_210 trivial))

theorem z_414 : le (tf [E, F, E, T, F, E, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, T, E, T, E, F] [([E, F, E, E, F, T, E, E, T, E, T, E, F], [F, E, E, E, F, T, E, E, T, E, T, E, F]), ([E, F, E, T, F, E, E, E, E, T, T, E, F], [E, F, E, T, F, E, E, E, E, T, T, F, E]), ([E, F, E, T, F, E, E, E, T, E, E, T, F], [F, E, E, T, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_45 (And.intro z_206 (And.intro z_334 trivial)))

theorem z_415 : le (tf [F, E, F, E, T, E, F, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, F, E, E, E, E, T, T] [([F, E, F, E, E, T, F, E, E, E, E, T, T], [F, F, E, E, E, T, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_162 trivial)

theorem z_416 : le (tf [F, E, T, F, E, E, F, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, F, E, E, E, E, T, T] [([F, E, E, F, T, E, F, E, E, E, E, T, T], [F, E, F, E, T, E, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_415 trivial)

theorem z_417 : le (tf [F, E, T, F, E, E, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, F, E, E, T, E, T] [([F, E, E, F, T, E, E, F, E, E, T, E, T], [F, E, F, E, T, E, E, F, E, E, T, E, T]), ([F, E, T, F, E, E, E, F, E, E, E, T, T], [F, E, T, F, E, E, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_166 (And.intro z_416 trivial))

theorem z_418 : le (tf [F, E, T, F, E, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, F, T, E, E, T] [([F, E, E, F, T, E, E, E, F, T, E, E, T], [F, E, E, F, T, E, E, F, E, T, E, E, T]), ([F, E, T, F, E, E, E, E, F, E, T, E, T], [F, E, T, F, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_167 (And.intro z_417 trivial))

theorem z_419 : le (tf [F, T, F, E, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, E, E, E, E, E, F, T, T] [([F, E, F, T, E, E, E, E, E, E, F, T, T], [F, E, F, T, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_244 trivial)

theorem z_420 : le (tf [F, T, E, F, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, E, E, E, T, F, E, T] [([F, E, T, F, E, E, E, E, E, T, F, E, T], [F, E, T, F, E, E, E, E, F, T, E, E, T]), ([F, T, E, F, E, E, E, E, E, E, F, T, T], [F, T, F, E, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_418 (And.intro z_419 trivial))

theorem z_421 : le (tf [E, T, F, F, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, T, F, T, E] [([E, T, F, F, E, E, E, E, E, T, F, E, T], [F, T, E, F, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_420 trivial)

theorem z_422 : le (tf [E, T, F, F, E, E, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, T, T, E, F] [([E, T, F, F, E, E, E, E, E, T, E, T, F], [E, T, F, F, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_421 trivial)

theorem z_423 : le (tf [E, T, F, F, E, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, T, E, E, T, F] [([E, T, F, F, E, E, E, E, E, T, E, T, F], [E, T, F, F, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_421 trivial)

theorem z_424 : le (tf [E, T, F, E, F, E, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, E, T, E, T, E, F] [([E, E, F, T, F, E, E, E, T, E, T, E, F], [E, F, E, T, F, E, E, E, T, E, T, E, F]), ([E, T, F, E, F, E, E, E, E, T, T, E, F], [E, T, F, F, E, E, E, E, E, T, T, E, F]), ([E, T, F, E, F, E, E, E, T, E, E, T, F], [E, T, F, F, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_414 (And.intro z_422 (And.intro z_423 trivial)))

theorem z_425 : le (tf [E, T, F, E, E, F, E, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, E, T, T, E, E, F] [([E, E, F, T, E, F, E, E, T, T, E, E, F], [E, F, E, T, E, F, E, E, T, T, E, E, F]), ([E, T, F, E, E, F, E, E, T, E, T, E, F], [E, T, F, E, F, E, E, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 (And.intro z_424 trivial))

theorem z_426 : le (tf [E, F, E, T, F, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, T, E, E, E, T, F] [([E, F, E, E, F, T, E, T, E, E, E, T, F], [F, E, E, E, F, T, E, T, E, E, E, T, F]), ([E, F, E, T, F, E, E, E, T, E, E, T, F], [F, E, E, T, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_334 trivial))

theorem z_427 : le (tf [E, T, F, E, F, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, T, E, E, E, T, F] [([E, E, F, T, F, E, E, T, E, E, E, T, F], [E, F, E, T, F, E, E, T, E, E, E, T, F]), ([E, T, F, E, F, E, E, E, T, E, E, T, F], [E, T, F, F, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_426 (And.intro z_423 trivial))

theorem z_428 : le (tf [E, T, F, E, E, F, E, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, T, E, E, T, E, F] [([E, E, F, T, E, F, E, T, E, E, T, E, F], [E, F, E, T, E, F, E, T, E, E, T, E, F]), ([E, T, F, E, E, F, E, E, T, E, T, E, F], [E, T, F, E, F, E, E, E, T, E, T, E, F]), ([E, T, F, E, E, F, E, T, E, E, E, T, F], [E, T, F, E, F, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_336 (And.intro z_424 (And.intro z_427 trivial)))

theorem z_429 : le (tf [E, T, F, E, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, T, E, T, E, E, F] [([E, E, F, T, E, E, F, T, E, T, E, E, F], [E, F, E, T, E, E, F, T, E, T, E, E, F]), ([E, T, F, E, E, E, F, E, T, T, E, E, F], [E, T, F, E, E, F, E, E, T, T, E, E, F]), ([E, T, F, E, E, E, F, T, E, E, T, E, F], [E, T, F, E, E, F, E, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_411 (And.intro z_425 (And.intro z_428 trivial)))

theorem z_430 : le (tf [E, F, E, T, E, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, T, E, T, E, F] [([E, F, E, E, T, E, F, E, T, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, T, E, F]), ([E, F, E, T, E, E, F, E, E, T, T, E, F], [F, E, E, T, E, E, F, E, E, T, T, E, F]), ([E, F, E, T, E, E, F, E, T, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_133 (And.intro z_322 (And.intro z_323 trivial)))

theorem z_431 : le (tf [F, E, E, T, F, E, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, T, T, E, F] [([F, E, E, E, F, T, E, E, E, T, T, E, F], [F, E, E, F, E, T, E, E, E, T, T, E, F]), ([F, E, E, T, F, E, E, E, E, T, E, T, F], [F, E, E, T, F, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_43 (And.intro z_333 trivial))

theorem z_432 : le (tf [F, E, T, E, E, F, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, T, T, E, F] [([F, E, E, T, E, F, E, E, E, T, T, E, F], [F, E, E, T, F, E, E, E, E, T, T, E, F]), ([F, E, T, E, E, F, E, E, E, T, E, T, F], [F, E, T, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_431 (And.intro z_337 trivial))

theorem z_433 : le (tf [F, T, E, E, F, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, E, E, E, F, T, T] [([F, E, T, E, F, E, E, E, E, E, F, T, T], [F, E, T, E, F, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_250 trivial)

theorem z_434 : le (tf [F, T, E, E, E, F, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, E, T, F, E, T] [([F, E, T, E, E, F, E, E, E, T, F, E, T], [F, E, T, E, E, F, E, E, F, T, E, E, T]), ([F, T, E, E, E, F, E, E, E, E, F, T, T], [F, T, E, E, F, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_301 (And.intro z_433 trivial))

theorem z_435 : le (tf [F, T, E, E, E, E, F, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, T, F, T, E] [([F, E, T, E, E, E, F, E, E, T, F, T, E], [F, E, T, E, E, F, E, E, E, T, F, T, E]), ([F, T, E, E, E, E, F, E, E, T, F, E, T], [F, T, E, E, E, F, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_337 (And.intro z_434 trivial))

theorem z_436 : le (tf [F, T, E, E, E, E, F, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, T, T, E, F] [([F, E, T, E, E, E, F, E, E, T, T, E, F], [F, E, T, E, E, F, E, E, E, T, T, E, F]), ([F, T, E, E, E, E, F, E, E, T, E, T, F], [F, T, E, E, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 (And.intro z_435 trivial))

theorem z_437 : le (tf [F, T, E, E, E, E, F, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, T, E, E, T, F] [([F, E, T, E, E, E, F, E, T, E, E, T, F], [F, E, T, E, E, F, E, E, T, E, E, T, F]), ([F, T, E, E, E, E, F, E, E, T, E, T, F], [F, T, E, E, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_338 (And.intro z_435 trivial))

theorem z_438 : le (tf [E, T, F, E, E, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, T, E, T, E, F] [([E, E, F, T, E, E, F, E, T, E, T, E, F], [E, F, E, T, E, E, F, E, T, E, T, E, F]), ([E, T, F, E, E, E, F, E, E, T, T, E, F], [F, T, E, E, E, E, F, E, E, T, T, E, F]), ([E, T, F, E, E, E, F, E, T, E, E, T, F], [F, T, E, E, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_430 (And.intro z_436 (And.intro z_437 trivial)))

theorem z_439 : le (tf [E, F, E, T, E, F, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, T, E, E, E, E, T, F] [([E, F, E, E, T, F, T, E, E, E, E, T, F], [F, E, E, E, T, F, T, E, E, E, E, T, F]), ([E, F, E, T, E, F, E, T, E, E, E, T, F], [F, E, E, T, E, F, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_173 (And.intro z_335 trivial))

theorem z_440 : le (tf [E, T, F, E, E, F, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, T, E, E, E, E, T, F] [([E, E, F, T, E, F, T, E, E, E, E, T, F], [E, F, E, T, E, F, T, E, E, E, E, T, F]), ([E, T, F, E, E, F, E, T, E, E, E, T, F], [E, T, F, E, F, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_439 (And.intro z_427 trivial))

theorem z_441 : le (tf [E, T, F, E, E, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, F, E, E, T, E, F] [([E, E, F, T, E, E, T, F, E, E, T, E, F], [E, F, E, T, E, E, T, F, E, E, T, E, F]), ([E, T, F, E, E, E, E, F, T, E, T, E, F], [E, T, F, E, E, E, F, E, T, E, T, E, F]), ([E, T, F, E, E, E, T, F, E, E, E, T, F], [E, T, F, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_326 (And.intro z_438 (And.intro z_440 trivial)))

theorem z_442 : le (tf [E, T, F, E, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, F, T, E, E, F] [([E, E, F, T, E, E, T, E, F, T, E, E, F], [E, F, E, T, E, E, T, E, F, T, E, E, F]), ([E, T, F, E, E, E, E, T, F, T, E, E, F], [E, T, F, E, E, E, F, T, E, T, E, E, F]), ([E, T, F, E, E, E, T, E, F, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_412 (And.intro z_429 (And.intro z_441 trivial)))

theorem z_443 : le (tf [E, T, E, F, E, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, T, F, E, E, E, F] [([E, E, T, F, E, E, T, T, F, E, E, E, F], [E, E, T, F, E, E, T, T, F, E, E, F, E]), ([E, T, E, F, E, E, T, E, F, T, E, E, F], [E, T, F, E, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_391 (And.intro z_442 trivial))

theorem z_444 : le (tf [E, F, E, T, E, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, F, E, E, E, T, F] [([E, F, E, E, T, T, E, F, E, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, T, F]), ([E, F, E, T, E, E, T, F, E, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_176 (And.intro z_325 trivial))

theorem z_445 : le (tf [E, T, F, E, E, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, F, E, E, E, T, F] [([E, E, F, T, E, T, E, F, E, E, E, T, F], [E, F, E, T, E, T, E, F, E, E, E, T, F]), ([E, T, F, E, E, E, T, F, E, E, E, T, F], [E, T, F, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_444 (And.intro z_440 trivial))

theorem z_446 : le (tf [E, T, F, E, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, F, E, T, E, F] [([E, E, F, T, E, T, E, E, F, E, T, E, F], [E, F, E, T, E, T, E, E, F, E, T, E, F]), ([E, T, F, E, E, E, T, E, F, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, T, E, F]), ([E, T, F, E, E, T, E, E, F, E, E, T, F], [E, T, F, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_328 (And.intro z_441 (And.intro z_445 trivial)))

theorem z_447 : le (tf [E, T, E, F, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, F, T, E, E, F] [([E, E, T, F, E, T, E, E, F, T, E, E, F], [E, E, T, F, E, T, E, F, E, T, E, E, F]), ([E, T, E, F, E, E, T, E, F, T, E, E, F], [E, T, F, E, E, E, T, E, F, T, E, E, F]), ([E, T, E, F, E, T, E, E, F, E, T, E, F], [E, T, F, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_442 (And.intro z_446 trivial)))

theorem z_448 : le (tf [E, T, E, E, F, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, T, E, T, F, E, E, E, F] [([E, E, T, E, F, T, E, T, F, E, E, E, F], [E, E, T, F, E, T, E, T, F, E, E, E, F]), ([E, T, E, E, F, E, T, T, F, E, E, E, F], [E, T, E, F, E, E, T, T, F, E, E, E, F]), ([E, T, E, E, F, T, E, E, F, T, E, E, F], [E, T, E, F, E, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_443 (And.intro z_447 trivial)))

theorem z_449 : le (tf [E, T, E, E, F, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, T, T, E, E, F, E, E, F] [([E, E, T, E, F, T, T, E, E, F, E, E, F], [E, E, T, F, E, T, T, E, E, F, E, E, F]), ([E, T, E, E, F, T, E, T, E, F, E, E, F], [E, T, E, E, F, T, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_404 (And.intro z_448 trivial))

theorem z_450 : le (tf [F, E, E, E, F, T, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, T, E, E, F, E, T] [([F, E, E, E, F, E, T, T, E, E, F, E, T], [F, E, E, F, E, E, T, T, E, E, F, E, T]), ([F, E, E, E, F, T, E, E, T, E, F, E, T], [F, E, E, E, F, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 (And.intro z_227 trivial))

theorem z_451 : le (tf [F, E, E, E, E, T, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, T, E, E, F, T, E] [([F, E, E, E, E, T, F, E, T, E, F, T, E], [F, E, E, E, E, T, F, E, T, F, E, T, E]), ([F, E, E, E, E, T, F, T, E, E, F, E, T], [F, E, E, E, F, T, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_228 (And.intro z_450 trivial))

theorem z_452 : le (tf [E, F, E, E, E, T, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, E, T, F, E, E] [([E, F, E, E, E, T, F, E, T, T, F, E, E], [F, E, E, E, E, T, F, E, T, T, F, E, E]), ([E, F, E, E, E, T, F, T, E, E, F, T, E], [F, E, E, E, E, T, F, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_374 (And.intro z_451 trivial))

theorem z_453 : le (tf [E, F, E, E, E, T, F, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, T, E, E, F, E] [([E, F, E, E, E, T, F, T, E, T, E, F, E], [E, F, E, E, E, T, F, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_452 trivial)

theorem z_454 : le (tf [E, F, E, E, T, E, F, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, T, E, E, E, F] [([E, F, E, E, E, T, F, T, T, E, E, E, F], [E, F, E, E, E, T, F, T, T, E, E, F, E]), ([E, F, E, E, T, E, F, T, E, T, E, E, F], [E, F, E, E, T, F, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_453 (And.intro z_381 trivial))

theorem z_455 : le (tf [E, E, F, E, T, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, T, E, E, E, F] [([E, E, F, E, T, E, F, T, T, E, E, E, F], [E, F, E, E, T, E, F, T, T, E, E, E, F]), ([E, E, F, E, T, T, F, E, E, T, E, E, F], [E, F, E, E, T, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_454 (And.intro z_384 trivial))

theorem z_456 : le (tf [E, F, E, E, T, E, F, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, T, E, F, E] [([E, F, E, E, E, T, F, T, E, T, E, F, E], [E, F, E, E, E, T, F, T, E, T, F, E, E]), ([E, F, E, E, T, E, F, E, T, T, E, F, E], [E, F, E, E, T, F, E, E, T, T, E, F, E]), ([E, F, E, E, T, E, F, T, E, E, T, F, E], [E, F, E, E, T, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_452 (And.intro z_203 (And.intro z_332 trivial)))

theorem z_457 : le (tf [E, E, F, E, T, E, F, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, T, T, E, E, F, E] [([E, E, F, E, E, T, F, T, T, E, E, F, E], [E, F, E, E, E, T, F, T, T, E, E, F, E]), ([E, E, F, E, T, E, F, T, E, T, E, F, E], [E, F, E, E, T, E, F, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_453 (And.intro z_456 trivial))

theorem z_458 : le (tf [F, E, E, E, T, E, F, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, E, F, T, E] [([F, E, E, E, E, T, F, E, T, E, F, T, E], [F, E, E, E, E, T, F, E, T, F, E, T, E]), ([F, E, E, E, T, E, F, E, E, T, F, T, E], [F, E, E, E, T, F, E, E, E, T, F, T, E]), ([F, E, E, E, T, E, F, E, T, E, F, E, T], [F, E, E, E, T, E, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_228 (And.intro z_124 (And.intro z_238 trivial)))

theorem z_459 : le (tf [E, F, E, E, T, E, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, T, T, F, E, E] [([E, F, E, E, E, T, F, E, T, T, F, E, E], [F, E, E, E, E, T, F, E, T, T, F, E, E]), ([E, F, E, E, T, E, F, E, T, E, F, T, E], [F, E, E, E, T, E, F, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_374 (And.intro z_458 trivial))

theorem z_460 : le (tf [F, E, E, E, T, E, F, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, T, E, E, F, E, T] [([F, E, E, E, E, T, F, T, E, E, F, E, T], [F, E, E, E, F, T, E, T, E, E, F, E, T]), ([F, E, E, E, T, E, F, E, T, E, F, E, T], [F, E, E, E, T, E, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_450 (And.intro z_238 trivial))

theorem z_461 : le (tf [E, F, E, E, T, E, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, E, F, T, E] [([E, F, E, E, E, T, F, T, E, E, F, T, E], [F, E, E, E, E, T, F, T, E, E, F, T, E]), ([E, F, E, E, T, E, F, E, T, E, F, T, E], [F, E, E, E, T, E, F, E, T, E, F, T, E]), ([E, F, E, E, T, E, F, T, E, E, F, E, T], [F, E, E, E, T, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_451 (And.intro z_458 (And.intro z_460 trivial)))

theorem z_462 : le (tf [E, E, F, E, T, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, T, E, T, F, E, E] [([E, E, F, E, E, T, F, T, E, T, F, E, E], [E, F, E, E, E, T, F, T, E, T, F, E, E]), ([E, E, F, E, T, E, F, E, T, T, F, E, E], [E, F, E, E, T, E, F, E, T, T, F, E, E]), ([E, E, F, E, T, E, F, T, E, E, F, T, E], [E, F, E, E, T, E, F, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_452 (And.intro z_459 (And.intro z_461 trivial)))

theorem z_463 : le (tf [F, E, E, F, E, E, E, T, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, T, T, F, E, E] [([F, E, E, F, E, E, E, T, T, E, F, T, E], [F, E, F, E, E, E, E, T, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_29 trivial)

theorem z_464 : le (tf [F, E, E, E, F, E, T, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, T, T, F, E, E] [([F, E, E, E, F, E, E, T, T, T, F, E, E], [F, E, E, F, E, E, E, T, T, T, F, E, E]), ([F, E, E, E, F, E, T, E, T, E, F, T, E], [F, E, E, F, E, E, T, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_463 (And.intro z_136 trivial))

theorem z_465 : le (tf [F, E, E, E, T, F, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, T, T, F, E, E] [([F, E, E, E, E, F, T, E, T, T, F, E, E], [F, E, E, E, F, E, T, E, T, T, F, E, E]), ([F, E, E, E, T, F, E, E, T, E, F, T, E], [F, E, E, E, T, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_464 (And.intro z_169 trivial))

theorem z_466 : le (tf [F, E, E, T, E, E, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, T, T, F, E, E] [([F, E, E, E, T, E, F, E, T, T, F, E, E], [F, E, E, E, T, F, E, E, T, T, F, E, E]), ([F, E, E, T, E, E, F, E, T, E, F, T, E], [F, E, E, T, E, E, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_465 (And.intro z_248 trivial))

theorem z_467 : le (tf [F, E, T, E, E, E, F, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, T, E, F, T, E] [([F, E, E, T, E, E, F, E, T, E, F, T, E], [F, E, E, T, E, E, F, E, T, F, E, T, E]), ([F, E, T, E, E, E, F, E, E, T, F, T, E], [F, E, T, E, E, F, E, E, E, T, F, T, E]), ([F, E, T, E, E, E, F, E, T, E, F, E, T], [F, E, T, E, E, E, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 (And.intro z_337 (And.intro z_253 trivial)))

theorem z_468 : le (tf [E, F, T, E, E, E, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, F, E, T, T, F, E, E] [([E, F, E, T, E, E, F, E, T, T, F, E, E], [F, E, E, T, E, E, F, E, T, T, F, E, E]), ([E, F, T, E, E, E, F, E, T, E, F, T, E], [F, E, T, E, E, E, F, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_466 (And.intro z_467 trivial))

theorem z_469 : le (tf [F, E, E, T, E, F, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, T, E, E, F, E, T] [([F, E, E, E, T, F, E, T, E, E, F, E, T], [F, E, E, E, T, F, E, T, E, F, E, E, T]), ([F, E, E, T, E, F, E, E, T, E, F, E, T], [F, E, E, T, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_171 (And.intro z_247 trivial))

theorem z_470 : le (tf [F, E, E, T, E, E, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, T, E, E, F, T, E] [([F, E, E, E, T, E, F, T, E, E, F, T, E], [F, E, E, E, T, F, E, T, E, E, F, T, E]), ([F, E, E, T, E, E, F, E, T, E, F, T, E], [F, E, E, T, E, E, F, E, T, F, E, T, E]), ([F, E, E, T, E, E, F, T, E, E, F, E, T], [F, E, E, T, E, F, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_172 (And.intro z_248 (And.intro z_469 trivial)))

theorem z_471 : le (tf [F, E, T, E, E, E, F, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, T, E, E, F, E, T] [([F, E, E, T, E, E, F, T, E, E, F, E, T], [F, E, E, T, E, F, E, T, E, E, F, E, T]), ([F, E, T, E, E, E, F, E, T, E, F, E, T], [F, E, T, E, E, E, F, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_469 (And.intro z_253 trivial))

theorem z_472 : le (tf [E, F, T, E, E, E, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, F, T, E, E, F, T, E] [([E, F, E, T, E, E, F, T, E, E, F, T, E], [F, E, E, T, E, E, F, T, E, E, F, T, E]), ([E, F, T, E, E, E, F, E, T, E, F, T, E], [F, E, T, E, E, E, F, E, T, E, F, T, E]), ([E, F, T, E, E, E, F, T, E, E, F, E, T], [F, E, T, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_470 (And.intro z_467 (And.intro z_471 trivial)))

theorem z_473 : le (tf [E, E, T, F, E, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, T, E, T, F, E, E] [([E, E, E, F, T, E, F, T, E, T, F, E, E], [E, E, F, E, T, E, F, T, E, T, F, E, E]), ([E, E, T, F, E, E, F, E, T, T, F, E, E], [E, F, T, E, E, E, F, E, T, T, F, E, E]), ([E, E, T, F, E, E, F, T, E, E, F, T, E], [E, F, T, E, E, E, F, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_462 (And.intro z_468 (And.intro z_472 trivial)))

theorem z_474 : le (tf [E, E, T, F, E, E, F, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, T, T, E, E, F, E] [([E, E, E, F, T, E, F, T, T, E, E, F, E], [E, E, F, E, T, E, F, T, T, E, E, F, E]), ([E, E, T, F, E, E, F, T, E, T, E, F, E], [E, E, T, F, E, E, F, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_457 (And.intro z_473 trivial))

theorem z_475 : le (tf [E, E, F, E, T, T, F, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, T, E, F, E] [([E, E, F, E, T, E, F, T, E, T, E, F, E], [E, F, E, E, T, E, F, T, E, T, E, F, E]), ([E, E, F, E, T, T, F, E, E, E, T, F, E], [E, F, E, E, T, T, F, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_456 (And.intro z_383 trivial))

theorem z_476 : le (tf [F, E, E, E, E, F, E, T, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, F, T, T, E, E] [([F, E, E, E, E, F, E, T, F, T, E, T, E], [F, E, E, E, F, E, E, T, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_265 trivial)

theorem z_477 : le (tf [F, E, E, E, F, T, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, F, T, E, T, E] [([F, E, E, E, F, E, T, E, F, T, E, T, E], [F, E, E, E, F, E, T, F, E, T, E, T, E]), ([F, E, E, E, F, T, E, E, F, E, T, T, E], [F, E, E, F, E, T, E, E, F, E, T, T, E]), ([F, E, E, E, F, T, E, E, F, T, E, E, T], [F, E, E, F, E, T, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_284 (And.intro z_291 (And.intro z_295 trivial)))

theorem z_478 : le (tf [F, E, E, E, E, T, F, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, F, T, T, E, E] [([F, E, E, E, E, E, F, T, F, T, T, E, E], [F, E, E, E, E, F, E, T, F, T, T, E, E]), ([F, E, E, E, E, T, F, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_476 (And.intro z_477 trivial))

theorem z_479 : le (tf [F, E, E, E, E, T, F, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, T, F, E, E, T, E] [([F, E, E, E, E, T, F, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, F, T, E, T, E]), ([F, E, E, E, E, T, F, T, F, E, E, E, T], [F, E, E, E, F, T, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_477 (And.intro z_304 trivial))

theorem z_480 : le (tf [E, F, E, E, E, T, F, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, F, E, T, E, E] [([E, F, E, E, E, T, F, E, F, T, T, E, E], [F, E, E, E, E, T, F, E, F, T, T, E, E]), ([E, F, E, E, E, T, F, T, F, E, E, T, E], [F, E, E, E, E, T, F, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 (And.intro z_479 trivial))

theorem z_481 : le (tf [E, F, E, E, T, E, F, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, F, T, E, E] [([E, F, E, E, E, T, F, T, E, F, T, E, E], [E, F, E, E, E, T, F, T, F, E, T, E, E]), ([E, F, E, E, T, E, F, E, T, F, T, E, E], [E, F, E, E, T, F, E, E, T, F, T, E, E]), ([E, F, E, E, T, E, F, T, E, F, E, T, E], [E, F, E, E, T, F, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_480 (And.intro z_202 (And.intro z_257 trivial)))

theorem z_482 : le (tf [E, F, E, E, T, T, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, F, E, T, E] [([E, F, E, E, T, E, F, T, E, F, E, T, E], [E, F, E, E, T, F, E, T, E, F, E, T, E]), ([E, F, E, E, T, T, F, E, E, F, E, E, T], [F, E, E, E, T, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_257 (And.intro z_397 trivial))

theorem z_483 : le (tf [E, E, F, E, T, T, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, F, T, E, E] [([E, E, F, E, T, E, F, T, E, F, T, E, E], [E, F, E, E, T, E, F, T, E, F, T, E, E]), ([E, E, F, E, T, T, F, E, E, F, E, T, E], [E, F, E, E, T, T, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_481 (And.intro z_482 trivial))

theorem z_484 : le (tf [E, F, E, E, T, E, F, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, F, T, T, E, E] [([E, F, E, E, E, T, F, E, F, T, T, E, E], [F, E, E, E, E, T, F, E, F, T, T, E, E]), ([E, F, E, E, T, E, F, E, F, T, E, T, E], [E, F, E, E, T, F, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 (And.intro z_278 trivial))

theorem z_485 : le (tf [E, E, F, E, T, E, F, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, T, F, E, T, E, E] [([E, E, F, E, E, T, F, T, F, E, T, E, E], [E, F, E, E, E, T, F, T, F, E, T, E, E]), ([E, E, F, E, T, E, F, E, F, T, T, E, E], [E, F, E, E, T, E, F, E, F, T, T, E, E]), ([E, E, F, E, T, E, F, T, F, E, E, T, E], [E, E, F, E, T, F, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_480 (And.intro z_484 (And.intro z_280 trivial)))

theorem z_486 : le (tf [F, E, E, F, E, E, E, T, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, F, T, T, E, E] [([F, E, E, F, E, E, E, T, F, T, E, T, E], [F, E, F, E, E, E, E, T, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_27 trivial)

theorem z_487 : le (tf [F, E, E, E, F, E, T, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, F, T, T, E, E] [([F, E, E, E, F, E, E, T, F, T, T, E, E], [F, E, E, F, E, E, E, T, F, T, T, E, E]), ([F, E, E, E, F, E, T, E, F, T, E, T, E], [F, E, E, E, F, E, T, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_486 (And.intro z_284 trivial))

theorem z_488 : le (tf [F, E, E, E, T, F, E, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, F, T, T, E, E] [([F, E, E, E, E, F, T, E, F, T, T, E, E], [F, E, E, E, F, E, T, E, F, T, T, E, E]), ([F, E, E, E, T, F, E, E, F, T, E, T, E], [F, E, E, E, T, F, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_487 (And.intro z_290 trivial))

theorem z_489 : le (tf [F, E, E, T, E, E, F, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, F, T, T, E, E] [([F, E, E, E, T, E, F, E, F, T, T, E, E], [F, E, E, E, T, F, E, E, F, T, T, E, E]), ([F, E, E, T, E, E, F, E, F, T, E, T, E], [F, E, E, T, E, F, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_488 (And.intro z_297 trivial))

theorem z_490 : le (tf [E, F, T, E, E, E, F, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, F, E, F, T, T, E, E] [([E, F, E, T, E, E, F, E, F, T, T, E, E], [F, E, E, T, E, E, F, E, F, T, T, E, E]), ([E, F, T, E, E, E, F, E, F, T, E, T, E], [E, F, T, E, E, F, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_489 (And.intro z_302 trivial))

theorem z_491 : le (tf [E, E, T, F, E, E, F, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, T, F, E, T, E, E] [([E, E, E, F, T, E, F, T, F, E, T, E, E], [E, E, F, E, T, E, F, T, F, E, T, E, E]), ([E, E, T, F, E, E, F, E, F, T, T, E, E], [E, F, T, E, E, E, F, E, F, T, T, E, E]), ([E, E, T, F, E, E, F, T, F, E, E, T, E], [E, E, T, F, E, F, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_485 (And.intro z_490 (And.intro z_307 trivial)))

theorem z_492 : le (tf [E, F, E, E, T, T, F, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, F, E, E, E, T] [([E, F, E, E, T, E, F, T, F, E, E, E, T], [E, F, E, E, T, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_279 trivial)

theorem z_493 : le (tf [E, E, F, E, T, T, F, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, F, E, E, T, E] [([E, E, F, E, T, E, F, T, F, E, E, T, E], [E, E, F, E, T, F, E, T, F, E, E, T, E]), ([E, E, F, E, T, T, F, E, F, E, E, E, T], [E, F, E, E, T, T, F, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_280 (And.intro z_492 trivial))

theorem z_494 : le (tf [F, E, E, E, T, T, F, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, F, F, E, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_495 : le (tf [E, F, E, T, E, T, F, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, F, F, E, E, E, E, T] [([E, F, E, E, T, T, F, F, E, E, E, E, T], [F, E, E, E, T, T, F, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_494 trivial)

theorem z_496 : le (tf [E, F, T, E, E, T, F, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, F, E, F, E, E, E, T] [([E, F, E, T, E, T, F, E, F, E, E, E, T], [E, F, E, T, E, T, F, F, E, E, E, E, T]), ([E, F, T, E, E, E, F, T, F, E, E, E, T], [E, F, T, E, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_495 (And.intro z_306 trivial))

theorem z_497 : le (tf [E, E, T, F, E, T, F, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, F, E, E, T, E] [([E, E, E, F, T, T, F, E, F, E, E, T, E], [E, E, F, E, T, T, F, E, F, E, E, T, E]), ([E, E, T, F, E, E, F, T, F, E, E, T, E], [E, E, T, F, E, F, E, T, F, E, E, T, E]), ([E, E, T, F, E, T, F, E, F, E, E, E, T], [E, F, T, E, E, T, F, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_493 (And.intro z_307 (And.intro z_496 trivial)))

theorem z_498 : le (tf [E, E, T, F, E, T, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, F, T, E, E] [([E, E, E, F, T, T, F, E, E, F, T, E, E], [E, E, F, E, T, T, F, E, E, F, T, E, E]), ([E, E, T, F, E, E, F, T, E, F, T, E, E], [E, E, T, F, E, E, F, T, F, E, T, E, E]), ([E, E, T, F, E, T, F, E, E, F, E, T, E], [E, E, T, F, E, T, F, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_483 (And.intro z_491 (And.intro z_497 trivial)))

theorem z_499 : le (tf [E, E, T, F, E, T, F, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, T, E, F, E] [([E, E, E, F, T, T, F, E, E, T, E, F, E], [E, E, F, E, T, T, F, E, E, T, E, F, E]), ([E, E, T, F, E, E, F, T, E, T, E, F, E], [E, E, T, F, E, E, F, T, E, T, F, E, E]), ([E, E, T, F, E, T, F, E, E, E, T, F, E], [E, E, T, F, E, T, F, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_475 (And.intro z_473 (And.intro z_498 trivial)))

theorem z_500 : le (tf [E, E, T, F, E, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, T, E, E, E, F] [([E, E, E, F, T, T, F, E, T, E, E, E, F], [E, E, F, E, T, T, F, E, T, E, E, E, F]), ([E, E, T, F, E, E, F, T, T, E, E, E, F], [E, E, T, F, E, E, F, T, T, E, E, F, E]), ([E, E, T, F, E, T, F, E, E, T, E, E, F], [E, E, T, F, E, T, F, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_455 (And.intro z_474 (And.intro z_499 trivial)))

theorem z_501 : le (tf [E, E, T, T, F, F, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, E, T, T, F, F, E, E, E, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_502 : le (tf [E, E, T, T, F, F, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, T, F, F, E, E, E, E, T, F, E] [([E, E, T, T, F, F, E, E, E, E, E, F, T], [E, E, T, T, F, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_501 trivial)

theorem z_503 : le (tf [E, E, T, T, F, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, F, E, E, E, T, E, E, F] [([E, E, T, T, F, F, E, E, E, E, T, E, F], [E, E, T, T, F, F, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_502 trivial)

theorem z_504 : le (tf [E, E, T, T, F, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, F, E, T, E, E, E, F] [([E, E, T, E, F, T, F, E, T, E, E, E, F], [E, E, T, F, E, T, F, E, T, E, E, E, F]), ([E, E, T, T, F, E, F, E, E, T, E, E, F], [E, E, T, T, F, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_500 (And.intro z_503 trivial))

theorem z_505 : le (tf [E, T, E, F, E, E, F, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, F, T, T, E, E, E, F] [([E, E, T, F, E, E, F, T, T, E, E, E, F], [E, E, T, F, E, E, F, T, T, E, E, F, E]), ([E, T, E, F, E, E, F, T, E, T, E, E, F], [E, T, F, E, E, E, F, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_474 (And.intro z_429 trivial))

theorem z_506 : le (tf [E, F, E, T, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, F, E, E, E, T, E, F] [([E, F, E, E, T, T, F, E, E, E, T, E, F], [E, F, E, E, T, T, F, E, E, E, T, F, E]), ([E, F, E, T, E, E, F, T, E, E, T, E, F], [E, F, E, T, E, F, E, T, E, E, T, E, F]), ([E, F, E, T, E, T, F, E, E, E, E, T, F], [F, E, E, T, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_383 (And.intro z_336 (And.intro z_399 trivial)))

theorem z_507 : le (tf [F, E, E, E, F, E, T, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, T, F, E, E, T, E] [([F, E, E, E, F, E, T, E, F, T, E, T, E], [F, E, E, E, F, E, T, F, E, T, E, T, E]), ([F, E, E, E, F, E, T, T, F, E, E, E, T], [F, E, E, F, E, E, T, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_284 (And.intro z_303 trivial))

theorem z_508 : le (tf [E, F, E, E, F, T, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, E, T, F, E, E, T, E] [([E, F, E, E, F, E, T, T, F, E, E, T, E], [F, E, E, E, F, E, T, T, F, E, E, T, E]), ([E, F, E, E, F, T, E, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, F, T, E, T, E]), ([E, F, E, E, F, T, E, T, F, E, E, E, T], [F, E, E, E, F, T, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_507 (And.intro z_477 (And.intro z_304 trivial)))

theorem z_509 : le (tf [E, F, E, E, F, T, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, T, E, E, F, E, T, E] [([E, F, E, E, F, T, E, T, E, F, E, T, E], [E, F, E, E, F, T, E, T, F, E, E, T, E]), ([E, F, E, E, F, T, T, E, E, F, E, E, T], [F, E, E, E, F, T, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_508 (And.intro z_308 trivial))

theorem z_510 : le (tf [E, F, E, T, F, E, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, F, T, E, T, E] [([E, F, E, E, F, T, E, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, F, T, E, T, E]), ([E, F, E, T, F, E, E, E, F, E, T, T, E], [F, E, E, T, F, E, E, E, F, E, T, T, E]), ([E, F, E, T, F, E, E, E, F, T, E, E, T], [F, E, E, T, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_477 (And.intro z_294 (And.intro z_296 trivial)))

theorem z_511 : le (tf [E, E, F, T, F, E, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, F, E, E, T, F, E, E, T, E] [([E, E, F, E, F, T, E, T, F, E, E, T, E], [E, F, E, E, F, T, E, T, F, E, E, T, E]), ([E, E, F, T, F, E, E, E, F, T, E, T, E], [E, F, E, T, F, E, E, E, F, T, E, T, E]), ([E, E, F, T, F, E, E, T, F, E, E, E, T], [E, F, E, T, F, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_508 (And.intro z_510 (And.intro z_305 trivial)))

theorem z_512 : le (tf [E, E, F, T, F, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, F, E, T, E, E, F, E, T, E] [([E, E, F, E, F, T, T, E, E, F, E, T, E], [E, F, E, E, F, T, T, E, E, F, E, T, E]), ([E, E, F, T, F, E, E, T, E, F, E, T, E], [E, E, F, T, F, E, E, T, F, E, E, T, E]), ([E, E, F, T, F, E, T, E, E, F, E, E, T], [E, F, E, T, F, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_509 (And.intro z_511 (And.intro z_309 trivial)))

theorem z_513 : le (tf [E, F, E, T, F, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, T, E, E, E, E, F, E, T] [([E, F, E, T, F, E, T, E, E, E, F, E, T], [E, F, E, T, F, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_309 trivial)

theorem z_514 : le (tf [E, E, F, T, F, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, F, T, E, E, E, E, F, T, E] [([E, E, F, T, F, E, T, E, E, E, F, T, E], [E, E, F, T, F, E, T, E, E, F, E, T, E]), ([E, E, F, T, F, T, E, E, E, E, F, E, T], [E, F, E, T, F, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_512 (And.intro z_513 trivial))

theorem z_515 : le (tf [F, E, T, F, E, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, F, E, T, T, E] [([F, E, E, F, T, E, E, E, F, E, T, T, E], [F, E, E, F, T, E, E, F, E, E, T, T, E]), ([F, E, T, F, E, E, E, E, F, E, T, E, T], [F, E, T, F, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_289 (And.intro z_417 trivial))

theorem z_516 : le (tf [F, T, F, E, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, E, E, E, F, E, E, T, T] [([F, E, F, T, E, E, E, E, F, E, E, T, T], [F, F, E, T, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_292 trivial)

theorem z_517 : le (tf [F, T, F, E, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, E, E, E, E, F, T, E, T] [([F, E, F, T, E, E, E, E, E, F, T, E, T], [F, E, F, T, E, E, E, E, F, E, T, E, T]), ([F, T, F, E, E, E, E, E, E, F, E, T, T], [F, T, F, E, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_293 (And.intro z_516 trivial))

theorem z_518 : le (tf [F, T, E, F, E, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, E, E, E, F, T, T, E] [([F, E, T, F, E, E, E, E, E, F, T, T, E], [F, E, T, F, E, E, E, E, F, E, T, T, E]), ([F, T, E, F, E, E, E, E, E, F, T, E, T], [F, T, F, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_515 (And.intro z_517 trivial))

theorem z_519 : le (tf [F, E, T, F, F, E, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, F, E, E, E, E, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_520 : le (tf [F, T, E, F, E, F, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, T, E, F, E, F, E, E, E, E, E, T, T] [([F, E, T, F, E, F, E, E, E, E, E, T, T], [F, E, T, F, F, E, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_519 trivial)

theorem z_521 : le (tf [E, T, F, F, E, F, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, F, E, E, E, E, T, E, T] [([E, T, F, F, E, F, E, E, E, E, E, T, T], [F, T, E, F, E, F, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_520 trivial)

theorem z_522 : le (tf [E, T, F, F, E, E, F, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, F, E, E, T, E, E, T] [([E, T, F, F, E, E, F, E, E, E, T, E, T], [E, T, F, F, E, F, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_521 trivial)

theorem z_523 : le (tf [E, T, F, F, E, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, F, T, E, E, E, T] [([E, T, F, F, E, E, E, F, E, T, E, E, T], [E, T, F, F, E, E, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_522 trivial)

theorem z_524 : le (tf [E, T, F, F, E, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, T, F, E, T, E] [([E, T, F, F, E, E, E, E, E, F, T, T, E], [F, T, E, F, E, E, E, E, E, F, T, T, E]), ([E, T, F, F, E, E, E, E, T, F, E, E, T], [E, T, F, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_518 (And.intro z_523 trivial))

theorem z_525 : le (tf [E, T, F, F, E, E, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, T, E, F, E, E, T] [([E, T, F, F, E, E, E, E, T, F, E, E, T], [E, T, F, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_523 trivial)

theorem z_526 : le (tf [E, T, F, F, E, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, T, E, E, F, T, E] [([E, T, F, F, E, E, E, E, T, E, F, T, E], [E, T, F, F, E, E, E, E, T, F, E, T, E]), ([E, T, F, F, E, E, E, T, E, E, F, E, T], [E, T, F, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_524 (And.intro z_525 trivial))

theorem z_527 : le (tf [E, T, F, F, E, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, T, E, E, E, E, T, F] [([E, T, F, F, E, E, E, T, E, E, E, T, F], [E, T, F, F, E, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_526 trivial)

theorem z_528 : le (tf [E, T, F, E, F, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, F, T, E, E, E, E, E, T, F] [([E, E, F, T, F, T, E, E, E, E, E, T, F], [E, E, F, T, F, T, E, E, E, E, F, T, E]), ([E, T, F, E, F, E, T, E, E, E, E, T, F], [E, T, F, F, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_514 (And.intro z_527 trivial))

theorem z_529 : le (tf [E, T, F, E, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, F, E, E, E, T, E, F] [([E, E, F, T, E, T, F, E, E, E, T, E, F], [E, F, E, T, E, T, F, E, E, E, T, E, F]), ([E, T, F, E, E, E, F, T, E, E, T, E, F], [E, T, F, E, E, F, E, T, E, E, T, E, F]), ([E, T, F, E, E, T, F, E, E, E, E, T, F], [E, T, F, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_506 (And.intro z_428 (And.intro z_528 trivial)))

theorem z_530 : le (tf [E, T, E, F, E, T, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, F, E, E, T, E, E, F] [([E, E, T, F, E, T, F, E, E, T, E, E, F], [E, E, T, F, E, T, F, E, E, T, E, F, E]), ([E, T, E, F, E, E, F, T, E, T, E, E, F], [E, T, F, E, E, E, F, T, E, T, E, E, F]), ([E, T, E, F, E, T, F, E, E, E, T, E, F], [E, T, F, E, E, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_499 (And.intro z_429 (And.intro z_529 trivial)))

theorem z_531 : le (tf [E, T, E, E, F, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, T, F, E, T, E, E, E, F] [([E, E, T, E, F, T, F, E, T, E, E, E, F], [E, E, T, F, E, T, F, E, T, E, E, E, F]), ([E, T, E, E, F, E, F, T, T, E, E, E, F], [E, T, E, F, E, E, F, T, T, E, E, E, F]), ([E, T, E, E, F, T, F, E, E, T, E, E, F], [E, T, E, F, E, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_500 (And.intro z_505 (And.intro z_530 trivial)))

theorem z_532 : le (tf [E, F, E, T, T, F, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, T, F, E, E, E, F, E, E, T] [([E, F, E, T, E, F, T, E, E, F, E, E, T], [E, F, E, T, F, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_309 trivial)

theorem z_533 : le (tf [E, E, F, T, T, F, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, T, F, E, E, E, F, E, T, E] [([E, E, F, T, E, F, T, E, E, F, E, T, E], [E, E, F, T, F, E, T, E, E, F, E, T, E]), ([E, E, F, T, T, F, E, E, E, F, E, E, T], [E, F, E, T, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_512 (And.intro z_532 trivial))

theorem z_534 : le (tf [E, T, F, F, E, E, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, T, E, E, E, F, E, T] [([E, T, F, F, E, E, E, T, E, E, F, E, T], [E, T, F, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_525 trivial)

theorem z_535 : le (tf [E, T, F, E, F, E, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, T, E, E, E, F, T, E] [([E, E, F, T, F, E, T, E, E, E, F, T, E], [E, E, F, T, F, E, T, E, E, F, E, T, E]), ([E, T, F, E, F, E, E, T, E, E, F, T, E], [E, T, F, F, E, E, E, T, E, E, F, T, E]), ([E, T, F, E, F, E, T, E, E, E, F, E, T], [E, T, F, F, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_512 (And.intro z_526 (And.intro z_534 trivial)))

theorem z_536 : le (tf [E, T, F, E, F, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, T, E, E, F, E, E, T] [([E, E, F, T, F, E, T, E, E, F, E, E, T], [E, F, E, T, F, E, T, E, E, F, E, E, T]), ([E, T, F, E, F, E, E, T, E, F, E, E, T], [E, T, F, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_309 (And.intro z_525 trivial))

theorem z_537 : le (tf [E, T, F, E, T, F, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, T, F, E, E, E, F, E, E, T] [([E, E, F, T, T, F, E, E, E, F, E, E, T], [E, F, E, T, T, F, E, E, E, F, E, E, T]), ([E, T, F, E, E, F, T, E, E, F, E, E, T], [E, T, F, E, F, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_532 (And.intro z_536 trivial))

theorem z_538 : le (tf [E, T, F, E, T, F, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, E, T, F, E, E, E, E, F, T, E] [([E, E, F, T, T, F, E, E, E, E, F, T, E], [E, E, F, T, T, F, E, E, E, F, E, T, E]), ([E, T, F, E, E, F, T, E, E, E, F, T, E], [E, T, F, E, F, E, T, E, E, E, F, T, E]), ([E, T, F, E, T, F, E, E, E, E, F, E, T], [E, T, F, E, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_533 (And.intro z_535 (And.intro z_537 trivial)))

theorem z_539 : le (tf [E, T, F, T, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, F, E, E, E, E, E, T, F] [([E, T, F, E, T, F, E, E, E, E, E, T, F], [E, T, F, E, T, F, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_538 trivial)

theorem z_540 : le (tf [E, T, E, T, F, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, F, E, E, E, E, T, E, F] [([E, E, T, T, F, F, E, E, E, E, T, E, F], [E, E, T, T, F, F, E, E, E, E, T, F, E]), ([E, T, E, T, F, F, E, E, E, E, E, T, F], [E, T, F, T, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_502 (And.intro z_539 trivial))

theorem z_541 : le (tf [E, T, E, T, F, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, F, E, E, T, E, E, F] [([E, E, T, T, F, E, F, E, E, T, E, E, F], [E, E, T, T, F, F, E, E, E, T, E, E, F]), ([E, T, E, E, F, T, F, E, E, T, E, E, F], [E, T, E, F, E, T, F, E, E, T, E, E, F]), ([E, T, E, T, F, E, F, E, E, E, T, E, F], [E, T, E, T, F, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_503 (And.intro z_530 (And.intro z_540 trivial)))

theorem z_542 : le (tf [E, T, E, T, F, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, F, T, E, E, E, F] [([E, E, T, T, F, E, E, F, T, E, E, E, F], [E, E, T, T, F, E, F, E, T, E, E, E, F]), ([E, T, E, E, F, T, E, F, T, E, E, E, F], [E, T, E, E, F, T, F, E, T, E, E, E, F]), ([E, T, E, T, F, E, E, F, E, T, E, E, F], [E, T, E, T, F, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_504 (And.intro z_531 (And.intro z_541 trivial)))

theorem z_543 : le (tf [E, T, E, T, F, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, T, E, F, E, E, F] [([E, E, T, T, F, E, E, T, E, F, E, E, F], [E, E, T, T, F, E, E, T, F, E, E, E, F]), ([E, T, E, E, F, T, E, T, E, F, E, E, F], [E, T, E, E, F, T, E, T, F, E, E, E, F]), ([E, T, E, T, F, E, E, E, T, F, E, E, F], [E, T, E, T, F, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_408 (And.intro z_448 (And.intro z_542 trivial)))

theorem z_544 : le (tf [E, T, E, T, F, E, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, T, E, E, E, F, E, F] [([E, E, T, T, F, E, T, E, E, E, F, E, F], [E, E, T, T, F, E, T, E, E, F, E, E, F]), ([E, T, E, E, F, T, T, E, E, E, F, E, F], [E, T, E, E, F, T, T, E, E, F, E, E, F]), ([E, T, E, T, F, E, E, T, E, E, F, E, F], [E, T, E, T, F, E, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_409 (And.intro z_449 (And.intro z_543 trivial)))

theorem z_545 : le (tf [E, T, E, T, F, T, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, T, E, E, E, E, E, F, F] [([E, E, T, T, F, T, E, E, E, E, E, F, F], [E, E, T, T, F, T, E, E, E, E, F, E, F]), ([E, T, E, T, F, E, T, E, E, E, E, F, F], [E, T, E, T, F, E, T, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_410 (And.intro z_544 trivial))

theorem z_546 : le (tf [E, T, E, T, T, E, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, T, E, F, E, E, E, E, F, F] [([E, E, T, T, T, E, F, E, E, E, E, F, F], [E, E, T, T, T, F, E, E, E, E, E, F, F]), ([E, T, E, T, E, T, F, E, E, E, E, F, F], [E, T, E, T, F, T, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_370 (And.intro z_545 trivial))

theorem z_547 : le (tf [F, E, E, T, E, E, F, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, T, T, F] [([F, E, E, E, T, E, F, E, E, E, T, T, F], [F, E, E, E, T, F, E, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_354 trivial)

theorem z_548 : le (tf [F, E, E, T, E, E, E, F, E, T, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, E, T, F] [([F, E, E, E, T, E, E, F, E, T, E, T, F], [F, E, E, E, T, E, F, E, E, T, E, T, F]), ([F, E, E, T, E, E, E, F, E, E, T, T, F], [F, E, E, T, E, E, F, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_355 (And.intro z_547 trivial))

theorem z_549 : le (tf [F, E, E, T, E, E, E, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, F, E, E, T, F] [([F, E, E, E, T, E, E, T, F, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, T, F]), ([F, E, E, T, E, E, E, E, F, T, E, T, F], [F, E, E, T, E, E, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_126 (And.intro z_548 trivial))

theorem z_550 : le (tf [F, E, E, T, E, E, E, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, E, F, T, E, F] [([F, E, E, E, T, E, E, T, E, F, T, E, F], [F, E, E, E, T, E, E, T, F, E, T, E, F]), ([F, E, E, T, E, E, E, E, T, F, T, E, F], [F, E, E, T, E, E, E, F, T, E, T, E, F]), ([F, E, E, T, E, E, E, T, E, F, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_127 (And.intro z_324 (And.intro z_549 trivial)))

theorem z_551 : le (tf [E, F, E, T, E, E, E, T, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, T, F, E, E, F] [([E, F, E, E, T, E, E, T, T, F, E, E, F], [E, F, E, E, T, E, E, T, T, F, E, F, E]), ([E, F, E, T, E, E, E, T, E, F, T, E, F], [F, E, E, T, E, E, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 (And.intro z_550 trivial))

theorem z_552 : le (tf [E, F, E, T, E, E, T, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, T, E, F, E, F] [([E, F, E, E, T, E, T, E, T, E, F, E, F], [E, F, E, E, T, E, T, E, T, F, E, E, F]), ([E, F, E, T, E, E, E, T, T, E, F, E, F], [E, F, E, T, E, E, E, T, T, F, E, E, F]), ([E, F, E, T, E, E, T, E, E, T, F, E, F], [E, F, E, T, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_130 (And.intro z_551 (And.intro z_412 trivial)))

theorem z_553 : le (tf [E, F, E, T, E, E, T, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, T, E, E, E, F, F] [([E, F, E, E, T, E, T, T, E, E, E, F, F], [E, F, E, E, T, E, T, T, E, E, F, E, F]), ([E, F, E, T, E, E, T, E, T, E, E, F, F], [E, F, E, T, E, E, T, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 (And.intro z_552 trivial))

theorem z_554 : le (tf [F, E, E, T, E, E, E, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, T, T, E, F] [([F, E, E, E, T, E, E, E, F, T, T, E, F], [F, E, E, E, T, E, E, E, F, T, T, F, E]), ([F, E, E, T, E, E, E, E, F, T, E, T, F], [F, E, E, T, E, E, E, F, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_101 (And.intro z_548 trivial))

theorem z_555 : le (tf [E, F, E, T, E, E, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, F, E, T, E, F] [([E, F, E, E, T, E, E, T, F, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, T, E, F]), ([E, F, E, T, E, E, E, E, F, T, T, E, F], [F, E, E, T, E, E, E, E, F, T, T, E, F]), ([E, F, E, T, E, E, E, T, F, E, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_127 (And.intro z_554 (And.intro z_549 trivial)))

theorem z_556 : le (tf [F, E, T, E, E, E, E, F, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, T, T, E, F] [([F, E, E, T, E, E, E, F, E, T, T, E, F], [F, E, E, T, E, E, F, E, E, T, T, E, F]), ([F, E, T, E, E, E, E, F, E, T, E, T, F], [F, E, T, E, E, E, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_322 (And.intro z_361 trivial))

theorem z_557 : le (tf [F, T, E, E, E, E, F, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, E, F, T, T] [([F, E, T, E, E, E, F, E, E, E, F, T, T], [F, E, T, E, E, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_359 trivial)

theorem z_558 : le (tf [F, T, E, E, E, E, E, F, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, E, T, F, E, T] [([F, E, T, E, E, E, E, F, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, T, F, E, T]), ([F, T, E, E, E, E, E, F, E, E, F, T, T], [F, T, E, E, E, E, F, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_360 (And.intro z_557 trivial))

theorem z_559 : le (tf [F, T, E, E, E, E, E, E, F, T, F, T, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, F, T, F, T, E] [([F, E, T, E, E, E, E, E, F, T, F, T, E], [F, E, T, E, E, E, E, F, E, T, F, T, E]), ([F, T, E, E, E, E, E, E, F, T, F, E, T], [F, T, E, E, E, E, E, F, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_361 (And.intro z_558 trivial))

theorem z_560 : le (tf [F, T, E, E, E, E, E, E, F, T, T, E, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, F, T, T, E, F] [([F, E, T, E, E, E, E, E, F, T, T, E, F], [F, E, T, E, E, E, E, F, E, T, T, E, F]), ([F, T, E, E, E, E, E, E, F, T, E, T, F], [F, T, E, E, E, E, E, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_556 (And.intro z_559 trivial))

theorem z_561 : le (tf [F, T, E, E, E, E, E, T, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, T, F, E, E, T, F] [([F, E, T, E, E, E, E, T, F, E, E, T, F], [F, E, T, E, E, E, F, T, E, E, E, T, F]), ([F, T, E, E, E, E, E, E, F, T, E, T, F], [F, T, E, E, E, E, E, E, F, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_339 (And.intro z_559 trivial))

theorem z_562 : le (tf [E, T, F, E, E, E, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, F, E, T, E, F] [([E, E, F, T, E, E, E, T, F, E, T, E, F], [E, F, E, T, E, E, E, T, F, E, T, E, F]), ([E, T, F, E, E, E, E, E, F, T, T, E, F], [F, T, E, E, E, E, E, E, F, T, T, E, F]), ([E, T, F, E, E, E, E, T, F, E, E, T, F], [F, T, E, E, E, E, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_555 (And.intro z_560 (And.intro z_561 trivial)))

theorem z_563 : le (tf [E, T, F, E, E, E, E, T, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, T, F, E, E, F] [([E, E, F, T, E, E, E, T, T, F, E, E, F], [E, F, E, T, E, E, E, T, T, F, E, E, F]), ([E, T, F, E, E, E, E, T, E, F, T, E, F], [E, T, F, E, E, E, E, T, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_551 (And.intro z_562 trivial))

theorem z_564 : le (tf [E, T, F, E, E, E, T, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, T, E, F, E, F] [([E, E, F, T, E, E, T, E, T, E, F, E, F], [E, F, E, T, E, E, T, E, T, E, F, E, F]), ([E, T, F, E, E, E, E, T, T, E, F, E, F], [E, T, F, E, E, E, E, T, T, F, E, E, F]), ([E, T, F, E, E, E, T, E, E, T, F, E, F], [E, T, F, E, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_552 (And.intro z_563 (And.intro z_442 trivial)))

theorem z_565 : le (tf [E, T, F, E, E, E, T, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, T, E, E, E, F, F] [([E, E, F, T, E, E, T, T, E, E, E, F, F], [E, F, E, T, E, E, T, T, E, E, E, F, F]), ([E, T, F, E, E, E, T, E, T, E, E, F, F], [E, T, F, E, E, E, T, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_553 (And.intro z_564 trivial))

theorem z_566 : le (tf [F, E, E, T, E, E, T, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, E, E, F, E, T, F] [([F, E, E, E, T, E, T, E, E, F, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, T, F]), ([F, E, E, T, E, E, E, T, E, F, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 (And.intro z_549 trivial))

theorem z_567 : le (tf [F, E, E, T, E, T, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, E, E, E, F, T, F] [([F, E, E, E, T, T, E, E, E, E, F, T, F], [F, E, E, E, T, T, E, E, E, F, E, T, F]), ([F, E, E, T, E, E, T, E, E, E, F, T, F], [F, E, E, T, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_316 (And.intro z_566 trivial))

theorem z_568 : le (tf [E, F, E, T, E, T, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, E, T, F, E, F] [([E, F, E, E, T, T, E, E, E, T, F, E, F], [E, F, E, E, T, T, E, E, F, T, E, E, F]), ([E, F, E, T, E, E, T, E, E, T, F, E, F], [E, F, E, T, E, E, T, E, F, T, E, E, F]), ([E, F, E, T, E, T, E, E, E, E, F, T, F], [F, E, E, T, E, T, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_178 (And.intro z_412 (And.intro z_567 trivial)))

theorem z_569 : le (tf [E, F, E, T, E, T, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, T, E, E, F, F] [([E, F, E, E, T, T, E, E, T, E, E, F, F], [E, F, E, E, T, T, E, E, T, E, F, E, F]), ([E, F, E, T, E, E, T, E, T, E, E, F, F], [E, F, E, T, E, E, T, E, T, E, F, E, F]), ([E, F, E, T, E, T, E, E, E, T, E, F, F], [E, F, E, T, E, T, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_179 (And.intro z_552 (And.intro z_568 trivial)))

theorem z_570 : le (tf [F, T, E, E, E, E, T, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, T, E, E, F, E, T, F] [([F, E, T, E, E, E, T, E, E, F, E, T, F], [F, E, T, E, E, E, T, E, F, E, E, T, F]), ([F, T, E, E, E, E, E, T, E, F, E, T, F], [F, T, E, E, E, E, E, T, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_341 (And.intro z_561 trivial))

theorem z_571 : le (tf [F, T, E, E, E, T, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, T, E, E, E, E, F, T, F] [([F, E, T, E, E, T, E, E, E, E, F, T, F], [F, E, T, E, E, T, E, E, E, F, E, T, F]), ([F, T, E, E, E, E, T, E, E, E, F, T, F], [F, T, E, E, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_570 trivial))

theorem z_572 : le (tf [E, T, F, E, E, T, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, E, T, F, E, F] [([E, E, F, T, E, T, E, E, E, T, F, E, F], [E, F, E, T, E, T, E, E, E, T, F, E, F]), ([E, T, F, E, E, E, T, E, E, T, F, E, F], [E, T, F, E, E, E, T, E, F, T, E, E, F]), ([E, T, F, E, E, T, E, E, E, E, F, T, F], [F, T, E, E, E, T, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_568 (And.intro z_442 (And.intro z_571 trivial)))

theorem z_573 : le (tf [E, T, F, E, E, T, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, T, E, E, F, F] [([E, E, F, T, E, T, E, E, T, E, E, F, F], [E, F, E, T, E, T, E, E, T, E, E, F, F]), ([E, T, F, E, E, E, T, E, T, E, E, F, F], [E, T, F, E, E, E, T, E, T, E, F, E, F]), ([E, T, F, E, E, T, E, E, E, T, E, F, F], [E, T, F, E, E, T, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_569 (And.intro z_564 (And.intro z_572 trivial)))

theorem z_574 : le (tf [E, T, E, F, E, T, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, T, E, E, E, F, F] [([E, E, T, F, E, T, E, T, E, E, E, F, F], [E, E, T, F, E, T, E, T, E, E, F, E, F]), ([E, T, E, F, E, E, T, T, E, E, E, F, F], [E, T, F, E, E, E, T, T, E, E, E, F, F]), ([E, T, E, F, E, T, E, E, T, E, E, F, F], [E, T, F, E, E, T, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_346 (And.intro z_565 (And.intro z_573 trivial)))

theorem z_575 : le (tf [E, T, E, F, E, T, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, T, E, F, E, F] [([E, E, T, F, E, T, E, E, T, E, F, E, F], [E, E, T, F, E, T, E, E, T, F, E, E, F]), ([E, T, E, F, E, E, T, E, T, E, F, E, F], [E, T, F, E, E, E, T, E, T, E, F, E, F]), ([E, T, E, F, E, T, E, E, E, T, F, E, F], [E, T, F, E, E, T, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_345 (And.intro z_564 (And.intro z_572 trivial)))

theorem z_576 : le (tf [F, E, E, T, T, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, T, E, E, F, E, E, E, T, F] [([F, E, E, T, E, T, E, F, E, E, E, T, F], [F, E, E, T, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 trivial)

theorem z_577 : le (tf [E, F, E, T, T, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, F, E, E, T, E, F] [([E, F, E, T, E, T, E, F, E, E, T, E, F], [E, F, E, T, E, T, F, E, E, E, T, E, F]), ([E, F, E, T, T, E, E, F, E, E, E, T, F], [F, E, E, T, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_506 (And.intro z_576 trivial))

theorem z_578 : le (tf [E, F, E, T, T, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, F, E, E, E, E, T, F] [([E, F, E, T, E, T, F, E, E, E, E, T, F], [F, E, E, T, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 trivial)

theorem z_579 : le (tf [E, T, F, E, T, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, F, E, E, E, E, T, F] [([E, E, F, T, T, E, F, E, E, E, E, T, F], [E, F, E, T, T, E, F, E, E, E, E, T, F]), ([E, T, F, E, E, T, F, E, E, E, E, T, F], [E, T, F, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_578 (And.intro z_528 trivial))

theorem z_580 : le (tf [E, T, F, E, T, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, F, E, E, T, E, F] [([E, E, F, T, T, E, E, F, E, E, T, E, F], [E, F, E, T, T, E, E, F, E, E, T, E, F]), ([E, T, F, E, E, T, E, F, E, E, T, E, F], [E, T, F, E, E, T, F, E, E, E, T, E, F]), ([E, T, F, E, T, E, E, F, E, E, E, T, F], [E, T, F, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_577 (And.intro z_529 (And.intro z_579 trivial)))

theorem z_581 : le (tf [E, T, F, T, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, E, F, E, E, E, T, F] [([E, T, F, E, T, E, E, F, E, E, E, T, F], [E, T, F, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_579 trivial)

theorem z_582 : le (tf [E, T, F, T, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, E, E, F, E, T, E, F] [([E, T, F, E, T, E, E, E, F, E, T, E, F], [E, T, F, E, T, E, E, F, E, E, T, E, F]), ([E, T, F, T, E, E, E, E, F, E, E, T, F], [E, T, F, T, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_580 (And.intro z_581 trivial))

theorem z_583 : le (tf [E, T, E, T, F, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, F, T, E, E, F] [([E, E, T, T, F, E, E, E, F, T, E, E, F], [E, E, T, T, F, E, E, F, E, T, E, E, F]), ([E, T, E, E, F, T, E, E, F, T, E, E, F], [E, T, E, F, E, T, E, E, F, T, E, E, F]), ([E, T, E, T, F, E, E, E, F, E, T, E, F], [E, T, F, T, E, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_407 (And.intro z_447 (And.intro z_582 trivial)))

theorem z_584 : le (tf [E, T, E, T, F, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, T, E, F, E, F] [([E, E, T, T, F, E, E, E, T, E, F, E, F], [E, E, T, T, F, E, E, E, T, F, E, E, F]), ([E, T, E, E, F, T, E, E, T, E, F, E, F], [E, T, E, F, E, T, E, E, T, E, F, E, F]), ([E, T, E, T, F, E, E, E, E, T, F, E, F], [E, T, E, T, F, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_367 (And.intro z_575 (And.intro z_583 trivial)))

theorem z_585 : le (tf [E, T, E, T, F, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, T, E, E, E, F, F] [([E, E, T, T, F, E, E, T, E, E, E, F, F], [E, E, T, T, F, E, E, T, E, E, F, E, F]), ([E, T, E, E, F, T, E, T, E, E, E, F, F], [E, T, E, F, E, T, E, T, E, E, E, F, F]), ([E, T, E, T, F, E, E, E, T, E, E, F, F], [E, T, E, T, F, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_368 (And.intro z_574 (And.intro z_584 trivial)))

theorem z_586 : le (tf [F, E, E, T, T, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, T, E, E, E, E, F, E, T, F] [([F, E, E, T, E, T, E, E, E, F, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 trivial)

theorem z_587 : le (tf [E, F, E, T, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, F, T, E, F] [([E, F, E, T, E, T, E, E, E, F, T, E, F], [E, F, E, T, E, T, E, E, F, E, T, E, F]), ([E, F, E, T, T, E, E, E, E, F, E, T, F], [F, E, E, T, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_328 (And.intro z_586 trivial))

theorem z_588 : le (tf [E, F, E, T, T, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, T, E, F, F] [([E, F, E, T, E, T, E, E, E, T, E, F, F], [E, F, E, T, E, T, E, E, E, T, F, E, F]), ([E, F, E, T, T, E, E, E, E, E, T, F, F], [E, F, E, T, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_568 (And.intro z_587 trivial))

theorem z_589 : le (tf [E, F, E, T, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, F, E, E, T, F] [([E, F, E, T, E, T, E, E, F, E, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 trivial)

theorem z_590 : le (tf [E, T, F, E, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, F, E, E, T, F] [([E, E, F, T, T, E, E, E, F, E, E, T, F], [E, F, E, T, T, E, E, E, F, E, E, T, F]), ([E, T, F, E, E, T, E, E, F, E, E, T, F], [E, T, F, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_589 (And.intro z_445 trivial))

theorem z_591 : le (tf [E, T, F, E, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, F, T, E, F] [([E, E, F, T, T, E, E, E, E, F, T, E, F], [E, F, E, T, T, E, E, E, E, F, T, E, F]), ([E, T, F, E, E, T, E, E, E, F, T, E, F], [E, T, F, E, E, T, E, E, F, E, T, E, F]), ([E, T, F, E, T, E, E, E, E, F, E, T, F], [E, T, F, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_587 (And.intro z_446 (And.intro z_590 trivial)))

theorem z_592 : le (tf [E, T, F, E, T, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, T, E, F, F] [([E, E, F, T, T, E, E, E, E, T, E, F, F], [E, F, E, T, T, E, E, E, E, T, E, F, F]), ([E, T, F, E, E, T, E, E, E, T, E, F, F], [E, T, F, E, E, T, E, E, E, T, F, E, F]), ([E, T, F, E, T, E, E, E, E, E, T, F, F], [E, T, F, E, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_588 (And.intro z_572 (And.intro z_591 trivial)))

theorem z_593 : le (tf [E, T, T, F, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, F, E, E, T, F] [([E, T, E, F, T, E, E, E, F, E, E, T, F], [E, T, F, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_590 trivial)

theorem z_594 : le (tf [E, T, T, F, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, E, F, T, E, F] [([E, T, E, F, T, E, E, E, E, F, T, E, F], [E, T, F, E, T, E, E, E, E, F, T, E, F]), ([E, T, T, F, E, E, E, E, E, F, E, T, F], [E, T, T, F, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_591 (And.intro z_593 trivial))

theorem z_595 : le (tf [E, T, T, F, E, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, E, T, E, F, F] [([E, T, E, F, T, E, E, E, E, T, E, F, F], [E, T, F, E, T, E, E, E, E, T, E, F, F]), ([E, T, T, F, E, E, E, E, E, E, T, F, F], [E, T, T, F, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_592 (And.intro z_594 trivial))

theorem z_596 : le (tf [E, T, T, E, F, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, F, E, E, E, T, E, E, F, F] [([E, T, E, T, F, E, E, E, T, E, E, F, F], [E, T, E, T, F, E, E, E, T, E, F, E, F]), ([E, T, T, E, F, E, E, E, E, T, E, F, F], [E, T, T, F, E, E, E, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_584 (And.intro z_595 trivial))

theorem z_597 : le (tf [E, T, T, E, E, F, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, F, E, T, E, E, E, F, F] [([E, T, E, T, E, F, E, T, E, E, E, F, F], [E, T, E, T, F, E, E, T, E, E, E, F, F]), ([E, T, T, E, E, F, E, E, T, E, E, F, F], [E, T, T, E, F, E, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_585 (And.intro z_596 trivial))

theorem z_598 : le (tf [E, T, T, E, E, T, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, T, F, E, E, E, E, F, F] [([E, T, E, T, E, T, F, E, E, E, E, F, F], [E, T, E, T, F, T, E, E, E, E, E, F, F]), ([E, T, T, E, E, E, F, T, E, E, E, F, F], [E, T, T, E, E, F, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_545 (And.intro z_597 trivial))

theorem z_599 : le (tf [E, T, T, E, T, E, E, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, T, E, E, F, E, E, E, F, F] [([E, T, E, T, T, E, E, F, E, E, E, F, F], [E, T, E, T, T, E, F, E, E, E, E, F, F]), ([E, T, T, E, E, T, E, F, E, E, E, F, F], [E, T, T, E, E, T, F, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_546 (And.intro z_598 trivial))

theorem z_600 : le (tf [E, T, T, T, E, E, E, E, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, E, E, E, E, F, E, E, F, F] [([E, T, T, E, T, E, E, E, F, E, E, F, F], [E, T, T, E, T, E, E, F, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_599 trivial)

theorem z_601 : le (tf [E, E, E, T, T, T, F, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, T, F, F, E, E, E, E, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_602 : le (tf [E, E, E, T, T, F, F, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_603 : le (tf [E, E, E, T, T, F, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, F, E, T, E] [([E, E, E, T, T, F, F, E, E, F, E, E, T], [E, E, E, T, T, F, F, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_602 trivial)

theorem z_604 : le (tf [E, E, E, T, T, F, F, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, T, F, E, E] [([E, E, E, T, T, F, F, E, E, E, F, T, E], [E, E, E, T, T, F, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_603 trivial)

theorem z_605 : le (tf [E, E, E, T, T, F, F, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, T, E, E, F, E] [([E, E, E, T, T, F, F, E, E, T, E, F, E], [E, E, E, T, T, F, F, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_604 trivial)

theorem z_606 : le (tf [E, E, E, T, T, F, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, T, E, E, E, E, F] [([E, E, E, T, T, F, F, E, T, E, E, E, F], [E, E, E, T, T, F, F, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_605 trivial)

theorem z_607 : le (tf [E, E, F, T, E, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, T, T, F, E, E, E, F] [([E, E, F, E, T, E, T, T, F, E, E, E, F], [E, F, E, E, T, E, T, T, F, E, E, E, F]), ([E, E, F, T, E, E, T, E, F, T, E, E, F], [E, F, E, T, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_372 (And.intro z_412 trivial))

theorem z_608 : le (tf [E, F, E, E, E, T, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, E, T, E, E, F] [([E, F, E, E, E, T, F, E, T, T, E, E, F], [F, E, E, E, E, T, F, E, T, T, E, E, F]), ([E, F, E, E, E, T, F, T, E, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 (And.intro z_107 trivial))

theorem z_609 : le (tf [E, F, E, E, E, T, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, E, F, T, E, E, F] [([E, F, E, E, E, T, E, T, F, T, E, E, F], [E, F, E, E, E, T, F, T, E, T, E, E, F]), ([E, F, E, E, E, T, T, E, F, E, T, E, F], [F, E, E, E, E, T, T, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_608 (And.intro z_119 trivial))

theorem z_610 : le (tf [E, F, E, E, T, E, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, F, T, E, E, F] [([E, F, E, E, E, T, E, T, F, T, E, E, F], [E, F, E, E, E, T, F, T, E, T, E, E, F]), ([E, F, E, E, T, E, E, T, F, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_608 (And.intro z_127 trivial))

theorem z_611 : le (tf [E, E, F, E, T, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, E, F, T, E, E, F] [([E, E, F, E, E, T, T, E, F, T, E, E, F], [E, F, E, E, E, T, T, E, F, T, E, E, F]), ([E, E, F, E, T, E, E, T, F, T, E, E, F], [E, F, E, E, T, E, E, T, F, T, E, E, F]), ([E, E, F, E, T, E, T, E, F, E, T, E, F], [E, F, E, E, T, E, T, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_609 (And.intro z_610 (And.intro z_348 trivial)))

theorem z_612 : le (tf [E, F, T, E, E, E, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, T, F, T, E, E, F] [([E, F, E, T, E, E, E, T, F, T, E, E, F], [E, F, E, T, E, E, F, T, E, T, E, E, F]), ([E, F, T, E, E, E, E, T, F, E, T, E, F], [E, F, T, E, E, E, F, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_411 (And.intro z_340 trivial))

theorem z_613 : le (tf [E, E, T, F, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, E, F, T, E, E, F] [([E, E, E, F, T, E, T, E, F, T, E, E, F], [E, E, F, E, T, E, T, E, F, T, E, E, F]), ([E, E, T, F, E, E, E, T, F, T, E, E, F], [E, F, T, E, E, E, E, T, F, T, E, E, F]), ([E, E, T, F, E, E, T, E, F, E, T, E, F], [E, F, T, E, E, E, T, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_611 (And.intro z_612 (And.intro z_342 trivial)))

theorem z_614 : le (tf [E, E, T, E, F, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, T, F, E, E, E, F] [([E, E, E, T, F, E, T, T, F, E, E, E, F], [E, E, F, T, E, E, T, T, F, E, E, E, F]), ([E, E, T, E, F, E, T, E, F, T, E, E, F], [E, E, T, F, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_607 (And.intro z_613 trivial))

theorem z_615 : le (tf [E, F, T, E, T, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, T, E, E, F, E, E, E, T, F] [([E, F, E, T, T, E, E, F, E, E, E, T, F], [F, E, E, T, T, E, E, F, E, E, E, T, F]), ([E, F, T, E, E, T, E, F, E, E, E, T, F], [E, F, T, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_576 (And.intro z_400 trivial))

theorem z_616 : le (tf [E, E, T, F, T, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, F, E, E, T, E, F] [([E, E, T, F, E, T, E, F, E, E, T, E, F], [E, E, T, F, E, T, F, E, E, E, T, E, F]), ([E, E, T, F, T, E, E, F, E, E, E, T, F], [E, F, T, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 (And.intro z_615 trivial))

theorem z_617 : le (tf [E, E, T, F, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, E, F, T, E, E, F] [([E, E, T, F, E, T, E, E, F, T, E, E, F], [E, E, T, F, E, T, E, F, E, T, E, E, F]), ([E, E, T, F, T, E, E, E, F, E, T, E, F], [E, E, T, F, T, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_616 trivial))

theorem z_618 : le (tf [E, E, T, E, T, F, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, T, F, E, E, E, F] [([E, E, E, T, T, F, E, T, F, E, E, E, F], [E, E, E, T, T, F, F, T, E, E, E, E, F]), ([E, E, T, E, E, F, T, T, F, E, E, E, F], [E, E, T, E, F, E, T, T, F, E, E, E, F]), ([E, E, T, E, T, F, E, E, F, T, E, E, F], [E, E, T, F, T, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_606 (And.intro z_614 (And.intro z_617 trivial)))

theorem z_619 : le (tf [E, E, T, E, T, T, F, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, T, F, E, F, E, E, E, F] [([E, E, E, T, T, T, F, E, F, E, E, E, F], [E, E, E, T, T, T, F, F, E, E, E, E, F]), ([E, E, T, E, T, E, F, T, F, E, E, E, F], [E, E, T, E, T, F, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_601 (And.intro z_618 trivial))

theorem z_620 : le (tf [E, F, E, T, E, E, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, E, F, T, E, F] [([E, F, E, E, T, E, T, E, E, F, T, E, F], [F, E, E, E, T, E, T, E, E, F, T, E, F]), ([E, F, E, T, E, E, E, T, E, F, T, E, F], [F, E, E, T, E, E, E, T, E, F, T, E, F]), ([E, F, E, T, E, E, T, E, E, F, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_129 (And.intro z_550 (And.intro z_566 trivial)))

theorem z_621 : le (tf [E, T, F, E, E, E, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, E, F, T, E, F] [([E, E, F, T, E, E, T, E, E, F, T, E, F], [E, F, E, T, E, E, T, E, E, F, T, E, F]), ([E, T, F, E, E, E, E, T, E, F, T, E, F], [E, T, F, E, E, E, E, T, F, E, T, E, F]), ([E, T, F, E, E, E, T, E, E, F, E, T, F], [F, T, E, E, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_620 (And.intro z_562 (And.intro z_570 trivial)))

theorem z_622 : le (tf [E, T, E, F, E, E, T, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, E, T, F, E, E, F] [([E, E, T, F, E, E, T, E, T, F, E, E, F], [E, E, T, F, E, E, T, F, T, E, E, E, F]), ([E, T, E, F, E, E, E, T, T, F, E, E, F], [E, T, F, E, E, E, E, T, T, F, E, E, F]), ([E, T, E, F, E, E, T, E, E, F, T, E, F], [E, T, F, E, E, E, T, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_314 (And.intro z_563 (And.intro z_621 trivial)))

theorem z_623 : le (tf [E, T, E, E, F, E, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, T, E, F, E, E, F] [([E, E, T, E, F, E, T, T, E, F, E, E, F], [E, E, T, F, E, E, T, T, E, F, E, E, F]), ([E, T, E, E, F, E, T, E, T, F, E, E, F], [E, T, E, F, E, E, T, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_315 (And.intro z_622 trivial))

theorem z_624 : le (tf [F, E, E, T, E, T, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, F, E, E, E, F, E, T] [([F, E, E, E, T, T, F, E, E, E, F, E, T], [F, E, E, E, T, T, F, E, E, F, E, E, T]), ([F, E, E, T, E, E, F, T, E, E, F, E, T], [F, E, E, T, E, F, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_397 (And.intro z_469 trivial))

theorem z_625 : le (tf [F, E, E, T, T, E, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, T, E, F, E, E, E, E, F, T] [([F, E, E, T, E, T, F, E, E, E, E, F, T], [F, E, E, T, E, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_624 trivial)

theorem z_626 : le (tf [F, E, T, E, E, T, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, T, F, E, E, E, E, F, T] [([F, E, E, T, E, T, F, E, E, E, E, F, T], [F, E, E, T, E, T, F, E, E, E, F, E, T]), ([F, E, T, E, E, E, F, T, E, E, E, F, T], [F, E, T, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_624 (And.intro z_471 trivial))

theorem z_627 : le (tf [E, F, T, E, T, E, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, E, T, E, F, E, E, E, E, F, T] [([E, F, E, T, T, E, F, E, E, E, E, F, T], [F, E, E, T, T, E, F, E, E, E, E, F, T]), ([E, F, T, E, E, T, F, E, E, E, E, F, T], [F, E, T, E, E, T, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_625 (And.intro z_626 trivial))

theorem z_628 : le (tf [E, E, T, F, T, E, F, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, F, E, E, E, T, F, E] [([E, E, T, F, E, T, F, E, E, E, T, F, E], [E, E, T, F, E, T, F, E, E, F, T, E, E]), ([E, E, T, F, T, E, F, E, E, E, E, F, T], [E, F, T, E, T, E, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_498 (And.intro z_627 trivial))

theorem z_629 : le (tf [E, E, T, F, T, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, F, E, E, T, E, E, F] [([E, E, T, F, E, T, F, E, E, T, E, E, F], [E, E, T, F, E, T, F, E, E, T, E, F, E]), ([E, E, T, F, T, E, F, E, E, E, T, E, F], [E, E, T, F, T, E, F, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_499 (And.intro z_628 trivial))

theorem z_630 : le (tf [E, E, T, F, T, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, F, T, E, E, E, F] [([E, E, T, F, E, T, E, F, T, E, E, E, F], [E, E, T, F, E, T, F, E, T, E, E, E, F]), ([E, E, T, F, T, E, E, F, E, T, E, E, F], [E, E, T, F, T, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_500 (And.intro z_629 trivial))

theorem z_631 : le (tf [E, F, E, T, E, E, E, F, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, T, T, E, E, F] [([E, F, E, E, T, E, E, F, T, T, E, E, F], [F, E, E, E, T, E, E, F, T, T, E, E, F]), ([E, F, E, T, E, E, E, F, T, E, T, E, F], [F, E, E, T, E, E, E, F, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_134 (And.intro z_324 trivial))

theorem z_632 : le (tf [E, T, F, E, E, E, E, F, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, T, T, E, E, F] [([E, E, F, T, E, E, E, F, T, T, E, E, F], [E, F, E, T, E, E, E, F, T, T, E, E, F]), ([E, T, F, E, E, E, E, F, T, E, T, E, F], [E, T, F, E, E, E, F, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_631 (And.intro z_438 trivial))

theorem z_633 : le (tf [E, T, E, F, E, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, F, E, T, E, E, F] [([E, E, T, F, E, E, T, F, E, T, E, E, F], [E, E, T, F, E, E, T, F, E, T, E, F, E]), ([E, T, E, F, E, E, E, F, T, T, E, E, F], [E, T, F, E, E, E, E, F, T, T, E, E, F]), ([E, T, E, F, E, E, T, F, E, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_313 (And.intro z_632 (And.intro z_441 trivial)))

theorem z_634 : le (tf [E, T, E, E, F, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, F, T, E, E, E, F] [([E, E, T, E, F, E, T, F, T, E, E, E, F], [E, E, T, F, E, E, T, F, T, E, E, E, F]), ([E, T, E, E, F, E, T, F, E, T, E, E, F], [E, T, E, F, E, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_314 (And.intro z_633 trivial))

theorem z_635 : le (tf [E, T, E, F, T, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, T, E, E, F, E, T, E, E, F] [([E, E, T, F, T, E, E, F, E, T, E, E, F], [E, E, T, F, T, E, F, E, E, T, E, E, F]), ([E, T, E, F, E, T, E, F, E, T, E, E, F], [E, T, E, F, E, T, F, E, E, T, E, E, F]), ([E, T, E, F, T, E, E, F, E, E, T, E, F], [E, T, F, E, T, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_629 (And.intro z_530 (And.intro z_580 trivial)))

theorem z_636 : le (tf [E, T, E, E, T, F, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, F, T, E, E, E, F] [([E, E, T, E, T, F, E, F, T, E, E, E, F], [E, E, T, F, T, E, E, F, T, E, E, E, F]), ([E, T, E, E, E, F, T, F, T, E, E, E, F], [E, T, E, E, F, E, T, F, T, E, E, E, F]), ([E, T, E, E, T, F, E, F, E, T, E, E, F], [E, T, E, F, T, E, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_630 (And.intro z_634 (And.intro z_635 trivial)))

theorem z_637 : le (tf [E, T, E, E, T, F, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, T, E, F, E, E, F] [([E, E, T, E, T, F, E, T, E, F, E, E, F], [E, E, T, E, T, F, E, T, F, E, E, E, F]), ([E, T, E, E, E, F, T, T, E, F, E, E, F], [E, T, E, E, F, E, T, T, E, F, E, E, F]), ([E, T, E, E, T, F, E, E, T, F, E, E, F], [E, T, E, E, T, F, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_618 (And.intro z_623 (And.intro z_636 trivial)))

theorem z_638 : le (tf [E, T, E, E, T, T, F, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, T, F, E, E, F, E, E, F] [([E, E, T, E, T, T, F, E, E, F, E, E, F], [E, E, T, E, T, T, F, E, F, E, E, E, F]), ([E, T, E, E, T, E, F, T, E, F, E, E, F], [E, T, E, E, T, F, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_619 (And.intro z_637 trivial))

theorem z_639 : le (tf [T, F, E, E, E, F, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, E, E, F, T, T] [([E, F, T, E, E, F, E, E, E, E, F, T, T], [F, E, T, E, E, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_359 trivial)

theorem z_640 : le (tf [T, F, E, E, E, E, F, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, E, E, T, F, E, T] [([E, F, T, E, E, E, F, E, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, T, F, E, T]), ([T, F, E, E, E, E, F, E, E, E, F, T, T], [T, F, E, E, E, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_360 (And.intro z_639 trivial))

theorem z_641 : le (tf [T, F, E, E, E, E, E, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, T, F, T, E] [([E, F, T, E, E, E, E, F, E, T, F, T, E], [F, E, T, E, E, E, E, F, E, T, F, T, E]), ([T, F, E, E, E, E, E, F, E, T, F, E, T], [T, F, E, E, E, E, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_361 (And.intro z_640 trivial))

theorem z_642 : le (tf [T, F, E, E, E, E, E, F, E, T, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, T, T, E, F] [([E, F, T, E, E, E, E, F, E, T, T, E, F], [F, E, T, E, E, E, E, F, E, T, T, E, F]), ([T, F, E, E, E, E, E, F, E, T, E, T, F], [T, F, E, E, E, E, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_556 (And.intro z_641 trivial))

theorem z_643 : le (tf [F, E, T, E, F, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, T, F, E, T] [([F, E, E, T, F, E, E, E, E, T, F, E, T], [F, E, E, T, F, E, E, E, F, T, E, E, T]), ([F, E, T, E, F, E, E, E, E, E, F, T, T], [F, E, T, E, F, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_296 (And.intro z_250 trivial))

theorem z_644 : le (tf [F, E, T, F, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, E, E, F, T, T] [([F, E, E, F, T, E, E, E, E, E, F, T, T], [F, E, F, E, T, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_122 trivial)

theorem z_645 : le (tf [T, F, E, F, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, E, F, E, E, E, E, E, E, F, T, T] [([E, F, T, F, E, E, E, E, E, E, F, T, T], [F, E, T, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_644 trivial)

theorem z_646 : le (tf [T, F, E, E, F, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, E, F, E, E, E, E, T, F, E, T] [([E, F, T, E, F, E, E, E, E, T, F, E, T], [F, E, T, E, F, E, E, E, E, T, F, E, T]), ([T, F, E, E, F, E, E, E, E, E, F, T, T], [T, F, E, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_643 (And.intro z_645 trivial))

theorem z_647 : le (tf [T, F, E, E, E, F, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, E, T, F, T, E] [([E, F, T, E, E, F, E, E, E, T, F, T, E], [F, E, T, E, E, F, E, E, E, T, F, T, E]), ([T, F, E, E, E, F, E, E, E, T, F, E, T], [T, F, E, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_337 (And.intro z_646 trivial))

theorem z_648 : le (tf [T, F, E, E, E, F, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, T, E, E, T, F] [([E, F, T, E, E, F, E, E, T, E, E, T, F], [F, E, T, E, E, F, E, E, T, E, E, T, F]), ([T, F, E, E, E, F, E, E, E, T, E, T, F], [T, F, E, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_338 (And.intro z_647 trivial))

theorem z_649 : le (tf [T, F, E, E, E, E, F, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, T, E, E, E, T, F] [([E, F, T, E, E, E, F, T, E, E, E, T, F], [F, E, T, E, E, E, F, T, E, E, E, T, F]), ([T, F, E, E, E, E, F, E, T, E, E, T, F], [T, F, E, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_339 (And.intro z_648 trivial))

theorem z_650 : le (tf [T, F, E, E, E, E, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, T, F, E, T, E, F] [([E, F, T, E, E, E, E, T, F, E, T, E, F], [E, F, T, E, E, E, F, T, E, E, T, E, F]), ([T, F, E, E, E, E, E, E, F, T, T, E, F], [T, F, E, E, E, E, E, F, E, T, T, E, F]), ([T, F, E, E, E, E, E, T, F, E, E, T, F], [T, F, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_340 (And.intro z_642 (And.intro z_649 trivial)))

theorem z_651 : le (tf [T, E, F, E, E, E, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, F, T, E, E, F] [([E, T, F, E, E, E, E, T, F, T, E, E, F], [E, T, F, E, E, E, F, T, E, T, E, E, F]), ([T, E, F, E, E, E, E, T, F, E, T, E, F], [T, F, E, E, E, E, E, T, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 (And.intro z_650 trivial))

theorem z_652 : le (tf [T, E, F, E, E, E, E, T, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, T, E, F, E, F] [([E, T, F, E, E, E, E, T, T, E, F, E, F], [E, T, F, E, E, E, E, T, T, F, E, E, F]), ([T, E, F, E, E, E, E, T, E, T, F, E, F], [T, E, F, E, E, E, E, T, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_563 (And.intro z_651 trivial))

theorem z_653 : le (tf [F, E, T, E, E, E, E, T, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, T, E, F, E, T, F] [([F, E, E, T, E, E, E, T, E, F, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, T, F]), ([F, E, T, E, E, E, E, E, T, F, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_549 (And.intro z_362 trivial))

theorem z_654 : le (tf [F, E, T, E, E, E, T, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, T, E, E, E, F, T, F] [([F, E, E, T, E, E, T, E, E, E, F, T, F], [F, E, E, T, E, E, T, E, E, F, E, T, F]), ([F, E, T, E, E, E, E, T, E, E, F, T, F], [F, E, T, E, E, E, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_566 (And.intro z_653 trivial))

theorem z_655 : le (tf [T, F, E, E, E, E, E, F, T, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, T, E, E, T, F] [([E, F, T, E, E, E, E, F, T, E, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, T, F]), ([T, F, E, E, E, E, E, F, E, T, E, T, F], [T, F, E, E, E, E, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_362 (And.intro z_641 trivial))

theorem z_656 : le (tf [T, F, E, E, E, E, E, T, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, T, E, F, E, T, F] [([E, F, T, E, E, E, E, T, E, F, E, T, F], [F, E, T, E, E, E, E, T, E, F, E, T, F]), ([T, F, E, E, E, E, E, E, T, F, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_653 (And.intro z_655 trivial))

theorem z_657 : le (tf [T, F, E, E, E, E, T, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, T, E, E, E, F, T, F] [([E, F, T, E, E, E, T, E, E, E, F, T, F], [F, E, T, E, E, E, T, E, E, E, F, T, F]), ([T, F, E, E, E, E, E, T, E, E, F, T, F], [T, F, E, E, E, E, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_654 (And.intro z_656 trivial))

theorem z_658 : le (tf [T, E, F, E, E, E, T, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, T, E, E, T, F, E, F] [([E, T, F, E, E, E, T, E, E, T, F, E, F], [E, T, F, E, E, E, T, E, F, T, E, E, F]), ([T, E, F, E, E, E, E, T, E, T, F, E, F], [T, E, F, E, E, E, E, T, F, T, E, E, F]), ([T, E, F, E, E, E, T, E, E, E, F, T, F], [T, F, E, E, E, E, T, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_442 (And.intro z_651 (And.intro z_657 trivial)))

theorem z_659 : le (tf [T, E, E, F, E, E, T, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, E, T, E, F, E, F] [([E, T, E, F, E, E, T, E, T, E, F, E, F], [E, T, F, E, E, E, T, E, T, E, F, E, F]), ([T, E, E, F, E, E, E, T, T, E, F, E, F], [T, E, F, E, E, E, E, T, T, E, F, E, F]), ([T, E, E, F, E, E, T, E, E, T, F, E, F], [T, E, F, E, E, E, T, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_564 (And.intro z_652 (And.intro z_658 trivial)))

theorem z_660 : le (tf [T, E, E, E, F, E, T, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, T, E, E, F, E, F] [([E, T, E, E, F, E, T, T, E, E, F, E, F], [E, T, E, E, F, E, T, T, E, F, E, E, F]), ([T, E, E, E, F, E, T, E, T, E, F, E, F], [T, E, E, F, E, E, T, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_623 (And.intro z_659 trivial))

theorem z_661 : le (tf [F, E, T, E, E, E, E, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, T, F, T, E, F] [([F, E, E, T, E, E, E, E, T, F, T, E, F], [F, E, E, T, E, E, E, F, T, E, T, E, F]), ([F, E, T, E, E, E, E, E, T, F, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_324 (And.intro z_362 trivial))

theorem z_662 : le (tf [T, F, E, E, E, E, E, E, T, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, T, F, T, E, F] [([E, F, T, E, E, E, E, E, T, F, T, E, F], [F, E, T, E, E, E, E, E, T, F, T, E, F]), ([T, F, E, E, E, E, E, E, T, F, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_661 (And.intro z_655 trivial))

theorem z_663 : le (tf [T, E, F, E, E, E, E, T, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, E, F, T, E, F] [([E, T, F, E, E, E, E, T, E, F, T, E, F], [E, T, F, E, E, E, E, T, F, E, T, E, F]), ([T, E, F, E, E, E, E, E, T, F, T, E, F], [T, F, E, E, E, E, E, E, T, F, T, E, F]), ([T, E, F, E, E, E, E, T, E, F, E, T, F], [T, F, E, E, E, E, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 (And.intro z_662 (And.intro z_656 trivial)))

theorem z_664 : le (tf [T, E, E, F, E, E, E, T, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, T, T, F, E, E, F] [([E, T, E, F, E, E, E, T, T, F, E, E, F], [E, T, F, E, E, E, E, T, T, F, E, E, F]), ([T, E, E, F, E, E, E, T, E, F, T, E, F], [T, E, F, E, E, E, E, T, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_563 (And.intro z_663 trivial))

theorem z_665 : le (tf [T, E, F, E, E, E, T, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, T, E, E, F, E, T, F] [([E, T, F, E, E, E, T, E, E, F, E, T, F], [F, T, E, E, E, E, T, E, E, F, E, T, F]), ([T, E, F, E, E, E, E, T, E, F, E, T, F], [T, F, E, E, E, E, E, T, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_570 (And.intro z_656 trivial))

theorem z_666 : le (tf [T, E, E, F, E, E, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, E, E, F, T, E, F] [([E, T, E, F, E, E, T, E, E, F, T, E, F], [E, T, F, E, E, E, T, E, E, F, T, E, F]), ([T, E, E, F, E, E, E, T, E, F, T, E, F], [T, E, F, E, E, E, E, T, E, F, T, E, F]), ([T, E, E, F, E, E, T, E, E, F, E, T, F], [T, E, F, E, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_621 (And.intro z_663 (And.intro z_665 trivial)))

theorem z_667 : le (tf [T, E, E, E, F, E, T, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, E, T, F, E, E, F] [([E, T, E, E, F, E, T, E, T, F, E, E, F], [E, T, E, F, E, E, T, E, T, F, E, E, F]), ([T, E, E, E, F, E, E, T, T, F, E, E, F], [T, E, E, F, E, E, E, T, T, F, E, E, F]), ([T, E, E, E, F, E, T, E, E, F, T, E, F], [T, E, E, F, E, E, T, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_622 (And.intro z_664 (And.intro z_666 trivial)))

theorem z_668 : le (tf [T, F, E, E, E, E, T, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, T, E, F, E, E, T, F] [([E, F, T, E, E, E, T, E, F, E, E, T, F], [F, E, T, E, E, E, T, E, F, E, E, T, F]), ([T, F, E, E, E, E, E, T, F, E, E, T, F], [T, F, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_341 (And.intro z_649 trivial))

theorem z_669 : le (tf [T, F, E, E, E, E, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, T, E, E, F, T, E, F] [([E, F, T, E, E, E, T, E, E, F, T, E, F], [E, F, T, E, E, E, T, E, F, E, T, E, F]), ([T, F, E, E, E, E, E, T, E, F, T, E, F], [T, F, E, E, E, E, E, T, F, E, T, E, F]), ([T, F, E, E, E, E, T, E, E, F, E, T, F], [T, F, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_342 (And.intro z_650 (And.intro z_668 trivial)))

theorem z_670 : le (tf [T, F, E, E, E, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, T, E, E, E, F, E, T, F] [([E, F, T, E, E, T, E, E, E, F, E, T, F], [F, E, T, E, E, T, E, E, E, F, E, T, F]), ([T, F, E, E, E, E, T, E, E, F, E, T, F], [T, F, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_668 trivial))

theorem z_671 : le (tf [T, E, F, E, E, T, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, E, E, E, F, T, E, F] [([E, T, F, E, E, T, E, E, E, F, T, E, F], [E, T, F, E, E, T, E, E, F, E, T, E, F]), ([T, E, F, E, E, E, T, E, E, F, T, E, F], [T, F, E, E, E, E, T, E, E, F, T, E, F]), ([T, E, F, E, E, T, E, E, E, F, E, T, F], [T, F, E, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_446 (And.intro z_669 (And.intro z_670 trivial)))

theorem z_672 : le (tf [T, E, F, E, T, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, T, E, E, E, E, F, E, T, F] [([E, T, F, E, T, E, E, E, E, F, E, T, F], [E, T, F, E, T, E, E, E, F, E, E, T, F]), ([T, E, F, E, E, T, E, E, E, F, E, T, F], [T, F, E, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_590 (And.intro z_670 trivial))

theorem z_673 : le (tf [T, E, E, F, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, E, E, E, E, F, T, E, F] [([E, T, E, F, T, E, E, E, E, F, T, E, F], [E, T, F, E, T, E, E, E, E, F, T, E, F]), ([T, E, E, F, E, T, E, E, E, F, T, E, F], [T, E, F, E, E, T, E, E, E, F, T, E, F]), ([T, E, E, F, T, E, E, E, E, F, E, T, F], [T, E, F, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_591 (And.intro z_671 (And.intro z_672 trivial)))

theorem z_674 : le (tf [T, E, E, E, T, F, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, E, E, T, F, E, E, F] [([E, T, E, E, T, F, E, E, T, F, E, E, F], [E, T, E, E, T, F, E, F, T, E, E, E, F]), ([T, E, E, E, E, F, T, E, T, F, E, E, F], [T, E, E, E, F, E, T, E, T, F, E, E, F]), ([T, E, E, E, T, F, E, E, E, F, T, E, F], [T, E, E, F, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_636 (And.intro z_667 (And.intro z_673 trivial)))

theorem z_675 : le (tf [T, E, E, E, T, F, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, E, T, E, E, F, E, F] [([E, T, E, E, T, F, E, T, E, E, F, E, F], [E, T, E, E, T, F, E, T, E, F, E, E, F]), ([T, E, E, E, E, F, T, T, E, E, F, E, F], [T, E, E, E, F, E, T, T, E, E, F, E, F]), ([T, E, E, E, T, F, E, E, T, E, F, E, F], [T, E, E, E, T, F, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_637 (And.intro z_660 (And.intro z_674 trivial)))

theorem z_676 : le (tf [T, E, E, E, T, T, F, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, T, F, E, E, E, F, E, F] [([E, T, E, E, T, T, F, E, E, E, F, E, F], [E, T, E, E, T, T, F, E, E, F, E, E, F]), ([T, E, E, E, T, E, F, T, E, E, F, E, F], [T, E, E, E, T, F, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_638 (And.intro z_675 trivial))

theorem z_677 : le (tf [T, E, F, E, E, T, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, E, E, E, T, E, F, F] [([E, T, F, E, E, T, E, E, E, T, E, F, F], [E, T, F, E, E, T, E, E, E, T, F, E, F]), ([T, E, F, E, E, E, T, E, E, T, E, F, F], [T, E, F, E, E, E, T, E, E, T, F, E, F]), ([T, E, F, E, E, T, E, E, E, E, T, F, F], [T, E, F, E, E, T, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_572 (And.intro z_658 (And.intro z_671 trivial)))

theorem z_678 : le (tf [T, E, E, F, E, T, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, E, E, T, E, E, F, F] [([E, T, E, F, E, T, E, E, T, E, E, F, F], [E, T, F, E, E, T, E, E, T, E, E, F, F]), ([T, E, E, F, E, E, T, E, T, E, E, F, F], [T, E, E, F, E, E, T, E, T, E, F, E, F]), ([T, E, E, F, E, T, E, E, E, T, E, F, F], [T, E, F, E, E, T, E, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_573 (And.intro z_659 (And.intro z_677 trivial)))

theorem z_679 : le (tf [T, E, F, E, E, T, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, E, E, E, E, F, T, F] [([E, T, F, E, E, T, E, E, E, E, F, T, F], [F, T, E, E, E, T, E, E, E, E, F, T, F]), ([T, E, F, E, E, E, T, E, E, E, F, T, F], [T, F, E, E, E, E, T, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_571 (And.intro z_657 trivial))

theorem z_680 : le (tf [T, E, E, F, E, T, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, E, E, E, T, F, E, F] [([E, T, E, F, E, T, E, E, E, T, F, E, F], [E, T, F, E, E, T, E, E, E, T, F, E, F]), ([T, E, E, F, E, E, T, E, E, T, F, E, F], [T, E, F, E, E, E, T, E, E, T, F, E, F]), ([T, E, E, F, E, T, E, E, E, E, F, T, F], [T, E, F, E, E, T, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_572 (And.intro z_658 (And.intro z_679 trivial)))

theorem z_681 : le (tf [E, T, F, T, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, E, E, E, F, E, T, F] [([E, T, F, E, T, E, E, E, E, F, E, T, F], [E, T, F, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_590 trivial)

theorem z_682 : le (tf [T, E, F, T, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, F, T, E, E, E, E, E, E, F, T, F] [([E, T, F, T, E, E, E, E, E, E, F, T, F], [E, T, F, T, E, E, E, E, E, F, E, T, F]), ([T, E, F, E, T, E, E, E, E, E, F, T, F], [T, E, F, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_681 (And.intro z_672 trivial))

theorem z_683 : le (tf [T, E, E, T, F, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, E, E, E, T, F, E, F] [([E, T, E, T, F, E, E, E, E, T, F, E, F], [E, T, E, T, F, E, E, E, F, T, E, E, F]), ([T, E, E, E, F, T, E, E, E, T, F, E, F], [T, E, E, F, E, T, E, E, E, T, F, E, F]), ([T, E, E, T, F, E, E, E, E, E, F, T, F], [T, E, F, T, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_583 (And.intro z_680 (And.intro z_682 trivial)))

theorem z_684 : le (tf [T, E, E, T, F, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, E, E, T, E, E, F, F] [([E, T, E, T, F, E, E, E, T, E, E, F, F], [E, T, E, T, F, E, E, E, T, E, F, E, F]), ([T, E, E, E, F, T, E, E, T, E, E, F, F], [T, E, E, F, E, T, E, E, T, E, E, F, F]), ([T, E, E, T, F, E, E, E, E, T, E, F, F], [T, E, E, T, F, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_584 (And.intro z_678 (And.intro z_683 trivial)))

theorem z_685 : le (tf [T, E, E, T, E, F, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, F, E, T, E, E, E, F, F] [([E, T, E, T, E, F, E, T, E, E, E, F, F], [E, T, E, T, F, E, E, T, E, E, E, F, F]), ([T, E, E, E, T, F, E, T, E, E, E, F, F], [T, E, E, E, T, F, E, T, E, E, F, E, F]), ([T, E, E, T, E, F, E, E, T, E, E, F, F], [T, E, E, T, F, E, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_585 (And.intro z_675 (And.intro z_684 trivial)))

theorem z_686 : le (tf [T, E, E, T, E, T, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, T, F, E, E, E, E, F, F] [([E, T, E, T, E, T, F, E, E, E, E, F, F], [E, T, E, T, F, T, E, E, E, E, E, F, F]), ([T, E, E, E, T, T, F, E, E, E, E, F, F], [T, E, E, E, T, T, F, E, E, E, F, E, F]), ([T, E, E, T, E, E, F, T, E, E, E, F, F], [T, E, E, T, E, F, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_545 (And.intro z_676 (And.intro z_685 trivial)))

theorem z_687 : le (tf [T, E, E, T, T, E, E, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, T, E, E, F, E, E, E, F, F] [([E, T, E, T, T, E, E, F, E, E, E, F, F], [E, T, E, T, T, E, F, E, E, E, E, F, F]), ([T, E, E, T, E, T, E, F, E, E, E, F, F], [T, E, E, T, E, T, F, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_546 (And.intro z_686 trivial))

theorem z_688 : le (tf [E, T, T, E, F, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, F, E, E, E, T, F, E, E, F] [([E, T, E, T, F, E, E, E, T, F, E, E, F], [E, T, E, T, F, E, E, F, T, E, E, E, F]), ([E, T, T, E, F, E, E, E, E, F, T, E, F], [E, T, T, F, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_542 (And.intro z_594 trivial))

theorem z_689 : le (tf [E, T, T, E, F, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, F, E, E, T, E, E, F, E, F] [([E, T, E, T, F, E, E, T, E, E, F, E, F], [E, T, E, T, F, E, E, T, E, F, E, E, F]), ([E, T, T, E, F, E, E, E, T, E, F, E, F], [E, T, T, E, F, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_543 (And.intro z_688 trivial))

theorem z_690 : le (tf [E, T, T, E, E, F, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, F, T, E, E, E, F, E, F] [([E, T, E, T, E, F, T, E, E, E, F, E, F], [E, T, E, T, F, E, T, E, E, E, F, E, F]), ([E, T, T, E, E, F, E, T, E, E, F, E, F], [E, T, T, E, F, E, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_544 (And.intro z_689 trivial))

theorem z_691 : le (tf [E, E, E, T, T, F, T, F, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, T, F, E, E, E, F, E] [([E, E, E, T, T, F, E, F, T, E, E, F, E], [E, E, E, T, T, F, F, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_605 trivial)

theorem z_692 : le (tf [E, E, T, E, T, F, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, T, F, E, E, E, E, F] [([E, E, E, T, T, F, T, F, E, E, E, E, F], [E, E, E, T, T, F, T, F, E, E, E, F, E]), ([E, E, T, E, T, F, E, F, T, E, E, E, F], [E, E, T, F, T, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_691 (And.intro z_630 trivial))

theorem z_693 : le (tf [E, E, E, F, E, T, T, T, F, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, T, F, F, E, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_694 : le (tf [E, E, E, T, F, E, T, T, F, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, T, F, F, E, E, E] [([E, E, E, E, F, T, T, T, F, F, E, E, E], [E, E, E, F, E, T, T, T, F, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_693 trivial)

theorem z_695 : le (tf [E, E, E, T, T, F, E, T, F, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, E, T, F, F, E, E, E] [([E, E, E, T, E, F, T, T, F, F, E, E, E], [E, E, E, T, F, E, T, T, F, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_694 trivial)

theorem z_696 : le (tf [F, E, E, E, E, T, T, E, F, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, E, F, E, F, T, E] [([F, E, E, E, E, T, E, T, F, E, F, T, E], [F, E, E, E, E, T, F, T, E, E, F, T, E]), ([F, E, E, E, E, T, T, E, F, E, F, E, T], [F, E, E, E, E, T, T, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_451 (And.intro z_79 trivial))

theorem z_697 : le (tf [E, F, E, E, E, T, T, E, F, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, E, F, T, F, E, E] [([E, F, E, E, E, T, E, T, F, T, F, E, E], [E, F, E, E, E, T, F, T, E, T, F, E, E]), ([E, F, E, E, E, T, T, E, F, E, F, T, E], [F, E, E, E, E, T, T, E, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_452 (And.intro z_696 trivial))

theorem z_698 : le (tf [F, E, E, E, T, E, T, E, F, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, F, E, F, E, T] [([F, E, E, E, E, T, T, E, F, E, F, E, T], [F, E, E, E, E, T, T, F, E, E, F, E, T]), ([F, E, E, E, T, E, E, T, F, E, F, E, T], [F, E, E, E, T, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 (And.intro z_460 trivial))

theorem z_699 : le (tf [E, F, E, E, T, E, T, E, F, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, F, E, F, T, E] [([E, F, E, E, E, T, T, E, F, E, F, T, E], [F, E, E, E, E, T, T, E, F, E, F, T, E]), ([E, F, E, E, T, E, E, T, F, E, F, T, E], [E, F, E, E, T, E, F, T, E, E, F, T, E]), ([E, F, E, E, T, E, T, E, F, E, F, E, T], [F, E, E, E, T, E, T, E, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_696 (And.intro z_461 (And.intro z_698 trivial)))

theorem z_700 : le (tf [E, E, F, E, T, E, T, E, F, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, E, F, T, F, E, E] [([E, E, F, E, E, T, T, E, F, T, F, E, E], [E, F, E, E, E, T, T, E, F, T, F, E, E]), ([E, E, F, E, T, E, E, T, F, T, F, E, E], [E, E, F, E, T, E, F, T, E, T, F, E, E]), ([E, E, F, E, T, E, T, E, F, E, F, T, E], [E, F, E, E, T, E, T, E, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_697 (And.intro z_462 (And.intro z_699 trivial)))

theorem z_701 : le (tf [F, E, E, E, T, E, T, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, E, F, T, E] [([F, E, E, E, E, T, T, F, E, E, F, T, E], [F, E, E, E, E, T, T, F, E, F, E, T, E]), ([F, E, E, E, T, E, E, F, T, E, F, T, E], [F, E, E, E, T, E, F, E, T, E, F, T, E]), ([F, E, E, E, T, E, T, F, E, E, F, E, T], [F, E, E, E, T, E, T, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 (And.intro z_458 (And.intro z_241 trivial)))

theorem z_702 : le (tf [F, E, E, T, E, E, F, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, T, E, F, E, T] [([F, E, E, E, T, E, F, E, T, E, F, E, T], [F, E, E, E, T, E, F, E, T, F, E, E, T]), ([F, E, E, T, E, E, F, E, E, T, F, E, T], [F, E, E, T, E, F, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_238 (And.intro z_320 trivial))

theorem z_703 : le (tf [F, E, E, T, E, E, T, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, F, E, E, F, E, T] [([F, E, E, E, T, E, T, F, E, E, F, E, T], [F, E, E, E, T, E, T, F, E, F, E, E, T]), ([F, E, E, T, E, E, E, F, T, E, F, E, T], [F, E, E, T, E, E, F, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_241 (And.intro z_702 trivial))

theorem z_704 : le (tf [F, E, E, T, E, E, T, E, F, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, E, F, E, F, T, E] [([F, E, E, E, T, E, T, E, F, E, F, T, E], [F, E, E, E, T, E, T, F, E, E, F, T, E]), ([F, E, E, T, E, E, E, T, F, E, F, T, E], [F, E, E, T, E, E, F, T, E, E, F, T, E]), ([F, E, E, T, E, E, T, E, F, E, F, E, T], [F, E, E, T, E, E, T, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_701 (And.intro z_470 (And.intro z_703 trivial)))

theorem z_705 : le (tf [F, E, T, E, E, E, T, E, F, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, T, E, F, E, F, E, T] [([F, E, E, T, E, E, T, E, F, E, F, E, T], [F, E, E, T, E, E, T, F, E, E, F, E, T]), ([F, E, T, E, E, E, E, T, F, E, F, E, T], [F, E, T, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_703 (And.intro z_471 trivial))

theorem z_706 : le (tf [E, F, T, E, E, E, T, E, F, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, E, F, E, F, T, E] [([E, F, E, T, E, E, T, E, F, E, F, T, E], [F, E, E, T, E, E, T, E, F, E, F, T, E]), ([E, F, T, E, E, E, E, T, F, E, F, T, E], [E, F, T, E, E, E, F, T, E, E, F, T, E]), ([E, F, T, E, E, E, T, E, F, E, F, E, T], [F, E, T, E, E, E, T, E, F, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_704 (And.intro z_472 (And.intro z_705 trivial)))

theorem z_707 : le (tf [E, E, T, F, E, E, T, E, F, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, E, F, T, F, E, E] [([E, E, E, F, T, E, T, E, F, T, F, E, E], [E, E, F, E, T, E, T, E, F, T, F, E, E]), ([E, E, T, F, E, E, E, T, F, T, F, E, E], [E, E, T, F, E, E, F, T, E, T, F, E, E]), ([E, E, T, F, E, E, T, E, F, E, F, T, E], [E, F, T, E, E, E, T, E, F, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_700 (And.intro z_473 (And.intro z_706 trivial)))

theorem z_708 : le (tf [E, E, T, E, F, E, T, T, F, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, T, F, E, F, E, E] [([E, E, E, T, F, E, T, T, F, E, F, E, E], [E, E, E, T, F, E, T, T, F, F, E, E, E]), ([E, E, T, E, F, E, T, E, F, T, F, E, E], [E, E, T, F, E, E, T, E, F, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_694 (And.intro z_707 trivial))

theorem z_709 : le (tf [F, E, E, T, E, E, E, F, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, T, E, F, T, E] [([F, E, E, E, T, E, E, F, T, E, F, T, E], [F, E, E, E, T, E, F, E, T, E, F, T, E]), ([F, E, E, T, E, E, E, F, E, T, F, T, E], [F, E, E, T, E, E, F, E, E, T, F, T, E]), ([F, E, E, T, E, E, E, F, T, E, F, E, T], [F, E, E, T, E, E, F, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_458 (And.intro z_321 (And.intro z_702 trivial)))

theorem z_710 : le (tf [E, F, E, T, E, E, E, F, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, T, T, F, E, E] [([E, F, E, E, T, E, E, F, T, T, F, E, E], [F, E, E, E, T, E, E, F, T, T, F, E, E]), ([E, F, E, T, E, E, E, F, T, E, F, T, E], [F, E, E, T, E, E, E, F, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_377 (And.intro z_709 trivial))

theorem z_711 : le (tf [E, F, E, T, E, E, T, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, E, F, T, E] [([E, F, E, E, T, E, T, F, E, E, F, T, E], [F, E, E, E, T, E, T, F, E, E, F, T, E]), ([E, F, E, T, E, E, E, F, T, E, F, T, E], [F, E, E, T, E, E, E, F, T, E, F, T, E]), ([E, F, E, T, E, E, T, F, E, E, F, E, T], [F, E, E, T, E, E, T, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_701 (And.intro z_709 (And.intro z_703 trivial)))

theorem z_712 : le (tf [E, E, F, T, E, E, T, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, T, F, E, T, F, E, E] [([E, E, F, E, T, E, T, F, E, T, F, E, E], [E, F, E, E, T, E, T, F, E, T, F, E, E]), ([E, E, F, T, E, E, E, F, T, T, F, E, E], [E, F, E, T, E, E, E, F, T, T, F, E, E]), ([E, E, F, T, E, E, T, F, E, E, F, T, E], [E, F, E, T, E, E, T, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_378 (And.intro z_710 (And.intro z_711 trivial)))

theorem z_713 : le (tf [F, E, E, E, F, E, T, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, T, E, F, E, T] [([F, E, E, E, F, E, E, T, T, E, F, E, T], [F, E, E, E, F, E, E, T, T, F, E, E, T]), ([F, E, E, E, F, E, T, E, E, T, F, E, T], [F, E, E, F, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_222 (And.intro z_75 trivial))

theorem z_714 : le (tf [F, E, E, E, E, F, T, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, E, F, T, E] [([F, E, E, E, E, F, E, T, T, E, F, T, E], [F, E, E, E, E, F, E, T, T, F, E, T, E]), ([F, E, E, E, E, F, T, E, E, T, F, T, E], [F, E, E, E, F, E, T, E, E, T, F, T, E]), ([F, E, E, E, E, F, T, E, T, E, F, E, T], [F, E, E, E, F, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 (And.intro z_120 (And.intro z_713 trivial)))

theorem z_715 : le (tf [F, E, E, E, E, E, T, F, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, T, F, E, E] [([F, E, E, E, E, E, T, F, T, E, F, T, E], [F, E, E, E, E, F, T, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_714 trivial)

theorem z_716 : le (tf [F, E, E, E, E, T, E, F, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, F, T, E] [([F, E, E, E, E, E, T, F, T, E, F, T, E], [F, E, E, E, E, F, T, E, T, E, F, T, E]), ([F, E, E, E, E, T, E, F, E, T, F, T, E], [F, E, E, E, E, T, F, E, E, T, F, T, E]), ([F, E, E, E, E, T, E, F, T, E, F, E, T], [F, E, E, E, E, T, F, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_714 (And.intro z_116 (And.intro z_78 trivial)))

theorem z_717 : le (tf [E, F, E, E, E, T, E, F, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, T, T, F, E, E] [([E, F, E, E, E, E, T, F, T, T, F, E, E], [F, E, E, E, E, E, T, F, T, T, F, E, E]), ([E, F, E, E, E, T, E, F, T, E, F, T, E], [F, E, E, E, E, T, E, F, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_715 (And.intro z_716 trivial))

theorem z_718 : le (tf [F, E, E, E, F, E, T, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, F, T, T] [([F, E, E, E, F, E, E, T, E, E, F, T, T], [F, E, E, F, E, E, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_71 trivial)

theorem z_719 : le (tf [F, E, E, E, T, F, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, F, T, T] [([F, E, E, E, E, F, T, E, E, E, F, T, T], [F, E, E, E, F, E, T, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_718 trivial)

theorem z_720 : le (tf [F, E, E, E, T, E, F, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, F, E, T] [([F, E, E, E, E, T, F, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, T]), ([F, E, E, E, T, E, F, E, E, E, F, T, T], [F, E, E, E, T, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 (And.intro z_719 trivial))

theorem z_721 : le (tf [F, E, E, E, T, E, E, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, F, T, E] [([F, E, E, E, E, T, E, F, E, T, F, T, E], [F, E, E, E, E, T, F, E, E, T, F, T, E]), ([F, E, E, E, T, E, E, F, E, T, F, E, T], [F, E, E, E, T, E, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_116 (And.intro z_720 trivial))

theorem z_722 : le (tf [F, E, E, E, T, E, E, F, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, F, E, T] [([F, E, E, E, E, T, E, F, T, E, F, E, T], [F, E, E, E, E, T, F, E, T, E, F, E, T]), ([F, E, E, E, T, E, E, F, E, T, F, E, T], [F, E, E, E, T, E, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_78 (And.intro z_720 trivial))

theorem z_723 : le (tf [E, F, E, E, T, E, E, F, T, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, E, F, T, E] [([E, F, E, E, E, T, E, F, T, E, F, T, E], [F, E, E, E, E, T, E, F, T, E, F, T, E]), ([E, F, E, E, T, E, E, F, E, T, F, T, E], [F, E, E, E, T, E, E, F, E, T, F, T, E]), ([E, F, E, E, T, E, E, F, T, E, F, E, T], [F, E, E, E, T, E, E, F, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_716 (And.intro z_721 (And.intro z_722 trivial)))

theorem z_724 : le (tf [E, E, F, E, T, E, E, F, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, F, T, T, F, E, E] [([E, E, F, E, E, T, E, F, T, T, F, E, E], [E, F, E, E, E, T, E, F, T, T, F, E, E]), ([E, E, F, E, T, E, E, F, T, E, F, T, E], [E, F, E, E, T, E, E, F, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_717 (And.intro z_723 trivial))

theorem z_725 : le (tf [F, E, T, E, E, E, E, F, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, T, E, F, E, T] [([F, E, E, T, E, E, E, F, T, E, F, E, T], [F, E, E, T, E, E, F, E, T, E, F, E, T]), ([F, E, T, E, E, E, E, F, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_702 (And.intro z_360 trivial))

theorem z_726 : le (tf [E, F, T, E, E, E, E, F, T, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, T, E, F, T, E] [([E, F, E, T, E, E, E, F, T, E, F, T, E], [F, E, E, T, E, E, E, F, T, E, F, T, E]), ([E, F, T, E, E, E, E, F, E, T, F, T, E], [F, E, T, E, E, E, E, F, E, T, F, T, E]), ([E, F, T, E, E, E, E, F, T, E, F, E, T], [F, E, T, E, E, E, E, F, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_709 (And.intro z_361 (And.intro z_725 trivial)))

theorem z_727 : le (tf [E, E, T, F, E, E, E, F, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, F, T, T, F, E, E] [([E, E, E, F, T, E, E, F, T, T, F, E, E], [E, E, F, E, T, E, E, F, T, T, F, E, E]), ([E, E, T, F, E, E, E, F, T, E, F, T, E], [E, F, T, E, E, E, E, F, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_724 (And.intro z_726 trivial))

theorem z_728 : le (tf [E, F, E, E, E, T, T, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, F, T, E] [([E, F, E, E, E, T, E, F, T, E, F, T, E], [F, E, E, E, E, T, E, F, T, E, F, T, E]), ([E, F, E, E, E, T, T, F, E, E, F, E, T], [F, E, E, E, E, T, T, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_716 (And.intro z_79 trivial))

theorem z_729 : le (tf [E, F, E, E, T, E, T, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, F, E, T] [([E, F, E, E, E, T, T, F, E, E, F, E, T], [F, E, E, E, E, T, T, F, E, E, F, E, T]), ([E, F, E, E, T, E, E, F, T, E, F, E, T], [F, E, E, E, T, E, E, F, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 (And.intro z_722 trivial))

theorem z_730 : le (tf [E, E, F, E, T, E, T, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, E, F, T, E] [([E, E, F, E, E, T, T, F, E, E, F, T, E], [E, F, E, E, E, T, T, F, E, E, F, T, E]), ([E, E, F, E, T, E, E, F, T, E, F, T, E], [E, F, E, E, T, E, E, F, T, E, F, T, E]), ([E, E, F, E, T, E, T, F, E, E, F, E, T], [E, F, E, E, T, E, T, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_728 (And.intro z_723 (And.intro z_729 trivial)))

theorem z_731 : le (tf [E, F, T, E, E, E, T, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, F, E, E, F, E, T] [([E, F, E, T, E, E, T, F, E, E, F, E, T], [F, E, E, T, E, E, T, F, E, E, F, E, T]), ([E, F, T, E, E, E, E, F, T, E, F, E, T], [F, E, T, E, E, E, E, F, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_703 (And.intro z_725 trivial))

theorem z_732 : le (tf [E, E, T, F, E, E, T, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, E, F, T, E] [([E, E, E, F, T, E, T, F, E, E, F, T, E], [E, E, F, E, T, E, T, F, E, E, F, T, E]), ([E, E, T, F, E, E, E, F, T, E, F, T, E], [E, F, T, E, E, E, E, F, T, E, F, T, E]), ([E, E, T, F, E, E, T, F, E, E, F, E, T], [E, F, T, E, E, E, T, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_730 (And.intro z_726 (And.intro z_731 trivial)))

theorem z_733 : le (tf [E, E, T, E, F, E, T, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, F, E, T, F, E, E] [([E, E, E, T, F, E, T, F, E, T, F, E, E], [E, E, F, T, E, E, T, F, E, T, F, E, E]), ([E, E, T, E, F, E, E, F, T, T, F, E, E], [E, E, T, F, E, E, E, F, T, T, F, E, E]), ([E, E, T, E, F, E, T, F, E, E, F, T, E], [E, E, T, F, E, E, T, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_712 (And.intro z_727 (And.intro z_732 trivial)))

theorem z_734 : le (tf [E, F, E, E, T, T, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, E, F, E, T] [([E, F, E, E, T, E, F, T, E, E, F, E, T], [F, E, E, E, T, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_460 trivial)

theorem z_735 : le (tf [E, E, F, E, T, T, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, E, F, T, E] [([E, E, F, E, T, E, F, T, E, E, F, T, E], [E, F, E, E, T, E, F, T, E, E, F, T, E]), ([E, E, F, E, T, T, F, E, E, E, F, E, T], [E, F, E, E, T, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_461 (And.intro z_734 trivial))

theorem z_736 : le (tf [E, F, T, E, E, T, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, F, E, E, E, F, E, T] [([E, F, E, T, E, T, F, E, E, E, F, E, T], [F, E, E, T, E, T, F, E, E, E, F, E, T]), ([E, F, T, E, E, E, F, T, E, E, F, E, T], [F, E, T, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_624 (And.intro z_471 trivial))

theorem z_737 : le (tf [E, E, T, F, E, T, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, E, F, T, E] [([E, E, E, F, T, T, F, E, E, E, F, T, E], [E, E, F, E, T, T, F, E, E, E, F, T, E]), ([E, E, T, F, E, E, F, T, E, E, F, T, E], [E, F, T, E, E, E, F, T, E, E, F, T, E]), ([E, E, T, F, E, T, F, E, E, E, F, E, T], [E, F, T, E, E, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_735 (And.intro z_472 (And.intro z_736 trivial)))

theorem z_738 : le (tf [F, E, E, T, T, E, E, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, T, E, E, F, E, E, F, E, T] [([F, E, E, T, E, T, E, F, E, E, F, E, T], [F, E, E, T, E, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_624 trivial)

theorem z_739 : le (tf [E, F, T, E, T, E, E, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, T, E, E, F, E, E, F, E, T] [([E, F, E, T, T, E, E, F, E, E, F, E, T], [F, E, E, T, T, E, E, F, E, E, F, E, T]), ([E, F, T, E, E, T, E, F, E, E, F, E, T], [E, F, T, E, E, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_738 (And.intro z_736 trivial))

theorem z_740 : le (tf [E, E, T, F, T, E, E, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, F, E, E, F, T, E] [([E, E, T, F, E, T, E, F, E, E, F, T, E], [E, E, T, F, E, T, F, E, E, E, F, T, E]), ([E, E, T, F, T, E, E, F, E, E, F, E, T], [E, F, T, E, T, E, E, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_737 (And.intro z_739 trivial))

theorem z_741 : le (tf [E, E, T, E, T, F, E, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, F, E, T, F, E, E] [([E, E, E, T, T, F, E, F, E, T, F, E, E], [E, E, E, T, T, F, F, E, E, T, F, E, E]), ([E, E, T, E, E, F, T, F, E, T, F, E, E], [E, E, T, E, F, E, T, F, E, T, F, E, E]), ([E, E, T, E, T, F, E, F, E, E, F, T, E], [E, E, T, F, T, E, E, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_604 (And.intro z_733 (And.intro z_740 trivial)))

theorem z_742 : le (tf [E, E, T, E, T, F, E, T, F, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, T, F, E, F, E, E] [([E, E, E, T, T, F, E, T, F, E, F, E, E], [E, E, E, T, T, F, E, T, F, F, E, E, E]), ([E, E, T, E, E, F, T, T, F, E, F, E, E], [E, E, T, E, F, E, T, T, F, E, F, E, E]), ([E, E, T, E, T, F, E, E, F, T, F, E, E], [E, E, T, E, T, F, E, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_695 (And.intro z_708 (And.intro z_741 trivial)))

theorem z_743 : le (tf [F, E, E, T, E, E, F, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, T, E, E, E, F, T] [([F, E, E, E, T, E, F, T, E, E, E, F, T], [F, E, E, E, T, F, E, T, E, E, E, F, T]), ([F, E, E, T, E, E, F, E, T, E, E, F, T], [F, E, E, T, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_331 (And.intro z_209 trivial))

theorem z_744 : le (tf [E, F, E, T, E, E, F, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, T, E, E, T, F, E] [([E, F, E, E, T, E, F, T, E, E, T, F, E], [E, F, E, E, T, F, E, T, E, E, T, F, E]), ([E, F, E, T, E, E, F, E, T, E, T, F, E], [E, F, E, T, E, F, E, E, T, E, T, F, E]), ([E, F, E, T, E, E, F, T, E, E, E, F, T], [F, E, E, T, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_332 (And.intro z_210 (And.intro z_743 trivial)))

theorem z_745 : le (tf [E, F, E, T, E, E, E, T, F, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, F, T, E, F, E] [([E, F, E, E, T, E, E, T, F, T, E, F, E], [E, F, E, E, T, E, F, T, E, T, E, F, E]), ([E, F, E, T, E, E, E, T, F, E, T, F, E], [E, F, E, T, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_456 (And.intro z_744 trivial))

theorem z_746 : le (tf [F, E, T, F, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, E, F, T, E, T] [([F, E, E, F, T, E, E, E, E, F, T, E, T], [F, E, F, E, T, E, E, E, E, F, T, E, T]), ([F, E, T, F, E, E, E, E, E, F, E, T, T], [F, E, T, F, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_154 (And.intro z_298 trivial))

theorem z_747 : le (tf [F, T, E, F, E, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, E, E, E, E, T, F, T] [([F, E, T, F, E, E, E, E, E, E, T, F, T], [F, E, T, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_746 trivial)

theorem z_748 : le (tf [F, T, E, E, F, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, E, E, T, E, F, T] [([F, E, T, E, F, E, E, E, E, T, E, F, T], [F, E, T, E, F, E, E, E, E, T, F, E, T]), ([F, T, E, E, F, E, E, E, E, E, T, F, T], [F, T, E, F, E, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_643 (And.intro z_747 trivial))

theorem z_749 : le (tf [E, T, F, E, F, E, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, E, E, T, T, F, E] [([E, E, F, T, F, E, E, E, E, T, T, F, E], [E, F, E, T, F, E, E, E, E, T, T, F, E]), ([E, T, F, E, F, E, E, E, E, T, E, F, T], [F, T, E, E, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_206 (And.intro z_748 trivial))

theorem z_750 : le (tf [F, E, E, T, F, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, T, E, F, E, T] [([F, E, E, E, F, T, E, E, T, E, F, E, T], [F, E, E, E, F, T, E, E, T, F, E, E, T]), ([F, E, E, T, F, E, E, E, E, T, F, E, T], [F, E, E, T, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_227 (And.intro z_296 trivial))

theorem z_751 : le (tf [F, E, T, E, F, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, T, E, E, F, T] [([F, E, E, T, F, E, E, E, T, E, E, F, T], [F, E, E, T, F, E, E, E, T, E, F, E, T]), ([F, E, T, E, F, E, E, E, E, T, E, F, T], [F, E, T, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_750 (And.intro z_643 trivial))

theorem z_752 : le (tf [F, T, E, E, E, F, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, T, E, E, F, T] [([F, E, T, E, E, F, E, E, T, E, E, F, T], [F, E, T, E, F, E, E, E, T, E, E, F, T]), ([F, T, E, E, E, F, E, E, E, T, E, F, T], [F, T, E, E, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_751 (And.intro z_748 trivial))

theorem z_753 : le (tf [E, T, F, E, E, F, E, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, E, T, E, T, F, E] [([E, E, F, T, E, F, E, E, T, E, T, F, E], [E, F, E, T, E, F, E, E, T, E, T, F, E]), ([E, T, F, E, E, F, E, E, E, T, T, F, E], [E, T, F, E, F, E, E, E, E, T, T, F, E]), ([E, T, F, E, E, F, E, E, T, E, E, F, T], [F, T, E, E, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_210 (And.intro z_749 (And.intro z_752 trivial)))

theorem z_754 : le (tf [F, T, E, E, E, E, F, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, T, E, E, E, F, T] [([F, E, T, E, E, E, F, T, E, E, E, F, T], [F, E, T, E, E, E, F, T, E, E, F, E, T]), ([F, T, E, E, E, E, F, E, T, E, E, F, T], [F, T, E, E, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_471 (And.intro z_752 trivial))

theorem z_755 : le (tf [E, T, F, E, E, E, F, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, T, E, E, T, F, E] [([E, E, F, T, E, E, F, T, E, E, T, F, E], [E, F, E, T, E, E, F, T, E, E, T, F, E]), ([E, T, F, E, E, E, F, E, T, E, T, F, E], [E, T, F, E, E, F, E, E, T, E, T, F, E]), ([E, T, F, E, E, E, F, T, E, E, E, F, T], [F, T, E, E, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_744 (And.intro z_753 (And.intro z_754 trivial)))

theorem z_756 : le (tf [E, T, F, E, E, E, E, T, F, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, F, T, E, F, E] [([E, E, F, T, E, E, E, T, F, T, E, F, E], [E, F, E, T, E, E, E, T, F, T, E, F, E]), ([E, T, F, E, E, E, E, T, F, E, T, F, E], [E, T, F, E, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_745 (And.intro z_755 trivial))

theorem z_757 : le (tf [F, E, E, T, E, E, T, E, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, E, F, E, E, F, T] [([F, E, E, E, T, E, T, E, F, E, E, F, T], [F, E, E, E, T, E, T, F, E, E, E, F, T]), ([F, E, E, T, E, E, E, T, F, E, E, F, T], [F, E, E, T, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_197 (And.intro z_743 trivial))

theorem z_758 : le (tf [E, F, E, T, E, E, T, E, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, F, E, T, F, E] [([E, F, E, E, T, E, T, E, F, E, T, F, E], [E, F, E, E, T, E, T, F, E, E, T, F, E]), ([E, F, E, T, E, E, E, T, F, E, T, F, E], [E, F, E, T, E, E, F, T, E, E, T, F, E]), ([E, F, E, T, E, E, T, E, F, E, E, F, T], [F, E, E, T, E, E, T, E, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_198 (And.intro z_744 (And.intro z_757 trivial)))

theorem z_759 : le (tf [F, T, E, E, E, E, T, E, F, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, T, E, F, E, E, F, T] [([F, E, T, E, E, E, T, E, F, E, E, F, T], [F, E, T, E, E, E, T, E, F, E, F, E, T]), ([F, T, E, E, E, E, E, T, F, E, E, F, T], [F, T, E, E, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_705 (And.intro z_754 trivial))

theorem z_760 : le (tf [E, T, F, E, E, E, T, E, F, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, F, E, T, F, E] [([E, E, F, T, E, E, T, E, F, E, T, F, E], [E, F, E, T, E, E, T, E, F, E, T, F, E]), ([E, T, F, E, E, E, E, T, F, E, T, F, E], [E, T, F, E, E, E, F, T, E, E, T, F, E]), ([E, T, F, E, E, E, T, E, F, E, E, F, T], [F, T, E, E, E, E, T, E, F, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_758 (And.intro z_755 (And.intro z_759 trivial)))

theorem z_761 : le (tf [E, T, E, F, E, E, T, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, E, F, T, E, F, E] [([E, E, T, F, E, E, T, E, F, T, E, F, E], [E, E, T, F, E, E, T, F, E, T, E, F, E]), ([E, T, E, F, E, E, E, T, F, T, E, F, E], [E, T, F, E, E, E, E, T, F, T, E, F, E]), ([E, T, E, F, E, E, T, E, F, E, T, F, E], [E, T, F, E, E, E, T, E, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_313 (And.intro z_756 (And.intro z_760 trivial)))

theorem z_762 : le (tf [E, T, E, E, F, E, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, T, F, E, E, F, E] [([E, E, T, E, F, E, T, T, F, E, E, F, E], [E, E, T, F, E, E, T, T, F, E, E, F, E]), ([E, T, E, E, F, E, T, E, F, T, E, F, E], [E, T, E, F, E, E, T, E, F, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_391 (And.intro z_761 trivial))

theorem z_763 : le (tf [F, E, E, T, E, F, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, E, T, F, T] [([F, E, E, E, T, F, E, E, E, E, T, F, T], [F, E, E, F, T, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_191 trivial)

theorem z_764 : le (tf [F, E, E, T, E, E, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, T, E, F, T] [([F, E, E, E, T, E, F, E, E, T, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, F, T]), ([F, E, E, T, E, E, F, E, E, E, T, F, T], [F, E, E, T, E, F, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_192 (And.intro z_763 trivial))

theorem z_765 : le (tf [F, E, E, T, E, E, E, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, T, F, E] [([F, E, E, E, T, E, E, F, E, T, T, F, E], [F, E, E, E, T, E, F, E, E, T, T, F, E]), ([F, E, E, T, E, E, E, F, E, T, E, F, T], [F, E, E, T, E, E, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_193 (And.intro z_764 trivial))

theorem z_766 : le (tf [F, E, E, T, E, E, E, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, T, E, E, F, T] [([F, E, E, E, T, E, E, F, T, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, F, T]), ([F, E, E, T, E, E, E, F, E, T, E, F, T], [F, E, E, T, E, E, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_194 (And.intro z_764 trivial))

theorem z_767 : le (tf [E, F, E, T, E, E, E, F, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, T, E, T, F, E] [([E, F, E, E, T, E, E, F, T, E, T, F, E], [F, E, E, E, T, E, E, F, T, E, T, F, E]), ([E, F, E, T, E, E, E, F, E, T, T, F, E], [F, E, E, T, E, E, E, F, E, T, T, F, E]), ([E, F, E, T, E, E, E, F, T, E, E, F, T], [F, E, E, T, E, E, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_195 (And.intro z_765 (And.intro z_766 trivial)))

theorem z_768 : le (tf [E, F, E, T, E, E, F, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, T, T, F, E] [([E, F, E, E, T, E, F, E, E, T, T, F, E], [F, E, E, E, T, E, F, E, E, T, T, F, E]), ([E, F, E, T, E, E, F, E, E, T, E, F, T], [F, E, E, T, E, E, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_193 (And.intro z_764 trivial))

theorem z_769 : le (tf [F, T, E, E, E, F, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, E, E, T, F, T] [([F, E, T, E, E, F, E, E, E, E, T, F, T], [F, E, T, E, F, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_212 trivial)

theorem z_770 : le (tf [F, T, E, E, E, E, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, T, E, F, T] [([F, E, T, E, E, E, F, E, E, T, E, F, T], [F, E, T, E, E, F, E, E, E, T, E, F, T]), ([F, T, E, E, E, E, F, E, E, E, T, F, T], [F, T, E, E, E, F, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_213 (And.intro z_769 trivial))

theorem z_771 : le (tf [E, T, F, E, E, E, F, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, E, T, T, F, E] [([E, E, F, T, E, E, F, E, E, T, T, F, E], [E, F, E, T, E, E, F, E, E, T, T, F, E]), ([E, T, F, E, E, E, F, E, E, T, E, F, T], [F, T, E, E, E, E, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_768 (And.intro z_770 trivial))

theorem z_772 : le (tf [F, T, E, E, E, E, E, F, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, T, E, E, F, T] [([F, E, T, E, E, E, E, F, T, E, E, F, T], [F, E, T, E, E, E, F, E, T, E, E, F, T]), ([F, T, E, E, E, E, E, F, E, T, E, F, T], [F, T, E, E, E, E, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_215 (And.intro z_770 trivial))

theorem z_773 : le (tf [E, T, F, E, E, E, E, F, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, T, E, T, F, E] [([E, E, F, T, E, E, E, F, T, E, T, F, E], [E, F, E, T, E, E, E, F, T, E, T, F, E]), ([E, T, F, E, E, E, E, F, E, T, T, F, E], [E, T, F, E, E, E, F, E, E, T, T, F, E]), ([E, T, F, E, E, E, E, F, T, E, E, F, T], [F, T, E, E, E, E, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_767 (And.intro z_771 (And.intro z_772 trivial)))

theorem z_774 : le (tf [E, T, E, F, E, E, E, F, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, F, T, T, E, F, E] [([E, E, T, F, E, E, E, F, T, T, E, F, E], [E, F, T, E, E, E, E, F, T, T, E, F, E]), ([E, T, E, F, E, E, E, F, T, E, T, F, E], [E, T, F, E, E, E, E, F, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_217 (And.intro z_773 trivial))

theorem z_775 : le (tf [E, F, E, T, E, E, T, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, E, E, F, T] [([E, F, E, E, T, E, T, F, E, E, E, F, T], [F, E, E, E, T, E, T, F, E, E, E, F, T]), ([E, F, E, T, E, E, E, F, T, E, E, F, T], [F, E, E, T, E, E, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_197 (And.intro z_766 trivial))

theorem z_776 : le (tf [E, T, F, E, E, E, T, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, F, E, E, E, F, T] [([E, E, F, T, E, E, T, F, E, E, E, F, T], [E, F, E, T, E, E, T, F, E, E, E, F, T]), ([E, T, F, E, E, E, E, F, T, E, E, F, T], [F, T, E, E, E, E, E, F, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_775 (And.intro z_772 trivial))

theorem z_777 : le (tf [E, T, E, F, E, E, T, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, F, E, E, T, F, E] [([E, E, T, F, E, E, T, F, E, E, T, F, E], [E, E, T, F, E, E, T, F, E, F, T, E, E]), ([E, T, E, F, E, E, E, F, T, E, T, F, E], [E, T, F, E, E, E, E, F, T, E, T, F, E]), ([E, T, E, F, E, E, T, F, E, E, E, F, T], [E, T, F, E, E, E, T, F, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_312 (And.intro z_773 (And.intro z_776 trivial)))

theorem z_778 : le (tf [E, T, E, E, F, E, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, F, E, T, E, F, E] [([E, E, T, E, F, E, T, F, E, T, E, F, E], [E, E, T, F, E, E, T, F, E, T, E, F, E]), ([E, T, E, E, F, E, E, F, T, T, E, F, E], [E, T, E, F, E, E, E, F, T, T, E, F, E]), ([E, T, E, E, F, E, T, F, E, E, T, F, E], [E, T, E, F, E, E, T, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_313 (And.intro z_774 (And.intro z_777 trivial)))

theorem z_779 : le (tf [E, F, E, T, E, T, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, F, E, E, E, E, F, T] [([E, F, E, E, T, T, F, E, E, E, E, F, T], [F, E, E, E, T, T, F, E, E, E, E, F, T]), ([E, F, E, T, E, E, F, T, E, E, E, F, T], [F, E, E, T, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_382 (And.intro z_743 trivial))

theorem z_780 : le (tf [E, T, F, E, E, T, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, F, E, E, E, E, F, T] [([E, E, F, T, E, T, F, E, E, E, E, F, T], [E, F, E, T, E, T, F, E, E, E, E, F, T]), ([E, T, F, E, E, E, F, T, E, E, E, F, T], [F, T, E, E, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_779 (And.intro z_754 trivial))

theorem z_781 : le (tf [E, T, E, F, E, T, F, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, F, E, E, E, T, F, E] [([E, E, T, F, E, T, F, E, E, E, T, F, E], [E, E, T, F, E, T, F, E, E, F, T, E, E]), ([E, T, E, F, E, E, F, T, E, E, T, F, E], [E, T, F, E, E, E, F, T, E, E, T, F, E]), ([E, T, E, F, E, T, F, E, E, E, E, F, T], [E, T, F, E, E, T, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_498 (And.intro z_755 (And.intro z_780 trivial)))

theorem z_782 : le (tf [E, F, E, T, T, E, E, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, F, E, E, E, F, T] [([E, F, E, T, E, T, E, F, E, E, E, F, T], [E, F, E, T, E, T, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_779 trivial)

theorem z_783 : le (tf [E, T, F, E, T, E, E, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, F, E, E, E, F, T] [([E, E, F, T, T, E, E, F, E, E, E, F, T], [E, F, E, T, T, E, E, F, E, E, E, F, T]), ([E, T, F, E, E, T, E, F, E, E, E, F, T], [E, T, F, E, E, T, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_782 (And.intro z_780 trivial))

theorem z_784 : le (tf [E, T, E, F, T, E, E, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, T, E, E, F, E, E, T, F, E] [([E, E, T, F, T, E, E, F, E, E, T, F, E], [E, E, T, F, T, E, F, E, E, E, T, F, E]), ([E, T, E, F, E, T, E, F, E, E, T, F, E], [E, T, E, F, E, T, F, E, E, E, T, F, E]), ([E, T, E, F, T, E, E, F, E, E, E, F, T], [E, T, F, E, T, E, E, F, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_628 (And.intro z_781 (And.intro z_783 trivial)))

theorem z_785 : le (tf [E, T, E, E, T, F, E, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, F, E, T, E, F, E] [([E, E, T, E, T, F, E, F, E, T, E, F, E], [E, E, T, E, T, F, E, F, E, T, F, E, E]), ([E, T, E, E, E, F, T, F, E, T, E, F, E], [E, T, E, E, F, E, T, F, E, T, E, F, E]), ([E, T, E, E, T, F, E, F, E, E, T, F, E], [E, T, E, F, T, E, E, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_741 (And.intro z_778 (And.intro z_784 trivial)))

theorem z_786 : le (tf [E, T, E, E, T, F, E, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, T, F, E, E, F, E] [([E, E, T, E, T, F, E, T, F, E, E, F, E], [E, E, T, E, T, F, E, T, F, E, F, E, E]), ([E, T, E, E, E, F, T, T, F, E, E, F, E], [E, T, E, E, F, E, T, T, F, E, E, F, E]), ([E, T, E, E, T, F, E, E, F, T, E, F, E], [E, T, E, E, T, F, E, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_742 (And.intro z_762 (And.intro z_785 trivial)))

theorem z_787 : le (tf [E, T, E, E, T, F, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, T, E, F, E, E, E, F] [([E, E, T, E, T, F, T, E, F, E, E, E, F], [E, E, T, E, T, F, T, F, E, E, E, E, F]), ([E, T, E, E, T, F, E, T, F, E, E, E, F], [E, T, E, E, T, F, E, T, F, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_692 (And.intro z_786 trivial))

theorem z_788 : le (tf [E, T, E, T, E, F, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, T, E, E, F, E, E, F] [([E, E, T, T, E, F, T, E, E, F, E, E, F], [E, E, T, T, F, E, T, E, E, F, E, E, F]), ([E, T, E, E, T, F, T, E, E, F, E, E, F], [E, T, E, E, T, F, T, E, F, E, E, E, F]), ([E, T, E, T, E, F, E, T, E, F, E, E, F], [E, T, E, T, F, E, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_409 (And.intro z_787 (And.intro z_543 trivial)))

theorem z_789 : le (tf [T, E, F, E, E, E, T, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, T, E, F, E, T, E, F] [([E, T, F, E, E, E, T, E, F, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, T, E, F]), ([T, E, F, E, E, E, E, T, F, E, T, E, F], [T, F, E, E, E, E, E, T, F, E, T, E, F]), ([T, E, F, E, E, E, T, E, F, E, E, T, F], [T, F, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_441 (And.intro z_650 (And.intro z_668 trivial)))

theorem z_790 : le (tf [T, E, E, F, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, E, F, T, E, E, F] [([E, T, E, F, E, E, T, E, F, T, E, E, F], [E, T, F, E, E, E, T, E, F, T, E, E, F]), ([T, E, E, F, E, E, E, T, F, T, E, E, F], [T, E, F, E, E, E, E, T, F, T, E, E, F]), ([T, E, E, F, E, E, T, E, F, E, T, E, F], [T, E, F, E, E, E, T, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_442 (And.intro z_651 (And.intro z_789 trivial)))

theorem z_791 : le (tf [T, E, E, E, F, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, T, F, E, E, E, F] [([E, T, E, E, F, E, T, T, F, E, E, E, F], [E, T, E, F, E, E, T, T, F, E, E, E, F]), ([T, E, E, E, F, E, T, E, F, T, E, E, F], [T, E, E, F, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_443 (And.intro z_790 trivial))

theorem z_792 : le (tf [T, E, F, E, E, E, E, F, T, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, F, T, E, T, E, F] [([E, T, F, E, E, E, E, F, T, E, T, E, F], [E, T, F, E, E, E, F, E, T, E, T, E, F]), ([T, E, F, E, E, E, E, F, E, T, T, E, F], [T, F, E, E, E, E, E, F, E, T, T, E, F]), ([T, E, F, E, E, E, E, F, T, E, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_438 (And.intro z_642 (And.intro z_655 trivial)))

theorem z_793 : le (tf [T, E, E, F, E, E, E, F, T, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, F, T, T, E, E, F] [([E, T, E, F, E, E, E, F, T, T, E, E, F], [E, T, F, E, E, E, E, F, T, T, E, E, F]), ([T, E, E, F, E, E, E, F, T, E, T, E, F], [T, E, F, E, E, E, E, F, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_632 (And.intro z_792 trivial))

theorem z_794 : le (tf [T, E, F, E, E, E, T, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, T, F, E, E, E, T, F] [([E, T, F, E, E, E, T, F, E, E, E, T, F], [E, T, F, E, E, F, T, E, E, E, E, T, F]), ([T, E, F, E, E, E, E, F, T, E, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_440 (And.intro z_655 trivial))

theorem z_795 : le (tf [T, E, E, F, E, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, F, E, E, T, E, F] [([E, T, E, F, E, E, T, F, E, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, T, E, F]), ([T, E, E, F, E, E, E, F, T, E, T, E, F], [T, E, F, E, E, E, E, F, T, E, T, E, F]), ([T, E, E, F, E, E, T, F, E, E, E, T, F], [T, E, F, E, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_441 (And.intro z_792 (And.intro z_794 trivial)))

theorem z_796 : le (tf [T, E, E, E, F, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, F, E, T, E, E, F] [([E, T, E, E, F, E, T, F, E, T, E, E, F], [E, T, E, F, E, E, T, F, E, T, E, E, F]), ([T, E, E, E, F, E, E, F, T, T, E, E, F], [T, E, E, F, E, E, E, F, T, T, E, E, F]), ([T, E, E, E, F, E, T, F, E, E, T, E, F], [T, E, E, F, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_633 (And.intro z_793 (And.intro z_795 trivial)))

theorem z_797 : le (tf [T, F, E, E, E, F, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, E, T, T, E, F] [([E, F, T, E, E, F, E, E, E, T, T, E, F], [F, E, T, E, E, F, E, E, E, T, T, E, F]), ([T, F, E, E, E, F, E, E, E, T, E, T, F], [T, F, E, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 (And.intro z_647 trivial))

theorem z_798 : le (tf [T, F, E, E, E, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, E, T, E, T, E, F] [([E, F, T, E, E, E, F, E, T, E, T, E, F], [E, F, T, E, E, E, F, E, T, E, T, F, E]), ([T, F, E, E, E, E, F, E, E, T, T, E, F], [T, F, E, E, E, F, E, E, E, T, T, E, F]), ([T, F, E, E, E, E, F, E, T, E, E, T, F], [T, F, E, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_216 (And.intro z_797 (And.intro z_648 trivial)))

theorem z_799 : le (tf [T, E, F, E, E, E, F, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, F, T, E, E, T, E, F] [([E, T, F, E, E, E, F, T, E, E, T, E, F], [E, T, F, E, E, F, E, T, E, E, T, E, F]), ([T, E, F, E, E, E, F, E, T, E, T, E, F], [T, F, E, E, E, E, F, E, T, E, T, E, F]), ([T, E, F, E, E, E, F, T, E, E, E, T, F], [T, F, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_428 (And.intro z_798 (And.intro z_649 trivial)))

theorem z_800 : le (tf [T, E, F, E, E, T, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, F, E, E, E, E, T, F] [([E, T, F, E, E, T, F, E, E, E, E, T, F], [E, T, F, E, F, T, E, E, E, E, E, T, F]), ([T, E, F, E, E, E, F, T, E, E, E, T, F], [T, F, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_528 (And.intro z_649 trivial))

theorem z_801 : le (tf [T, E, E, F, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, F, E, E, E, T, E, F] [([E, T, E, F, E, T, F, E, E, E, T, E, F], [E, T, F, E, E, T, F, E, E, E, T, E, F]), ([T, E, E, F, E, E, F, T, E, E, T, E, F], [T, E, F, E, E, E, F, T, E, E, T, E, F]), ([T, E, E, F, E, T, F, E, E, E, E, T, F], [T, E, F, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_529 (And.intro z_799 (And.intro z_800 trivial)))

theorem z_802 : le (tf [T, E, F, E, T, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, T, E, E, F, E, E, E, T, F] [([E, T, F, E, T, E, E, F, E, E, E, T, F], [E, T, F, E, T, E, F, E, E, E, E, T, F]), ([T, E, F, E, E, T, E, F, E, E, E, T, F], [T, E, F, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_579 (And.intro z_800 trivial))

theorem z_803 : le (tf [T, E, E, F, T, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, E, E, F, E, E, T, E, F] [([E, T, E, F, T, E, E, F, E, E, T, E, F], [E, T, F, E, T, E, E, F, E, E, T, E, F]), ([T, E, E, F, E, T, E, F, E, E, T, E, F], [T, E, E, F, E, T, F, E, E, E, T, E, F]), ([T, E, E, F, T, E, E, F, E, E, E, T, F], [T, E, F, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_580 (And.intro z_801 (And.intro z_802 trivial)))

theorem z_804 : le (tf [T, E, E, E, T, F, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, E, F, E, T, E, E, F] [([E, T, E, E, T, F, E, F, E, T, E, E, F], [E, T, E, F, T, E, E, F, E, T, E, E, F]), ([T, E, E, E, E, F, T, F, E, T, E, E, F], [T, E, E, E, F, E, T, F, E, T, E, E, F]), ([T, E, E, E, T, F, E, F, E, E, T, E, F], [T, E, E, F, T, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_635 (And.intro z_796 (And.intro z_803 trivial)))

theorem z_805 : le (tf [T, E, E, E, T, F, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, E, T, F, E, E, E, F] [([E, T, E, E, T, F, E, T, F, E, E, E, F], [E, T, E, E, T, F, E, T, F, E, E, F, E]), ([T, E, E, E, E, F, T, T, F, E, E, E, F], [T, E, E, E, F, E, T, T, F, E, E, E, F]), ([T, E, E, E, T, F, E, E, F, T, E, E, F], [T, E, E, E, T, F, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_786 (And.intro z_791 (And.intro z_804 trivial)))

theorem z_806 : le (tf [T, E, E, E, T, F, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, T, E, E, F, E, E, F] [([E, T, E, E, T, F, T, E, E, F, E, E, F], [E, T, E, E, T, F, T, E, F, E, E, E, F]), ([T, E, E, E, T, F, E, T, E, F, E, E, F], [T, E, E, E, T, F, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_787 (And.intro z_805 trivial))

theorem z_807 : le (tf [E, F, E, T, E, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, E, F, E, T, F] [([E, F, E, E, T, T, E, E, E, F, E, T, F], [F, E, E, E, T, T, E, E, E, F, E, T, F]), ([E, F, E, T, E, E, T, E, E, F, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_316 (And.intro z_566 trivial))

theorem z_808 : le (tf [E, T, F, E, E, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, E, F, E, T, F] [([E, E, F, T, E, T, E, E, E, F, E, T, F], [E, F, E, T, E, T, E, E, E, F, E, T, F]), ([E, T, F, E, E, E, T, E, E, F, E, T, F], [F, T, E, E, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_807 (And.intro z_570 trivial))

theorem z_809 : le (tf [E, T, E, F, E, T, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, E, F, T, E, F] [([E, E, T, F, E, T, E, E, E, F, T, E, F], [E, F, T, E, E, T, E, E, E, F, T, E, F]), ([E, T, E, F, E, E, T, E, E, F, T, E, F], [E, T, F, E, E, E, T, E, E, F, T, E, F]), ([E, T, E, F, E, T, E, E, E, F, E, T, F], [E, T, F, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 (And.intro z_621 (And.intro z_808 trivial)))

theorem z_810 : le (tf [E, T, E, T, F, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, E, F, T, E, F] [([E, E, T, T, F, E, E, E, E, F, T, E, F], [E, E, T, T, F, E, E, E, F, E, T, E, F]), ([E, T, E, E, F, T, E, E, E, F, T, E, F], [E, T, E, F, E, T, E, E, E, F, T, E, F]), ([E, T, E, T, F, E, E, E, E, F, E, T, F], [E, T, F, T, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_366 (And.intro z_809 (And.intro z_681 trivial)))

theorem z_811 : le (tf [E, T, E, T, E, F, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, E, E, T, F, E, E, F] [([E, E, T, T, E, F, E, E, T, F, E, E, F], [E, E, T, T, F, E, E, E, T, F, E, E, F]), ([E, T, E, E, T, F, E, E, T, F, E, E, F], [E, T, E, E, T, F, E, F, T, E, E, E, F]), ([E, T, E, T, E, F, E, E, E, F, T, E, F], [E, T, E, T, F, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_367 (And.intro z_636 (And.intro z_810 trivial)))

theorem z_812 : le (tf [T, E, E, F, E, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, E, E, E, F, E, T, F] [([E, T, E, F, E, T, E, E, E, F, E, T, F], [E, T, F, E, E, T, E, E, E, F, E, T, F]), ([T, E, E, F, E, E, T, E, E, F, E, T, F], [T, E, F, E, E, E, T, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_808 (And.intro z_665 trivial))

theorem z_813 : le (tf [T, E, E, T, F, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, E, E, E, F, E, T, F] [([E, T, E, T, F, E, E, E, E, F, E, T, F], [E, T, F, T, E, E, E, E, E, F, E, T, F]), ([T, E, E, E, F, T, E, E, E, F, E, T, F], [T, E, E, F, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_681 (And.intro z_812 trivial))

theorem z_814 : le (tf [T, E, E, T, E, F, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, F, E, E, E, F, T, E, F] [([E, T, E, T, E, F, E, E, E, F, T, E, F], [E, T, E, T, F, E, E, E, E, F, T, E, F]), ([T, E, E, E, T, F, E, E, E, F, T, E, F], [T, E, E, F, T, E, E, E, E, F, T, E, F]), ([T, E, E, T, E, F, E, E, E, F, E, T, F], [T, E, E, T, F, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_810 (And.intro z_673 (And.intro z_813 trivial)))

theorem z_815 : le (tf [T, E, E, T, E, E, F, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, F, E, T, F, E, E, F] [([E, T, E, T, E, E, F, E, T, F, E, E, F], [E, T, E, T, E, F, E, E, T, F, E, E, F]), ([T, E, E, E, T, E, F, E, T, F, E, E, F], [T, E, E, E, T, F, E, E, T, F, E, E, F]), ([T, E, E, T, E, E, F, E, E, F, T, E, F], [T, E, E, T, E, F, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_811 (And.intro z_674 (And.intro z_814 trivial)))

theorem z_816 : le (tf [T, E, E, T, E, E, T, F, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, T, F, E, F, E, E, F] [([E, T, E, T, E, E, T, F, E, F, E, E, F], [E, T, E, T, E, F, T, E, E, F, E, E, F]), ([T, E, E, E, T, E, T, F, E, F, E, E, F], [T, E, E, E, T, F, T, E, E, F, E, E, F]), ([T, E, E, T, E, E, E, F, T, F, E, E, F], [T, E, E, T, E, E, F, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_788 (And.intro z_806 (And.intro z_815 trivial)))

theorem z_817 : le (tf [E, F, E, T, T, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, E, F, T, F] [([E, F, E, T, E, T, E, E, E, E, F, T, F], [F, E, E, T, E, T, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_567 trivial)

theorem z_818 : le (tf [E, T, F, E, T, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, E, F, T, F] [([E, E, F, T, T, E, E, E, E, E, F, T, F], [E, F, E, T, T, E, E, E, E, E, F, T, F]), ([E, T, F, E, E, T, E, E, E, E, F, T, F], [F, T, E, E, E, T, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_817 (And.intro z_571 trivial))

theorem z_819 : le (tf [E, T, T, F, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, E, E, F, T, F] [([E, T, E, F, T, E, E, E, E, E, F, T, F], [E, T, F, E, T, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_818 trivial)

theorem z_820 : le (tf [E, T, T, E, F, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, F, E, E, E, E, T, F, E, F] [([E, T, E, T, F, E, E, E, E, T, F, E, F], [E, T, E, T, F, E, E, E, F, T, E, E, F]), ([E, T, T, E, F, E, E, E, E, E, F, T, F], [E, T, T, F, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_583 (And.intro z_819 trivial))

theorem z_821 : le (tf [E, T, T, E, E, F, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, F, E, E, T, E, F, E, F] [([E, T, E, T, E, F, E, E, T, E, F, E, F], [E, T, E, T, F, E, E, E, T, E, F, E, F]), ([E, T, T, E, E, F, E, E, E, T, F, E, F], [E, T, T, E, F, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_584 (And.intro z_820 trivial))

theorem z_822 : le (tf [T, E, T, E, F, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, T, E, F, E, E, E, E, E, F, T, F] [([E, T, T, E, F, E, E, E, E, E, F, T, F], [E, T, T, F, E, E, E, E, E, E, F, T, F]), ([T, E, E, T, F, E, E, E, E, E, F, T, F], [T, E, F, T, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_819 (And.intro z_682 trivial))

theorem z_823 : le (tf [T, E, T, E, E, F, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, F, E, E, E, T, F, E, F] [([E, T, T, E, E, F, E, E, E, T, F, E, F], [E, T, T, E, F, E, E, E, E, T, F, E, F]), ([T, E, E, T, E, F, E, E, E, T, F, E, F], [T, E, E, T, F, E, E, E, E, T, F, E, F]), ([T, E, T, E, E, F, E, E, E, E, F, T, F], [T, E, T, E, F, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_820 (And.intro z_683 (And.intro z_822 trivial)))

theorem z_824 : le (tf [T, E, T, E, E, E, F, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, E, F, E, T, E, F, E, F] [([E, T, T, E, E, E, F, E, T, E, F, E, F], [E, T, T, E, E, F, E, E, T, E, F, E, F]), ([T, E, E, T, E, E, F, E, T, E, F, E, F], [T, E, E, T, E, E, F, E, T, F, E, E, F]), ([T, E, T, E, E, E, F, E, E, T, F, E, F], [T, E, T, E, E, F, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_821 (And.intro z_815 (And.intro z_823 trivial)))

theorem z_825 : le (tf [T, E, T, E, E, E, T, F, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, E, T, F, E, E, F, E, F] [([E, T, T, E, E, E, T, F, E, E, F, E, F], [E, T, T, E, E, F, T, E, E, E, F, E, F]), ([T, E, E, T, E, E, T, F, E, E, F, E, F], [T, E, E, T, E, E, T, F, E, F, E, E, F]), ([T, E, T, E, E, E, E, F, T, E, F, E, F], [T, E, T, E, E, E, F, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_690 (And.intro z_816 (And.intro z_824 trivial)))

theorem z_826 : le (tf [T, E, T, E, E, T, E, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, T, E, F, E, E, E, F, F] [([E, T, T, E, E, T, E, F, E, E, E, F, F], [E, T, T, E, E, T, F, E, E, E, E, F, F]), ([T, E, E, T, E, T, E, F, E, E, E, F, F], [T, E, E, T, E, T, F, E, E, E, E, F, F]), ([T, E, T, E, E, E, T, F, E, E, E, F, F], [T, E, T, E, E, E, T, F, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_598 (And.intro z_686 (And.intro z_825 trivial)))

theorem z_827 : le (tf [T, E, T, E, T, E, E, E, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, T, E, E, E, F, E, E, F, F] [([E, T, T, E, T, E, E, E, F, E, E, F, F], [E, T, T, E, T, E, E, F, E, E, E, F, F]), ([T, E, E, T, T, E, E, E, F, E, E, F, F], [T, E, E, T, T, E, E, F, E, E, E, F, F]), ([T, E, T, E, E, T, E, E, F, E, E, F, F], [T, E, T, E, E, T, E, F, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_599 (And.intro z_687 (And.intro z_826 trivial)))

theorem z_828 : le (tf [T, E, T, T, E, E, E, E, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, E, E, E, E, E, F, E, F, F] [([E, T, T, T, E, E, E, E, E, F, E, F, F], [E, T, T, T, E, E, E, E, F, E, E, F, F]), ([T, E, T, E, T, E, E, E, E, F, E, F, F], [T, E, T, E, T, E, E, E, F, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_600 (And.intro z_827 trivial))

theorem z_829 : le (tf [T, E, T, F, E, E, E, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, E, E, E, E, E, T, F, F] [([E, T, T, F, E, E, E, E, E, E, T, F, F], [E, T, T, F, E, E, E, E, E, F, T, E, F]), ([T, E, E, F, T, E, E, E, E, E, T, F, F], [T, E, E, F, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_594 (And.intro z_673 trivial))

theorem z_830 : le (tf [T, T, E, E, F, E, E, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, F, E, E, E, E, E, T, F, F] [([T, E, T, E, F, E, E, E, E, E, T, F, F], [T, E, T, F, E, E, E, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_829 trivial)

theorem z_831 : le (tf [T, T, E, E, E, F, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, F, E, E, E, T, E, F, F] [([T, E, T, E, E, F, E, E, E, T, E, F, F], [T, E, T, E, E, F, E, E, E, T, F, E, F]), ([T, T, E, E, E, F, E, E, E, E, T, F, F], [T, T, E, E, F, E, E, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_823 (And.intro z_830 trivial))

theorem z_832 : le (tf [T, T, E, E, E, E, F, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, E, F, E, T, E, E, F, F] [([T, E, T, E, E, E, F, E, T, E, E, F, F], [T, E, T, E, E, E, F, E, T, E, F, E, F]), ([T, T, E, E, E, E, F, E, E, T, E, F, F], [T, T, E, E, E, F, E, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_824 (And.intro z_831 trivial))

theorem z_833 : le (tf [T, T, E, E, E, E, T, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, E, T, F, E, E, E, F, F] [([T, E, T, E, E, E, T, F, E, E, E, F, F], [T, E, T, E, E, E, T, F, E, E, F, E, F]), ([T, T, E, E, E, E, E, F, T, E, E, F, F], [T, T, E, E, E, E, F, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_825 (And.intro z_832 trivial))

theorem z_834 : le (tf [T, T, E, E, E, T, E, E, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, T, E, E, F, E, E, F, F] [([T, E, T, E, E, T, E, E, F, E, E, F, F], [T, E, T, E, E, T, E, F, E, E, E, F, F]), ([T, T, E, E, E, E, T, E, F, E, E, F, F], [T, T, E, E, E, E, T, F, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_826 (And.intro z_833 trivial))

theorem z_835 : le (tf [T, T, E, E, T, E, E, E, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, T, E, E, E, E, F, E, F, F] [([T, E, T, E, T, E, E, E, E, F, E, F, F], [T, E, T, E, T, E, E, E, F, E, E, F, F]), ([T, T, E, E, E, T, E, E, E, F, E, F, F], [T, T, E, E, E, T, E, E, F, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_827 (And.intro z_834 trivial))

theorem z_836 : le (tf [T, T, E, T, E, E, E, E, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, E, E, E, E, E, E, F, F, F] [([T, E, T, T, E, E, E, E, E, E, F, F, F], [T, E, T, T, E, E, E, E, E, F, E, F, F]), ([T, T, E, E, T, E, E, E, E, E, F, F, F], [T, T, E, E, T, E, E, E, E, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_828 (And.intro z_835 trivial))

theorem n_0 : UpperZero (tf [T, T, T, E, E, E, E, E, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, E, E, E, E, E, E, F, F, F] (lfZero_of_mirror_dec [T, T, T, E, E, E, E, E, E, E, F, F, F] (by decide +kernel)) [[T, T, E, T, E, E, E, E, E, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_836 trivial)
    trivial

theorem infinitesimal : Infinitesimal (tf (start 3 7)) := by
  rw [infinitesimal_start_iff, show start 3 7 = [T, T, T, E, E, E, E, E, E, E, F, F, F] from by decide]
  exact n_0

end Cgt.Cert_3_7
